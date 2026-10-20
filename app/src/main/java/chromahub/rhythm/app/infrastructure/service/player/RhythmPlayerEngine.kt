/*
 * SPDX-FileCopyrightText: 2024-2026 Anjishnu Nandi <https://github.com/cromaguy>
 * SPDX-License-Identifier: GPL-3.0-or-later
 */

package chromahub.rhythm.app.infrastructure.service.player

import android.content.Context
import android.media.AudioDeviceInfo
import android.media.AudioFocusRequest
import android.media.AudioManager
import android.media.MediaFormat
import android.net.Uri
import android.os.Build
import android.os.Handler
import android.util.Log
import androidx.annotation.OptIn
import androidx.core.net.toUri
import androidx.media3.common.AudioAttributes
import androidx.media3.common.C
import androidx.media3.common.MediaItem
import androidx.media3.common.MimeTypes
import androidx.media3.common.PlaybackParameters
import androidx.media3.common.Player
import androidx.media3.common.TrackSelectionParameters
import androidx.media3.common.audio.AudioProcessor
import androidx.media3.common.audio.BaseAudioProcessor
import androidx.media3.common.audio.SonicAudioProcessor
import androidx.media3.common.util.UnstableApi
import androidx.media3.datasource.DataSpec
import androidx.media3.datasource.DefaultDataSource
import androidx.media3.datasource.DefaultHttpDataSource
import androidx.media3.datasource.ResolvingDataSource
import androidx.media3.datasource.cache.CacheDataSource
import androidx.media3.datasource.okhttp.OkHttpDataSource
import androidx.media3.exoplayer.DecoderReuseEvaluation
import androidx.media3.exoplayer.DefaultLoadControl
import androidx.media3.exoplayer.DefaultRenderersFactory
import androidx.media3.exoplayer.ExoPlayer
import androidx.media3.exoplayer.Renderer
import androidx.media3.exoplayer.RendererCapabilities
import androidx.media3.exoplayer.SeekParameters
import androidx.media3.exoplayer.analytics.AnalyticsListener
import androidx.media3.exoplayer.audio.AudioRendererEventListener
import androidx.media3.exoplayer.audio.AudioSink
import androidx.media3.exoplayer.audio.DefaultAudioSink
import androidx.media3.exoplayer.audio.MediaCodecAudioRenderer
import androidx.media3.exoplayer.audio.SilenceSkippingAudioProcessor
import androidx.media3.exoplayer.mediacodec.MediaCodecAdapter
import androidx.media3.exoplayer.mediacodec.MediaCodecSelector
import androidx.media3.exoplayer.mediacodec.MediaCodecUtil
import androidx.media3.exoplayer.source.DefaultMediaSourceFactory
import androidx.media3.extractor.DefaultExtractorsFactory
import androidx.media3.extractor.flac.FlacExtractor
import androidx.media3.extractor.mp3.Mp3Extractor
import androidx.media3.extractor.ts.AdtsExtractor
import chromahub.rhythm.app.core.device.DeviceCapabilitiesProvider
import chromahub.rhythm.app.core.device.HiFiCapabilityChecker
import chromahub.rhythm.app.features.streaming.data.provider.UserTrustManager
import chromahub.rhythm.app.features.streaming.di.StreamingMusicModule
import chromahub.rhythm.app.infrastructure.audio.RhythmBassBoostProcessor
import chromahub.rhythm.app.infrastructure.audio.RhythmMonoAudioProcessor
import chromahub.rhythm.app.infrastructure.audio.RhythmSpatializationProcessor
import chromahub.rhythm.app.infrastructure.service.player.replaygain.ReplayGainAudioProcessor
import chromahub.rhythm.app.infrastructure.service.player.replaygain.ReplayGainCache
import chromahub.rhythm.app.infrastructure.service.player.replaygain.ReplayGainUtil
import chromahub.rhythm.app.shared.data.model.AppSettings
import chromahub.rhythm.app.shared.data.model.TransitionSettings
import chromahub.rhythm.app.util.calculateVolumeIn
import chromahub.rhythm.app.util.calculateVolumeOut
import chromahub.rhythm.app.util.envelope
import java.nio.ByteBuffer
import java.util.concurrent.TimeUnit
import kotlin.math.roundToInt
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.cancel
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking

// Parâmetros proprietários da Dolby no Android C2
// 2 = Auscultadores (Headphones); 1 = DAX State ativo para renderização binaural
private const val DOLBY_ACTIVE_DEVICE = 2
private const val DOLBY_DAX_STATE = 1
private const val DOLBY_TAG = "RhythmDolby"

// Ganho de -4 dB (10^(-4/20) ≈ 0.631f) aplicado em PCM para neutralizar os -14 dB forçados pela Samsung
private const val DOLBY_HEADROOM_GAIN = 0.631f

@OptIn(UnstableApi::class)
class RhythmPlayerEngine(
    private val context: Context,
    private val bassBoostProcessor: RhythmBassBoostProcessor? = null,
    private val spatializationProcessor: RhythmSpatializationProcessor? = null,
    private val monoProcessor: RhythmMonoAudioProcessor? = null
) {
    companion object {
        private const val TAG = "RhythmPlayerEngine"
    }

    private var scope = CoroutineScope(Dispatchers.Main + SupervisorJob())
    private var transitionJob: Job? = null
    @Volatile
    private var transitionRunning = false

    private lateinit var playerA: ExoPlayer
    private lateinit var playerB: ExoPlayer

    private var playerABassBoost: RhythmBassBoostProcessor? = null
    private var playerBBassBoost: RhythmBassBoostProcessor? = null
    private var playerASpatialization: RhythmSpatializationProcessor? = null
    private var playerBSpatialization: RhythmSpatializationProcessor? = null
    private var playerAMono: RhythmMonoAudioProcessor? = null
    private var playerBMono: RhythmMonoAudioProcessor? = null
    private lateinit var playerAReplayGain: ReplayGainAudioProcessor
    private lateinit var playerBReplayGain: ReplayGainAudioProcessor
    private lateinit var playerADolbyGain: DolbyGainAudioProcessor
    private lateinit var playerBDolbyGain: DolbyGainAudioProcessor
    private var activeReplayGainProcessor: ReplayGainAudioProcessor? = null
    private var activeDolbyGainProcessor: DolbyGainAudioProcessor? = null
    private var userVolume: Float = 1.0f
    @Volatile
    var isInternalVolumeAdjustment: Boolean = false

    private val onPlayerSwappedListeners = mutableListOf<(Player) -> Unit>()

    private val _activeAudioSessionId = MutableStateFlow(0)
    val activeAudioSessionId: StateFlow<Int> = _activeAudioSessionId.asStateFlow()

    private val _currentEngineFormat = MutableStateFlow<EngineAudioFormat?>(null)
    val currentEngineFormat: StateFlow<EngineAudioFormat?> = _currentEngineFormat.asStateFlow()

    private var playerADecoderName: String = ""
    private var playerBDecoderName: String = ""

    private val analyticsListenerA = object : AnalyticsListener {
        override fun onAudioDecoderInitialized(
            eventTime: AnalyticsListener.EventTime,
            decoderName: String,
            initializedTimestampMs: Long,
            initializationDurationMs: Long
        ) {
            playerADecoderName = decoderName
            val format = (playerA as? ExoPlayer)?.audioFormat ?: playerA.currentTracks.getFirstSelectedTrackFormatByType(C.TRACK_TYPE_AUDIO)
            if (format != null && masterPlayer === playerA) {
                _currentEngineFormat.value = EngineAudioFormat(format, decoderName)
            }
        }

        override fun onAudioInputFormatChanged(
            eventTime: AnalyticsListener.EventTime,
            format: androidx.media3.common.Format,
            decoderReuseEvaluation: DecoderReuseEvaluation?
        ) {
            if (masterPlayer === playerA) {
                _currentEngineFormat.value = EngineAudioFormat(format, playerADecoderName)
            }
        }
    }

    private val analyticsListenerB = object : AnalyticsListener {
        override fun onAudioDecoderInitialized(
            eventTime: AnalyticsListener.EventTime,
            decoderName: String,
            initializedTimestampMs: Long,
            initializationDurationMs: Long
        ) {
            playerBDecoderName = decoderName
            val format = (playerB as? ExoPlayer)?.audioFormat ?: playerB.currentTracks.getFirstSelectedTrackFormatByType(C.TRACK_TYPE_AUDIO)
            if (format != null && masterPlayer === playerB) {
                _currentEngineFormat.value = EngineAudioFormat(format, decoderName)
            }
        }

        override fun onAudioInputFormatChanged(
            eventTime: AnalyticsListener.EventTime,
            format: androidx.media3.common.Format,
            decoderReuseEvaluation: DecoderReuseEvaluation?
        ) {
            if (masterPlayer === playerB) {
                _currentEngineFormat.value = EngineAudioFormat(format, playerBDecoderName)
            }
        }
    }

    private val audioManager = context.getSystemService(Context.AUDIO_SERVICE) as AudioManager
    private var audioFocusRequest: AudioFocusRequest? = null
    private var isFocusLossPause = false

    private val focusChangeListener = AudioManager.OnAudioFocusChangeListener { focusChange ->
        when (focusChange) {
            AudioManager.AUDIOFOCUS_LOSS -> {
                Log.d(TAG, "AudioFocus LOSS. Pausing both players.")
                isFocusLossPause = false
                playerA.playWhenReady = false
                playerB.playWhenReady = false
                abandonAudioFocus()
            }
            AudioManager.AUDIOFOCUS_LOSS_TRANSIENT -> {
                Log.d(TAG, "AudioFocus LOSS_TRANSIENT. Pausing.")
                isFocusLossPause = true
                playerA.playWhenReady = false
                playerB.playWhenReady = false
            }
            AudioManager.AUDIOFOCUS_GAIN -> {
                Log.d(TAG, "AudioFocus GAIN. Resuming if paused by loss.")
                if (isFocusLossPause) {
                    isFocusLossPause = false
                    playerA.playWhenReady = true
                    if (transitionRunning) playerB.playWhenReady = true
                }
            }
        }
    }

    private val masterPlayerListener = object : Player.Listener {
        override fun onPlayWhenReadyChanged(playWhenReady: Boolean, reason: Int) {
            if (playWhenReady) {
                requestAudioFocus()
                if (transitionRunning && ::playerB.isInitialized && playerB.playbackState != Player.STATE_ENDED) {
                    playerB.playWhenReady = true
                }
            } else {
                if (transitionRunning && ::playerB.isInitialized) {
                    playerB.playWhenReady = false
                }
                // Libera a fila e buffers do Player B imediatamente ao pausar para poupar RAM
                if (::playerB.isInitialized && !transitionRunning) {
                    playerB.stop()
                    playerB.clearMediaItems()
                }
                if (!isFocusLossPause) {
                    abandonAudioFocus()
                }
            }
        }

        override fun onAudioSessionIdChanged(audioSessionId: Int) {
            _activeAudioSessionId.value = audioSessionId
            Log.d(TAG, "Audio session ID changed: $audioSessionId")
        }

        override fun onTracksChanged(tracks: androidx.media3.common.Tracks) {
            Log.d(TAG, "Tracks changed")
            val format = tracks.getFirstSelectedTrackFormatByType(C.TRACK_TYPE_AUDIO) ?: (masterPlayer as? ExoPlayer)?.audioFormat
            if (format != null) {
                val mime = format.sampleMimeType.orEmpty()
                val isDolby = mime.contains("eac3") || mime.contains("ac4")
                
                // Ativa a atenuação de -4 dB apenas para faixas Dolby Atmos
                activeDolbyGainProcessor?.isDolbyAtmos = isDolby

                if (isDolby) {
                    // Ignora ReplayGain em faixas Atmos para preservar a decodificação de objetos
                    activeReplayGainProcessor?.setMode(ReplayGainUtil.Mode.None, false)
                } else {
                    val info = ReplayGainUtil.parse(format)
                    masterPlayer.currentMediaItem?.mediaId?.let { id ->
                        ReplayGainCache.put(id, info)
                    }
                    val appSettings = AppSettings.getInstance(context)
                    activeReplayGainProcessor?.let { proc ->
                        applyReplayGainSettingsOnProcessor(proc, appSettings.replayGain.value)
                    }
                    activeReplayGainProcessor?.setRootFormat(format)
                }
                val currentDec = if (masterPlayer === playerA) playerADecoderName else playerBDecoderName
                _currentEngineFormat.value = EngineAudioFormat(format, currentDec)
            }
        }

        override fun onVolumeChanged(volume: Float) {
            if (!transitionRunning && !isInternalVolumeAdjustment) {
                userVolume = volume
                Log.d(TAG, "User volume updated: $userVolume")
            }
        }
    }

    fun setUserVolume(volume: Float) {
        userVolume = volume.coerceIn(0f, 1f)
        if (::playerA.isInitialized) {
            playerA.volume = userVolume
        }
    }

    fun getUserVolume(): Float = userVolume

    fun addPlayerSwapListener(listener: (Player) -> Unit) {
        onPlayerSwappedListeners.add(listener)
    }

    fun removePlayerSwapListener(listener: (Player) -> Unit) {
        onPlayerSwappedListeners.remove(listener)
    }

    val masterPlayer: Player
        get() = playerA

    fun isTransitionRunning(): Boolean = transitionRunning || transitionJob?.isActive == true

    fun getAudioSessionId(): Int = if (::playerA.isInitialized) playerA.audioSessionId else 0

    @Volatile
    private var preferredAudioDevice: AudioDeviceInfo? = null

    fun setPreferredAudioDevice(device: AudioDeviceInfo?) {
        preferredAudioDevice = device
        if (::playerA.isInitialized) {
            try { playerA.setPreferredAudioDevice(device) } catch (e: Exception) { Log.w(TAG, "Failed to set preferred device on playerA", e) }
        }
        if (::playerB.isInitialized) {
            try { playerB.setPreferredAudioDevice(device) } catch (e: Exception) { Log.w(TAG, "Failed to set preferred device on playerB", e) }
        }
    }

    private var isReleased = false

    fun initialize() {
        if (!isReleased && ::playerA.isInitialized && playerA.applicationLooper.thread.isAlive) return

        if (!scope.isActive) {
            scope = CoroutineScope(Dispatchers.Main + SupervisorJob())
        }

        if (::playerA.isInitialized) {
            try { playerA.release() } catch (_: Exception) {}
        }
        if (::playerB.isInitialized) {
            try { playerB.release() } catch (_: Exception) {}
        }

        val aBass = bassBoostProcessor?.let { RhythmBassBoostProcessor().apply { setParent(it) } }
        val aSpatial = spatializationProcessor?.let { RhythmSpatializationProcessor().apply { setParent(it) } }
        val aMono = monoProcessor?.let { RhythmMonoAudioProcessor().apply { setParent(it) } }
        val aReplayGain = ReplayGainAudioProcessor()
        val aDolbyGain = DolbyGainAudioProcessor()
        playerABassBoost = aBass
        playerASpatialization = aSpatial
        playerAMono = aMono
        playerAReplayGain = aReplayGain
        playerADolbyGain = aDolbyGain

        val bBass = bassBoostProcessor?.let { RhythmBassBoostProcessor().apply { setParent(it) } }
        val bSpatial = spatializationProcessor?.let { RhythmSpatializationProcessor().apply { setParent(it) } }
        val bMono = monoProcessor?.let { RhythmMonoAudioProcessor().apply { setParent(it) } }
        val bReplayGain = ReplayGainAudioProcessor()
        val bDolbyGain = DolbyGainAudioProcessor()
        playerBBassBoost = bBass
        playerBSpatialization = bSpatial
        playerBMono = bMono
        playerBReplayGain = bReplayGain
        playerBDolbyGain = bDolbyGain

        val appSettings = AppSettings.getInstance(context)
        applyReplayGainSettingsOnProcessor(aReplayGain, appSettings.replayGain.value)
        applyReplayGainSettingsOnProcessor(bReplayGain, appSettings.replayGain.value)

        playerA = buildPlayer(
            handleAudioFocus = false,
            bassProcessor = aBass,
            spatialProcessor = aSpatial,
            monoProcessor = aMono,
            replayGainProcessor = aReplayGain,
            dolbyGainProcessor = aDolbyGain
        )
        playerB = buildPlayer(
            handleAudioFocus = false,
            bassProcessor = bBass,
            spatialProcessor = bSpatial,
            monoProcessor = bMono,
            replayGainProcessor = bReplayGain,
            dolbyGainProcessor = bDolbyGain
        )

        val initVolume = if (appSettings.useSystemVolume.value) 1.0f else appSettings.appVolume.value
        userVolume = initVolume
        playerA.volume = initVolume

        val initSpeed = appSettings.playbackSpeed.value.coerceIn(0.25f, 3.0f)
        val initPitch = appSettings.playbackPitch.value.coerceIn(0.5f, 2.0f)
        val initParams = PlaybackParameters(initSpeed, initPitch)
        playerA.playbackParameters = initParams
        playerB.playbackParameters = initParams

        playerA.addListener(masterPlayerListener)
        playerA.addAnalyticsListener(analyticsListenerA)
        playerB.addAnalyticsListener(analyticsListenerB)
        activeReplayGainProcessor = aReplayGain
        activeDolbyGainProcessor = aDolbyGain

        _activeAudioSessionId.value = playerA.audioSessionId

        isReleased = false
        Log.d(TAG, "RhythmPlayerEngine initialized. SessionA=${playerA.audioSessionId}, initialVolume=$initVolume, speed=$initSpeed, pitch=$initPitch")

        scope.launch {
            launch { appSettings.crossfade.collect { updateTrackSelectionParameters() } }
            launch { appSettings.equalizerEnabled.collect { updateTrackSelectionParameters() } }
            launch { appSettings.replayGain.collect { updateTrackSelectionParameters() } }
            launch { appSettings.bassBoostEnabled.collect { updateTrackSelectionParameters() } }
            launch { appSettings.virtualizerEnabled.collect { updateTrackSelectionParameters() } }
            launch { appSettings.monoAudioEnabled.collect { updateTrackSelectionParameters() } }
            launch { appSettings.isAudioOffloadActive.collect { updateTrackSelectionParameters() } }
            launch {
                appSettings.playbackSpeed.collect {
                    updatePlaybackParameters()
                    updateTrackSelectionParameters()
                }
            }
            launch {
                appSettings.playbackPitch.collect {
                    updatePlaybackParameters()
                    updateTrackSelectionParameters()
                }
            }
            launch { appSettings.gaplessPlayback.collect { updateTrackSelectionParameters() } }
            launch { appSettings.skipSilenceEnabled.collect { updateTrackSelectionParameters() } }
        }
    }

    private fun requestAudioFocus() {
        if (audioFocusRequest != null) return

        val attributes = android.media.AudioAttributes.Builder()
            .setUsage(android.media.AudioAttributes.USAGE_MEDIA)
            .setContentType(android.media.AudioAttributes.CONTENT_TYPE_MUSIC)
            .build()

        val request = AudioFocusRequest.Builder(AudioManager.AUDIOFOCUS_GAIN)
            .setAudioAttributes(attributes)
            .setOnAudioFocusChangeListener(focusChangeListener)
            .build()

        val result = audioManager.requestAudioFocus(request)
        if (result == AudioManager.AUDIOFOCUS_REQUEST_GRANTED) {
            audioFocusRequest = request
        } else {
            Log.w(TAG, "AudioFocus Request Failed: $result")
            playerA.playWhenReady = false
        }
    }

    private fun abandonAudioFocus() {
        audioFocusRequest?.let {
            audioManager.abandonAudioFocusRequest(it)
            audioFocusRequest = null
        }
    }

    private fun buildPlayer(
        handleAudioFocus: Boolean,
        bassProcessor: RhythmBassBoostProcessor? = null,
        spatialProcessor: RhythmSpatializationProcessor? = null,
        monoProcessor: RhythmMonoAudioProcessor? = null,
        replayGainProcessor: ReplayGainAudioProcessor? = null,
        dolbyGainProcessor: DolbyGainAudioProcessor? = null
    ): ExoPlayer {
        // Otimização extrema de memória: buffers compactos para evitar retenção desnecessária na RAM do A05s
        val loadControl = DefaultLoadControl.Builder()
            .setBufferDurationsMs(
                /* minBufferMs = */ 10_000,
                /* maxBufferMs = */ 20_000,
                /* bufferForPlaybackMs = */ 500,
                /* bufferForPlaybackAfterRebufferMs = */ 1_000
            )
            .setBackBuffer(0, false)
            .setPrioritizeTimeOverSizeThresholds(true)
            .build()

        val appSettings = AppSettings.getInstance(context)
        val isPlaybackRateModified =
            kotlin.math.abs(appSettings.playbackSpeed.value - 1f) > 0.001f ||
            kotlin.math.abs(appSettings.playbackPitch.value - 1f) > 0.001f
        val hasActiveProcessors =
            appSettings.bassBoostEnabled.value ||
            appSettings.virtualizerEnabled.value ||
            appSettings.monoAudioEnabled.value ||
            appSettings.skipSilenceEnabled.value ||
            isPlaybackRateModified

        val floatOutputPref = appSettings.audioEngineFloatOutput.value &&
            HiFiCapabilityChecker.isSupported() &&
            !hasActiveProcessors

        val mediaCodecSelector = MediaCodecSelector { mimeType, requiresSecureDecoder, requiresTunnelingDecoder ->
            if (mimeType == MimeTypes.AUDIO_AC3) {
                return@MediaCodecSelector emptyList()
            }

            if (mimeType == MimeTypes.AUDIO_E_AC3 || mimeType == MimeTypes.AUDIO_E_AC3_JOC || mimeType == MimeTypes.AUDIO_AC4) {
                val candidates = MediaCodecUtil.getDecoderInfos(
                    mimeType,
                    requiresSecureDecoder,
                    requiresTunnelingDecoder
                )
                val sorted = candidates.sortedByDescending { info ->
                    val name = info.name.lowercase()
                    when {
                        name.contains("c2.dolby") -> 3
                        name.contains("dolby") -> 2
                        else -> 0
                    }
                }
                if (sorted.isNotEmpty()) {
                    return@MediaCodecSelector sorted
                }
            }

            val defaultDecoders = MediaCodecSelector.DEFAULT.getDecoderInfos(
                mimeType,
                requiresSecureDecoder,
                requiresTunnelingDecoder
            )
            val disabled = appSettings.audioEngineDisabledDecoders.value
            val preferHw = appSettings.audioEnginePreferHardware.value

            val filtered = if (disabled.isEmpty()) defaultDecoders else defaultDecoders.filter { it.name !in disabled }
            if (preferHw) {
                filtered.sortedByDescending { if (DeviceCapabilitiesProvider.isLikelyHardwareDecoder(it.name)) 1 else 0 }
            } else {
                filtered
            }
        }

        val renderersFactory = object : DefaultRenderersFactory(context) {
            override fun buildAudioRenderers(
                context: Context,
                extensionRendererMode: Int,
                mediaCodecSelector: MediaCodecSelector,
                enableDecoderFallback: Boolean,
                audioSink: AudioSink,
                eventHandler: Handler,
                eventListener: AudioRendererEventListener,
                out: ArrayList<Renderer>
            ) {
                super.buildAudioRenderers(
                    context,
                    extensionRendererMode,
                    mediaCodecSelector,
                    enableDecoderFallback,
                    audioSink,
                    eventHandler,
                    eventListener,
                    out
                )

                val mcIndex = out.indexOfFirst { it is MediaCodecAudioRenderer }
                if (mcIndex >= 0) {
                    out[mcIndex] = DolbyMediaCodecAudioRenderer(
                        context,
                        MediaCodecAdapter.Factory.getDefault(context),
                        mediaCodecSelector,
                        enableDecoderFallback,
                        eventHandler,
                        eventListener,
                        audioSink,
                        dolbyGainProcessor
                    )
                }

                for (i in out.indices) {
                    val renderer = out[i]
                    if (renderer.javaClass.simpleName.contains("Ffmpeg", ignoreCase = true)) {
                        out[i] = NoDolbyRenderer(renderer)
                    }
                }
            }

            override fun buildAudioSink(
                context: Context,
                enableFloatOutput: Boolean,
                enableAudioTrackPlaybackParams: Boolean
            ): AudioSink? {
                val processors = mutableListOf<AudioProcessor>()

                if (dolbyGainProcessor != null) {
                    processors.add(dolbyGainProcessor)
                }
                if (bassProcessor != null) {
                    processors.add(bassProcessor)
                }
                if (spatialProcessor != null) {
                    processors.add(spatialProcessor)
                }
                if (monoProcessor != null) {
                    processors.add(monoProcessor)
                }
                if (replayGainProcessor != null) {
                    processors.add(replayGainProcessor)
                }

                val silenceSkippingProcessor = SilenceSkippingAudioProcessor(
                    /* minimumSilenceDurationUs = */ 500_000L,
                    /* silenceRetentionRatio = */ 0.2f,
                    /* maxSilenceToKeepDurationUs = */ 1_000_000L,
                    /* minVolumeToKeepPercentageWhenMuting = */ 5,
                    /* silenceThresholdLevel = */ 40.toShort()
                )
                val sonicAudioProcessor = SonicAudioProcessor()
                val allProcessors: Array<AudioProcessor> =
                    (listOf(silenceSkippingProcessor) + processors + sonicAudioProcessor).toTypedArray()
                val processorChain = object : androidx.media3.exoplayer.audio.AudioProcessorChain {
                    override fun getAudioProcessors(): Array<AudioProcessor> = allProcessors

                    override fun applyPlaybackParameters(playbackParameters: PlaybackParameters): PlaybackParameters {
                        sonicAudioProcessor.setSpeed(playbackParameters.speed)
                        sonicAudioProcessor.setPitch(playbackParameters.pitch)
                        return playbackParameters
                    }

                    override fun applySkipSilenceEnabled(skipSilenceEnabled: Boolean): Boolean {
                        silenceSkippingProcessor.setEnabled(skipSilenceEnabled)
                        return skipSilenceEnabled
                    }

                    override fun getMediaDuration(playoutDuration: Long): Long {
                        return if (sonicAudioProcessor.isActive) sonicAudioProcessor.getMediaDuration(playoutDuration) else playoutDuration
                    }

                    override fun getSkippedOutputFrameCount(): Long {
                        return silenceSkippingProcessor.skippedFrames
                    }
                }

                return DefaultAudioSink.Builder(context)
                    .setEnableFloatOutput(floatOutputPref)
                    .setEnableAudioOutputPlaybackParameters(true)
                    .setAudioProcessorChain(processorChain)
                    .build()
            }
        }.apply {
            val extensionMode = if (appSettings.decoderExtensionsEnabled.value) {
                DefaultRenderersFactory.EXTENSION_RENDERER_MODE_ON
            } else {
                DefaultRenderersFactory.EXTENSION_RENDERER_MODE_OFF
            }
            setExtensionRendererMode(extensionMode)
            setMediaCodecSelector(mediaCodecSelector)
        }

        val audioAttributes = AudioAttributes.Builder()
            .setContentType(C.AUDIO_CONTENT_TYPE_MUSIC)
            .setUsage(C.USAGE_MEDIA)
            .setSpatializationBehavior(C.SPATIALIZATION_BEHAVIOR_AUTO)
            .build()

        val okHttpClient = UserTrustManager.buildUserTrustingHttpClientBuilder()
            .connectTimeout(15, TimeUnit.SECONDS)
            .readTimeout(30, TimeUnit.SECONDS)
            .build()
        val httpDataSourceFactory = OkHttpDataSource.Factory(okHttpClient)
            .setUserAgent("Rhythm/${chromahub.rhythm.app.BuildConfig.VERSION_NAME} (Android)")
        val cacheDataSourceFactory = CacheDataSource.Factory()
            .setCache(AudioCacheManager.getCache(context))
            .setUpstreamDataSourceFactory(httpDataSourceFactory)
            .setFlags(CacheDataSource.FLAG_IGNORE_CACHE_ON_ERROR)

        val baseDataSourceFactory = DefaultDataSource.Factory(context, cacheDataSourceFactory)

        val resolvingDataSourceFactory = ResolvingDataSource.Factory(
            baseDataSourceFactory,
            object : ResolvingDataSource.Resolver {
                override fun resolveDataSpec(dataSpec: DataSpec): DataSpec {
                    if (dataSpec.uri.scheme == "streaming") {
                        val trackId = dataSpec.uri.lastPathSegment
                        if (!trackId.isNullOrBlank()) {
                            val repository = StreamingMusicModule.provideStreamingMusicRepository(context)
                            val freshUrl = runBlocking { repository.getStreamingUrl(trackId) }
                            if (!freshUrl.isNullOrBlank()) {
                                return dataSpec.buildUpon()
                                    .setUri((freshUrl).toUri())
                                    .setKey("streaming_$trackId")
                                    .build()
                            }
                        }
                    }
                    return dataSpec
                }
            }
        )

        // Fábrica de extratores com tolerância a falhas e controle de tempo forçado
        val extractorsFactory = DefaultExtractorsFactory()
            .setConstantBitrateSeekingEnabled(true)
            .setConstantBitrateSeekingAlwaysEnabled(true)
            .setMp3ExtractorFlags(Mp3Extractor.FLAG_ENABLE_INDEX_SEEKING)
            .setAdtsExtractorFlags(AdtsExtractor.FLAG_ENABLE_CONSTANT_BITRATE_SEEKING)
            .setFlacExtractorFlags(FlacExtractor.FLAG_DISABLE_ID3_METADATA)

        val mediaSourceFactory = DefaultMediaSourceFactory(context, extractorsFactory)
            .setDataSourceFactory(resolvingDataSourceFactory)

        val defaultParams = TrackSelectionParameters.DEFAULT
        val trackSelectionParameters = buildTrackSelectionParameters(defaultParams, appSettings)

        val player = ExoPlayer.Builder(context, renderersFactory)
            .setLoadControl(loadControl)
            .setMediaSourceFactory(mediaSourceFactory)
            .setSeekBackIncrementMs(10_000L)
            .setSeekForwardIncrementMs(10_000L)
            .build().apply {
                setShuffleOrder(RhythmShuffleOrder(0))
                this.trackSelectionParameters = trackSelectionParameters
                setAudioAttributes(audioAttributes, handleAudioFocus)
                setHandleAudioBecomingNoisy(true)
                setWakeMode(C.WAKE_MODE_LOCAL)
                setSkipSilenceEnabled(appSettings.skipSilenceEnabled.value)
                setSeekParameters(SeekParameters.EXACT)
                playWhenReady = false
                preferredAudioDevice?.let { dev ->
                    try { setPreferredAudioDevice(dev) } catch (e: Exception) { Log.w(TAG, "Failed to apply preferred device", e) }
                }
            }

        return player
    }

    fun setPauseAtEndOfMediaItems(shouldPause: Boolean) {
        playerA.pauseAtEndOfMediaItems = shouldPause
    }

    fun setGaplessPlayback(enabled: Boolean) {
        if (::playerA.isInitialized) {
            playerA.pauseAtEndOfMediaItems = !enabled
        }
        if (::playerB.isInitialized) {
            playerB.pauseAtEndOfMediaItems = !enabled
        }
        Log.d(TAG, "Gapless playback ${if (enabled) "enabled" else "disabled"}")
    }

    fun setSkipSilenceEnabled(enabled: Boolean) {
        if (::playerA.isInitialized) {
            playerA.skipSilenceEnabled = enabled
        }
        if (::playerB.isInitialized) {
            playerB.skipSilenceEnabled = enabled
        }
        Log.d(TAG, "Skip silence ${if (enabled) "enabled" else "disabled"}")
    }

    fun prepareNext(
        mediaItem: MediaItem,
        targetIndex: Int = 0,
        fullQueue: List<MediaItem>? = null,
        shuffleIndices: IntArray? = null,
        startPositionMs: Long = 0L
    ) {
        val currentMime = (playerA as? ExoPlayer)?.audioFormat?.sampleMimeType.orEmpty()
        if (currentMime.contains("eac3") || currentMime.contains("ac4")) {
            Log.d(TAG, "prepareNext ignorado: preservando recursos de hardware e fluidez em Dolby Atmos")
            return
        }

        try {
            Log.d(TAG, "prepareNext called for ${mediaItem.mediaId} (targetIndex=$targetIndex, queueSize=${fullQueue?.size ?: 1})")
            ReplayGainCache.get(mediaItem.mediaId)?.let { cachedInfo ->
                playerBReplayGain.setTags(cachedInfo)
            }
            playerB.stop()
            playerB.clearMediaItems()
            playerB.playWhenReady = false

            if (!fullQueue.isNullOrEmpty() && targetIndex in fullQueue.indices) {
                playerB.setMediaItems(fullQueue, targetIndex, if (startPositionMs > 0) startPositionMs else 0L)
                if (shuffleIndices != null && shuffleIndices.size == fullQueue.size) {
                    playerB.setShuffleOrder(RhythmShuffleOrder(shuffleIndices))
                }
            } else {
                playerB.setMediaItem(mediaItem)
                if (startPositionMs > 0) {
                    playerB.seekTo(startPositionMs)
                } else {
                    playerB.seekTo(0)
                }
            }

            if (::playerA.isInitialized) {
                playerB.playbackParameters = playerA.playbackParameters
            }
            playerB.prepare()
            playerB.volume = 0f
            playerB.pause()
            Log.d(TAG, "Player B prepared, paused, volume=0")
        } catch (e: Exception) {
            Log.e(TAG, "Failed to prepare next player", e)
        }
    }

    fun extractShuffleIndices(player: Player = masterPlayer): IntArray? {
        if (!player.shuffleModeEnabled || player.mediaItemCount <= 0) return null
        val count = player.mediaItemCount
        val shuffledIndices = IntArray(count)
        val timeline = player.currentTimeline
        var idx = 0
        var windowIndex = timeline.getFirstWindowIndex(true)
        val visited = BooleanArray(count)
        while (windowIndex != C.INDEX_UNSET && windowIndex in visited.indices && !visited[windowIndex] && idx < count) {
            shuffledIndices[idx++] = windowIndex
            visited[windowIndex] = true
            windowIndex = timeline.getNextWindowIndex(windowIndex, Player.REPEAT_MODE_OFF, true)
        }
        return if (idx == count) shuffledIndices else null
    }

    @Synchronized
    fun snapCompleteTransition() {
        if (!transitionRunning) return
        Log.d(TAG, "snapCompleteTransition: force-completing active transition")
        transitionRunning = false
        transitionJob?.cancel()
        if (::playerB.isInitialized) {
            playerB.volume = 0f
            playerB.stop()
            playerB.clearMediaItems()
        }
        if (::playerA.isInitialized) {
            playerA.volume = userVolume
            setPauseAtEndOfMediaItems(false)
        }
    }

    fun cancelNext() {
        transitionJob?.cancel()
        val wasTransitioning = transitionRunning
        transitionRunning = false
        if (::playerB.isInitialized && playerB.mediaItemCount > 0) {
            Log.d(TAG, "Cancelling next player")
            playerB.stop()
            playerB.clearMediaItems()
        }
        if (::playerA.isInitialized) {
            if (wasTransitioning) {
                playerA.volume = userVolume
            }
            setPauseAtEndOfMediaItems(false)
        }
    }

    @Synchronized
    fun performTransition(settings: TransitionSettings) {
        if (isTransitionRunning()) {
            Log.w(TAG, "Ignoring duplicate transition request; a transition is already active.")
            return
        }

        transitionRunning = true
        transitionJob = scope.launch {
            try {
                performOverlapTransition(settings)
            } catch (_: CancellationException) {
                Log.d(TAG, "Transition cancelled before completion.")
            } catch (e: Exception) {
                Log.e(TAG, "Error performing transition", e)
                playerA.volume = userVolume
                setPauseAtEndOfMediaItems(false)
                playerB.stop()
            } finally {
                transitionRunning = false
            }
        }
    }

    private suspend fun performOverlapTransition(settings: TransitionSettings) {
        if (playerB.mediaItemCount == 0) {
            playerA.volume = userVolume
            setPauseAtEndOfMediaItems(false)
            return
        }

        val outgoingPlayer = playerA
        val incomingPlayer = playerB
        val targetVolume = userVolume

        val outgoingMediaItemCount = outgoingPlayer.mediaItemCount
        val currentOutgoingIndex = outgoingPlayer.currentMediaItemIndex
            .takeIf { it in 0 until outgoingMediaItemCount }
            ?: 0

        val incomingMediaId = incomingPlayer.currentMediaItem?.mediaId
        val isSelfTransition = outgoingPlayer.currentMediaItem?.mediaId == incomingMediaId
        if (incomingPlayer.mediaItemCount <= 1 && outgoingMediaItemCount > 1) {
            val fullQueue = (0 until outgoingMediaItemCount).map { outgoingPlayer.getMediaItemAt(it) }
            val incomingQueueIndex = when {
                isSelfTransition -> currentOutgoingIndex
                incomingMediaId != null -> (0 until outgoingMediaItemCount)
                    .firstOrNull { index -> outgoingPlayer.getMediaItemAt(index).mediaId == incomingMediaId }
                    ?: currentOutgoingIndex
                else -> currentOutgoingIndex
            }
            incomingPlayer.setMediaItems(fullQueue, incomingQueueIndex, 0L)
            if (outgoingPlayer.shuffleModeEnabled) {
                extractShuffleIndices(outgoingPlayer)?.let { indices ->
                    incomingPlayer.setShuffleOrder(RhythmShuffleOrder(indices))
                }
            }
        }

        incomingPlayer.repeatMode = outgoingPlayer.repeatMode
        incomingPlayer.shuffleModeEnabled = outgoingPlayer.shuffleModeEnabled
        incomingPlayer.playbackParameters = outgoingPlayer.playbackParameters

        outgoingPlayer.removeListener(masterPlayerListener)

        val incomingReplayGain = if (incomingPlayer === playerA) playerAReplayGain else playerBReplayGain
        val incomingDolbyGain = if (incomingPlayer === playerA) playerADolbyGain else playerBDolbyGain
        playerA = incomingPlayer
        playerB = outgoingPlayer
        activeReplayGainProcessor = incomingReplayGain
        activeDolbyGainProcessor = incomingDolbyGain

        val mediaIdToSync = playerA.currentMediaItem?.mediaId ?: incomingMediaId
        val tracks = playerA.currentTracks
        val format = tracks.getFirstSelectedTrackFormatByType(C.TRACK_TYPE_AUDIO) ?: (playerA as? ExoPlayer)?.audioFormat
        val mime = format?.sampleMimeType.orEmpty()
        val isDolby = mime.contains("eac3") || mime.contains("ac4")
        
        activeDolbyGainProcessor?.isDolbyAtmos = isDolby

        if (isDolby) {
            incomingReplayGain.setMode(ReplayGainUtil.Mode.None, false)
        } else {
            val cachedTags = ReplayGainCache.get(mediaIdToSync)
            if (cachedTags != null) {
                incomingReplayGain.setTags(cachedTags)
            } else if (format != null) {
                val info = ReplayGainUtil.parse(format)
                if (mediaIdToSync != null) {
                    ReplayGainCache.put(mediaIdToSync, info)
                }
                val appSettings = AppSettings.getInstance(context)
                applyReplayGainSettingsOnProcessor(incomingReplayGain, appSettings.replayGain.value)
                incomingReplayGain.setRootFormat(format)
            }
        }

        playerB.pauseAtEndOfMediaItems = true
        playerA.pauseAtEndOfMediaItems = false

        playerA.addListener(masterPlayerListener)
        if (playerA.playWhenReady) {
            requestAudioFocus()
        }

        onPlayerSwappedListeners.forEach { it(playerA) }

        _activeAudioSessionId.value = playerA.audioSessionId

        val swappedFormat = (playerA as? ExoPlayer)?.audioFormat ?: playerA.currentTracks.getFirstSelectedTrackFormatByType(C.TRACK_TYPE_AUDIO)
        val swappedDecoder = if (playerA === incomingPlayer) {
            if (incomingPlayer === playerA) playerADecoderName else playerBDecoderName
        } else playerADecoderName
        if (swappedFormat != null) {
            _currentEngineFormat.value = EngineAudioFormat(swappedFormat, swappedDecoder)
        }

        if (playerA.playbackState == Player.STATE_IDLE) {
            playerA.prepare()
        }

        var readinessChecks = 0
        val maxReadinessChecks = if (settings.isManualSkip) 16 else 60
        while (playerA.playbackState == Player.STATE_BUFFERING && readinessChecks < maxReadinessChecks) {
            delay(20)
            readinessChecks++
        }

        val incomingReady = playerA.playbackState == Player.STATE_READY
        var isFading = false

        if (incomingReady || settings.isManualSkip) {
            playerA.volume = 0f
            playerB.volume = targetVolume
            if (!playerB.isPlaying && playerB.playbackState == Player.STATE_READY) {
                playerB.play()
            }

            playerA.playWhenReady = true
            playerA.play()
            isFading = true
        }

        if (isFading) {
            val configuredDuration = settings.durationMs.toLong().coerceAtLeast(500L)
            val remainingAudio = if (playerB.duration > 0 && playerB.currentPosition >= 0) {
                (playerB.duration - playerB.currentPosition).coerceAtLeast(500L)
            } else {
                configuredDuration
            }
            val fadeDuration = if (!settings.isManualSkip) {
                configuredDuration.coerceAtMost(remainingAudio)
            } else {
                configuredDuration
            }

            val stepMs = 16L
            var elapsed = 0L

            while (elapsed <= fadeDuration && transitionRunning) {
                while (!playerA.playWhenReady && transitionRunning) {
                    if (playerB.playWhenReady) {
                        playerB.playWhenReady = false
                    }
                    delay(50)
                }
                if (playerA.playWhenReady && !playerB.playWhenReady && playerB.playbackState != Player.STATE_ENDED) {
                    playerB.playWhenReady = true
                }

                if (!transitionRunning) break

                val progress = (elapsed.toFloat() / fadeDuration).coerceIn(0f, 1f)
                val volIn = calculateVolumeIn(progress, settings.curveIn) * targetVolume
                val volOut = calculateVolumeOut(progress, settings.curveOut) * targetVolume

                playerA.volume = volIn.coerceIn(0f, targetVolume)
                playerB.volume = volOut.coerceIn(0f, targetVolume)

                if (playerA.playbackState == Player.STATE_ENDED) {
                    break
                }

                delay(stepMs)
                elapsed += stepMs
            }
        } else {
            playerA.volume = targetVolume
            if (playerA.playbackState == Player.STATE_READY) {
                playerA.play()
            } else {
                playerA.playWhenReady = true
            }
        }

        playerB.volume = 0f
        playerA.volume = targetVolume

        playerB.pause()
        playerB.stop()
        playerB.clearMediaItems()

        try {
            playerB.seekTo(0)
            playerB.playbackParameters = playerA.playbackParameters
        } catch (e: Exception) {
            playerB.release()
            val otherReplayGain = if (incomingReplayGain === playerAReplayGain) playerBReplayGain else playerAReplayGain
            val otherDolbyGain = if (incomingDolbyGain === playerADolbyGain) playerBDolbyGain else playerADolbyGain
            val otherBassBoost = if (incomingReplayGain === playerAReplayGain) playerBBassBoost else playerABassBoost
            val otherSpatial = if (incomingReplayGain === playerAReplayGain) playerBSpatialization else playerASpatialization
            val otherMono = if (incomingReplayGain === playerAReplayGain) playerBMono else playerAMono
            playerB = buildPlayer(
                handleAudioFocus = false,
                bassProcessor = otherBassBoost,
                spatialProcessor = otherSpatial,
                monoProcessor = otherMono,
                replayGainProcessor = otherReplayGain,
                dolbyGainProcessor = otherDolbyGain
            ).apply {
                playbackParameters = playerA.playbackParameters
            }
        }
    }

    fun getActiveReplayGainProcessor(): ReplayGainAudioProcessor? = activeReplayGainProcessor

    private fun applyReplayGainSettingsOnProcessor(processor: ReplayGainAudioProcessor, enabled: Boolean) {
        val appSettings = AppSettings.getInstance(context)
        val mode = if (enabled) {
            when (appSettings.replayGainMode.value) {
                1 -> ReplayGainUtil.Mode.Track
                2 -> ReplayGainUtil.Mode.Album
                else -> ReplayGainUtil.Mode.None
            }
        } else {
            ReplayGainUtil.Mode.None
        }
        processor.setMode(mode, false)
        processor.setReduceGain(appSettings.replayGainDrc.value)
        processor.setRgGain(appSettings.replayGainPreamp.value.toInt())
        processor.setNonRgGain(appSettings.replayGainPreampUntagged.value.toInt())
    }

    fun applyReplayGainSettings(enabled: Boolean) {
        val currentMime = (masterPlayer as? ExoPlayer)?.audioFormat?.sampleMimeType.orEmpty()
        val isDolby = currentMime.contains("eac3") || currentMime.contains("ac4")
        if (!isDolby) {
            if (::playerAReplayGain.isInitialized) {
                applyReplayGainSettingsOnProcessor(playerAReplayGain, enabled)
            }
            if (::playerBReplayGain.isInitialized) {
                applyReplayGainSettingsOnProcessor(playerBReplayGain, enabled)
            }
            Log.d(TAG, "Replay Gain settings applied on both player processors: enabled=$enabled")
        } else {
            Log.d(TAG, "Replay Gain ignorado: faixa atual é Dolby Atmos (gerenciada nativamente em -18 LKFS)")
        }
        updateTrackSelectionParameters()
    }

    private fun buildTrackSelectionParameters(
        baseParameters: TrackSelectionParameters,
        appSettings: AppSettings
    ): TrackSelectionParameters {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.Q) {
            return baseParameters
        }

        val isCrossfadeEnabled = appSettings.crossfade.value
        val isEqualizerEnabled = appSettings.equalizerEnabled.value
        val isReplayGainEnabled = appSettings.replayGain.value
        val isBassBoostEnabled = appSettings.bassBoostEnabled.value
        val isVirtualizerEnabled = appSettings.virtualizerEnabled.value
        val isMonoAudioEnabled = appSettings.monoAudioEnabled.value
        val isPlaybackRateModified =
            kotlin.math.abs(appSettings.playbackSpeed.value - 1f) > 0.001f ||
            kotlin.math.abs(appSettings.playbackPitch.value - 1f) > 0.001f

        val isSkipSilenceEnabled = appSettings.skipSilenceEnabled.value

        val isOffloadSupported = appSettings.isAudioOffloadActive.value &&
            (!isCrossfadeEnabled && !isEqualizerEnabled && !isReplayGainEnabled &&
             !isBassBoostEnabled && !isVirtualizerEnabled && !isMonoAudioEnabled &&
             !isPlaybackRateModified && !isSkipSilenceEnabled)

        val audioOffloadPreferences = TrackSelectionParameters.AudioOffloadPreferences.Builder()
            .setAudioOffloadMode(
                if (isOffloadSupported) {
                    TrackSelectionParameters.AudioOffloadPreferences.AUDIO_OFFLOAD_MODE_ENABLED
                } else {
                    TrackSelectionParameters.AudioOffloadPreferences.AUDIO_OFFLOAD_MODE_DISABLED
                }
            )
            .setIsSpeedChangeSupportRequired(true)
            .setIsGaplessSupportRequired(appSettings.gaplessPlayback.value)
            .build()

        return baseParameters.buildUpon()
            .setAudioOffloadPreferences(audioOffloadPreferences)
            .build()
    }

    fun updatePlaybackParameters() {
        if (!::playerA.isInitialized || !::playerB.isInitialized) return
        val appSettings = AppSettings.getInstance(context)
        val speed = appSettings.playbackSpeed.value.coerceIn(0.25f, 3.0f)
        val pitch = appSettings.playbackPitch.value.coerceIn(0.5f, 2.0f)
        val params = PlaybackParameters(speed, pitch)
        if (playerA.playbackParameters != params) {
            playerA.playbackParameters = params
            Log.d(TAG, "Applied playback parameters on playerA: speed=$speed, pitch=$pitch")
        }
        if (playerB.playbackParameters != params) {
            playerB.playbackParameters = params
            Log.d(TAG, "Applied playback parameters on playerB: speed=$speed, pitch=$pitch")
        }
    }

    fun updateTrackSelectionParameters() {
        scope.launch(Dispatchers.Main) {
            if (!::playerA.isInitialized || !::playerB.isInitialized) return@launch
            val appSettings = AppSettings.getInstance(context)
            val paramsA = buildTrackSelectionParameters(playerA.trackSelectionParameters, appSettings)
            val paramsB = buildTrackSelectionParameters(playerB.trackSelectionParameters, appSettings)
            if (playerA.trackSelectionParameters != paramsA) {
                playerA.trackSelectionParameters = paramsA
            }
            if (playerB.trackSelectionParameters != paramsB) {
                playerB.trackSelectionParameters = paramsB
            }
        }
    }

    fun release() {
        setPauseAtEndOfMediaItems(false)
        transitionJob?.cancel()
        scope.cancel()
        abandonAudioFocus()
        if (::playerA.isInitialized) {
            playerA.removeAnalyticsListener(analyticsListenerA)
            playerA.removeListener(masterPlayerListener)
            playerA.release()
        }
        if (::playerB.isInitialized) {
            playerB.removeAnalyticsListener(analyticsListenerB)
            playerB.release()
        }
        isReleased = true
        Log.d(TAG, "RhythmPlayerEngine released.")
    }

    fun getCurrentAudioFormat(): androidx.media3.common.Format? =
        _currentEngineFormat.value?.format ?: (masterPlayer as? ExoPlayer)?.audioFormat

    fun getCurrentDecoderName(): String =
        _currentEngineFormat.value?.decoderName.orEmpty()
}

data class EngineAudioFormat(
    val format: androidx.media3.common.Format,
    val decoderName: String = "",
    val timestamp: Long = System.currentTimeMillis()
)

/**
 * Processador de áudio que atenua faixas em Dolby Atmos (E-AC-3 JOC / AC-4) em -4 dB (fator 0.631).
 * Permanece sempre ativo na cadeia PCM 16-bit. Quando a faixa não é Dolby, executa cópia direta
 * de buffers via put(ByteBuffer), com custo zero de CPU e sem fragmentação de memória.
 */
@OptIn(UnstableApi::class)
class DolbyGainAudioProcessor : BaseAudioProcessor() {

    @Volatile
    var isDolbyAtmos: Boolean = false

    override fun onConfigure(inputAudioFormat: AudioProcessor.AudioFormat): AudioProcessor.AudioFormat {
        return if (inputAudioFormat.encoding == C.ENCODING_PCM_16BIT) {
            inputAudioFormat
        } else {
            AudioProcessor.AudioFormat.NOT_SET
        }
    }

    override fun queueInput(inputBuffer: ByteBuffer) {
        val remaining = inputBuffer.remaining()
        if (remaining == 0) return
        val out = replaceOutputBuffer(remaining)

        if (!isDolbyAtmos) {
            // Cópia direta e instantânea em memória para arquivos comuns (FLAC, MP3, ALAC, WAV)
            out.put(inputBuffer)
        } else {
            // Atenuação de -4 dB apenas em faixas Atmos para blindar contra clipping e anular os -14 dB da Samsung
            while (inputBuffer.hasRemaining()) {
                val sample = inputBuffer.short
                val scaled = (sample * DOLBY_HEADROOM_GAIN).roundToInt().coerceIn(-32768, 32767).toShort()
                out.putShort(scaled)
            }
        }
        out.flip()
    }
}

/**
 * Renderizador MediaCodec que força o decodificador nativo da Dolby (c2.dolby.eac3.decoder)
 * a executar o downmix binaural por objetos para auscultadores (2 canais estéreo) a -18 LKFS.
 */
@OptIn(UnstableApi::class)
private class DolbyMediaCodecAudioRenderer(
    context: Context,
    codecAdapterFactory: MediaCodecAdapter.Factory,
    mediaCodecSelector: MediaCodecSelector,
    enableDecoderFallback: Boolean,
    eventHandler: Handler?,
    eventListener: AudioRendererEventListener?,
    audioSink: AudioSink,
    private val dolbyGainProcessor: DolbyGainAudioProcessor?
) : MediaCodecAudioRenderer(
    context,
    codecAdapterFactory,
    mediaCodecSelector,
    enableDecoderFallback,
    eventHandler,
    eventListener,
    audioSink
) {
    override fun getMediaFormat(
        format: androidx.media3.common.Format,
        codecMimeType: String,
        codecMaxInputSize: Int,
        codecOperatingRate: Float
    ): MediaFormat {
        val mediaFormat = super.getMediaFormat(format, codecMimeType, codecMaxInputSize, codecOperatingRate)
        if (codecMimeType.contains("eac3") || codecMimeType.contains("ac4")) {
            dolbyGainProcessor?.isDolbyAtmos = true
            try {
                // 1. Limita a saída a 2 canais para acionar a binauralização interna no chip da Dolby
                mediaFormat.setInteger(MediaFormat.KEY_MAX_OUTPUT_CHANNEL_COUNT, 2)
                mediaFormat.setInteger("max-output-channel-count", 2)

                // 2. Parâmetros proprietários da Dolby (2 = Auscultadores, 1 = DAX Ativo)
                mediaFormat.setInteger("vendor.dolby.active-device.value", DOLBY_ACTIVE_DEVICE)
                mediaFormat.setInteger("vendor.dolby.dax-state.value", DOLBY_DAX_STATE)

                // 3. Normalização estrita da Dolby a -18 LKFS / LUFS (padrão de estúdio)
                mediaFormat.setInteger("vendor.dolby.output-level.value", -18)

                // 4. Desativa o compressor dinâmico interno da Dolby que causa o efeito de bombeamento
                mediaFormat.setInteger("vendor.dolby.dap.volume-leveler.enable", 0)
                mediaFormat.setInteger("vendor.dolby.dap.dvle.value", 0)

                Log.d(DOLBY_TAG, "Dolby vendor params set: mime=$codecMimeType activeDevice=$DOLBY_ACTIVE_DEVICE dax=$DOLBY_DAX_STATE outputLevel=-18 maxChannels=2")
            } catch (e: Exception) {
                Log.w(DOLBY_TAG, "Failed to set Dolby vendor params", e)
            }
        } else {
            dolbyGainProcessor?.isDolbyAtmos = false
        }
        return mediaFormat
    }
}

/**
 * Envolve o renderizador do FFmpeg e rejeita categoricamente AC3, E-AC-3, E-AC-3 JOC e AC-4.
 */
@OptIn(UnstableApi::class)
private class NoDolbyRenderer(private val base: Renderer) : Renderer by base {
    override fun getCapabilities(): RendererCapabilities = NoDolbyCapabilities(base.capabilities)
}

@OptIn(UnstableApi::class)
private class NoDolbyCapabilities(private val base: RendererCapabilities) : RendererCapabilities by base {
    private val blockedMimeTypes = setOf(
        MimeTypes.AUDIO_AC3,
        MimeTypes.AUDIO_E_AC3,
        MimeTypes.AUDIO_E_AC3_JOC,
        MimeTypes.AUDIO_AC4
    )

    override fun supportsFormat(format: androidx.media3.common.Format): Int {
        return if (format.sampleMimeType in blockedMimeTypes) {
            RendererCapabilities.create(C.FORMAT_UNSUPPORTED_TYPE)
        } else {
            base.supportsFormat(format)
        }
    }
}

private fun androidx.media3.common.Tracks.getFirstSelectedTrackFormatByType(trackType: Int): androidx.media3.common.Format? {
    for (group in groups) {
        if (group.type == trackType && group.isSelected) {
            for (i in 0 until group.length) {
                if (group.isTrackSelected(i)) {
                    return group.getTrackFormat(i)
                }
            }
        }
    }
    return null
}
