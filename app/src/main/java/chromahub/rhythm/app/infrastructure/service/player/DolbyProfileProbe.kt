package chromahub.rhythm.app.infrastructure.service.player

import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.media.AudioManager
import android.os.Build
import android.os.Handler
import android.os.Looper
import android.util.Log

object DolbyProfileProbe {
    private const val TAG = "DolbyProbe"
    private const val ACTION_PROBE = "chromahub.rhythm.app.DOLBY_PROBE"
    private val handler = Handler(Looper.getMainLooper())
    private var isReceiverRegistered = false

    fun registerReceiver(
        context: Context,
        audioManager: AudioManager,
        condition: () -> Boolean
    ) {
        if (isReceiverRegistered) return
        val receiver = object : BroadcastReceiver() {
            override fun onReceive(ctx: Context?, intent: Intent?) {
                if (intent?.action == ACTION_PROBE) {
                    Log.d(TAG, "Broadcast recebido. A iniciar bateria de testes...")
                    runDolbyProbe(audioManager, condition)
                }
            }
        }
        val filter = IntentFilter(ACTION_PROBE)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            context.registerReceiver(receiver, filter, Context.RECEIVER_EXPORTED)
        } else {
            context.registerReceiver(receiver, filter)
        }
        isReceiverRegistered = true
    }

    fun runDolbyProbe(audioManager: AudioManager, condition: () -> Boolean) {
        if (!condition()) {
            Log.w(TAG, "Condição não cumprida: reprodução inativa ou faixa não é Dolby Atmos.")
            return
        }

        val variants = listOf(
            "V1 (Profile 6 puro)" to {
                audioManager.setParameters("g_effect_dolby_enable=1;g_effect_dolby_profile=6")
            },
            "V2 (Profile 6 + Game switch)" to {
                audioManager.setParameters("g_effect_dolby_enable=1;g_effect_game_dolby_enable=1;g_effect_dolby_profile=6")
            },
            "V3 (Game switch primeiro, profile 6 apos 150ms)" to {
                audioManager.setParameters("g_effect_game_dolby_enable=1")
                handler.postDelayed({
                    audioManager.setParameters("g_effect_dolby_enable=1;g_effect_dolby_profile=6")
                }, 150)
            },
            "V4 (Profile 1 Movie - Controlo)" to {
                audioManager.setParameters("g_effect_dolby_enable=1;g_effect_dolby_profile=1")
            },
            "V5 (Profile 4 Game)" to {
                audioManager.setParameters("g_effect_dolby_enable=1;g_effect_game_dolby_enable=1;g_effect_dolby_profile=4")
            },
            "V6 (Profile 7 Game2)" to {
                audioManager.setParameters("g_effect_dolby_enable=1;g_effect_dolby_profile=7")
            },
            "V7 (Profile 6 + Leveler 0 separado)" to {
                audioManager.setParameters("g_effect_dolby_enable=1;g_effect_dolby_profile=6")
                handler.postDelayed({
                    audioManager.setParameters("volume_leveler=0")
                }, 150)
            }
        )

        variants.forEachIndexed { index, (name, action) ->
            val delayMs = index * 3000L
            handler.postDelayed({
                Log.d(TAG, "--- V${index + 1} inicio: $name ---")
                try {
                    action()
                } catch (e: Exception) {
                    Log.e(TAG, "Erro ao enviar $name", e)
                }
                handler.postDelayed({
                    val currentParams = try {
                        audioManager.getParameters("g_effect_dolby_profile;g_effect_dolby_enable")
                    } catch (e: Exception) {
                        "erro"
                    }
                    Log.d(TAG, "getParameters=$currentParams")
                    Log.d(TAG, "--- V${index + 1} fim ---")
                }, 2500)
            }, delayMs)
        }
    }
}
