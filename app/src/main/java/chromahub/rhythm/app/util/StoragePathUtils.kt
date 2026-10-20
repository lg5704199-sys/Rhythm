/*
 * SPDX-FileCopyrightText: 2024-2026 Anjishnu Nandi <https://github.com/cromaguy>
 * SPDX-License-Identifier: GPL-3.0-or-later
 */

package chromahub.rhythm.app.util

import android.content.Context
import android.net.Uri
import android.os.Build
import android.os.Environment
import android.provider.DocumentsContract
import android.provider.MediaStore
import android.util.Log
import java.io.File
import java.util.Locale

/**
 * Centralized utility for resolving SAF Document Tree URIs, normalizing storage paths,
 * sanitizing corrupted paths, and evaluating folder hierarchies.
 */
object StoragePathUtils {
    private const val TAG = "StoragePathUtils"

    /**
     * Resolves an Android Storage Access Framework (SAF) tree URI into a local filesystem path.
     * Handles external storage documents, downloads provider, media documents, SD cards, and raw URIs.
     */
    fun getPathFromTreeUri(context: Context, uri: Uri): String? {
        try {
            val authority = uri.authority ?: return null

            if (authority == "com.android.externalstorage.documents") {
                val docId = try {
                    DocumentsContract.getTreeDocumentId(uri)
                } catch (_: Exception) {
                    try {
                        DocumentsContract.getDocumentId(uri)
                    } catch (_: Exception) {
                        uri.lastPathSegment ?: ""
                    }
                }

                if (docId.isNotEmpty()) {
                    val colonIndex = docId.indexOf(':')
                    val storageType = if (colonIndex != -1) docId.substring(0, colonIndex) else docId
                    val relativePath = if (colonIndex != -1) {
                        docId.substring(colonIndex + 1).trimStart('/')
                    } else {
                        ""
                    }

                    val basePath = if (storageType.equals("primary", ignoreCase = true) ||
                        storageType.equals("home", ignoreCase = true)
                    ) {
                        try {
                            Environment.getExternalStorageDirectory()?.absolutePath
                        } catch (_: Exception) { null } ?: "/storage/emulated/0"
                    } else {
                        resolveRemovableStoragePath(context, storageType)
                    }

                    val fullPath = if (relativePath.isNotEmpty()) "$basePath/$relativePath" else basePath
                    return sanitizeAndNormalizePath(fullPath)
                }
            }

            if (authority == "com.android.providers.downloads.documents") {
                val docId = try {
                    DocumentsContract.getTreeDocumentId(uri)
                } catch (_: Exception) {
                    try {
                        DocumentsContract.getDocumentId(uri)
                    } catch (_: Exception) {
                        uri.lastPathSegment ?: ""
                    }
                }

                val downloadsDir = try {
                    Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS)?.absolutePath
                } catch (_: Exception) { null } ?: "/storage/emulated/0/Download"
                if (docId.equals("downloads", ignoreCase = true)) {
                    return sanitizeAndNormalizePath(downloadsDir)
                }

                if (docId.startsWith("raw:", ignoreCase = true)) {
                    val rawPath = docId.substring(4)
                    return sanitizeAndNormalizePath(rawPath)
                }

                if (docId.startsWith("msf:", ignoreCase = true)) {
                    val resolved = queryDataColumn(context, uri)
                    return if (!resolved.isNullOrBlank()) {
                        sanitizeAndNormalizePath(resolved)
                    } else {
                        sanitizeAndNormalizePath(downloadsDir)
                    }
                }

                val colonIndex = docId.indexOf(':')
                if (colonIndex != -1) {
                    val relPath = docId.substring(colonIndex + 1).trimStart('/')
                    if (relPath.startsWith("/")) {
                        return sanitizeAndNormalizePath(relPath)
                    }
                    return sanitizeAndNormalizePath("$downloadsDir/$relPath")
                }

                return sanitizeAndNormalizePath(downloadsDir)
            }

            if (authority == "com.android.providers.media.documents") {
                val docId = try {
                    DocumentsContract.getTreeDocumentId(uri)
                } catch (_: Exception) {
                    try {
                        DocumentsContract.getDocumentId(uri)
                    } catch (_: Exception) {
                        uri.lastPathSegment ?: ""
                    }
                }

                val musicDir = try {
                    Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_MUSIC)?.absolutePath
                } catch (_: Exception) { null } ?: "/storage/emulated/0/Music"

                if (docId.contains("audio_root", ignoreCase = true) || docId.contains("music_root", ignoreCase = true)) {
                    return sanitizeAndNormalizePath(musicDir)
                }

                val colonIndex = docId.indexOf(':')
                if (colonIndex != -1) {
                    val relPath = docId.substring(colonIndex + 1).trimStart('/')
                    return sanitizeAndNormalizePath("$musicDir/$relPath")
                }
            }

            val uriPath = uri.path
            if (!uriPath.isNullOrBlank()) {
                val decoded = Uri.decode(uriPath)
                val rawMarker = "/tree/raw:"
                val docRawMarker = "/document/raw:"
                when {
                    decoded.contains(rawMarker) -> {
                        val path = decoded.substringAfter(rawMarker)
                        return sanitizeAndNormalizePath(path)
                    }
                    decoded.contains(docRawMarker) -> {
                        val path = decoded.substringAfter(docRawMarker)
                        return sanitizeAndNormalizePath(path)
                    }
                    uri.scheme == "file" -> {
                        return sanitizeAndNormalizePath(decoded)
                    }
                }
            }
        } catch (e: Exception) {
            Log.e(TAG, "Failed to parse path from tree URI: $uri", e)
        }

        return null
    }

    /**
     * Resolves the mount point of an external SD card or removable volume ID (e.g. 1234-5678 or disk ID).
     */
    private fun resolveRemovableStoragePath(context: Context, volumeId: String): String {
        val directPath = File("/storage/$volumeId")
        if (directPath.exists()) {
            return directPath.absolutePath
        }

        try {
            val externalDirs = context.getExternalFilesDirs(null)
            for (dir in externalDirs) {
                if (dir == null) continue
                val full = dir.absolutePath
                val idx = full.indexOf("/Android/data")
                if (idx != -1) {
                    val root = full.substring(0, idx)
                    if (root.contains(volumeId, ignoreCase = true)) {
                        return root
                    }
                }
            }
        } catch (e: Exception) {
            Log.w(TAG, "Error resolving external storage dirs", e)
        }

        return "/storage/$volumeId"
    }

    /**
     * Queries the MediaStore DATA column for a given URI.
     */
    private fun queryDataColumn(context: Context, uri: Uri): String? {
        val projection = arrayOf(MediaStore.MediaColumns.DATA)
        try {
            context.contentResolver.query(uri, projection, null, null, null)?.use { cursor ->
                if (cursor.moveToFirst()) {
                    val colIndex = cursor.getColumnIndex(MediaStore.MediaColumns.DATA)
                    if (colIndex >= 0) {
                        return cursor.getString(colIndex)
                    }
                }
            }
        } catch (e: Exception) {
            Log.w(TAG, "Failed to query _data column for uri: $uri", e)
        }
        return null
    }

    /**
     * Sanitizes and normalizes filesystem storage paths:
     * - Heals duplicate storage prefixes (e.g. "/storage/emulated/0//storage/emulated/0/Download")
     * - Strips legacy prefixes like "raw:"
     * - Resolves symlinks (e.g. "/sdcard", "/storage/self/primary") to canonical storage paths
     * - Collapses consecutive slashes and trims trailing slashes
     */
    fun sanitizeAndNormalizePath(path: String?): String {
        if (path.isNullOrBlank()) return ""

        var normalized = path.trim().replace('\\', '/')

        if (normalized.startsWith("raw:", ignoreCase = true)) {
            normalized = normalized.substring(4).trim()
        }

        while (normalized.contains("//")) {
            normalized = normalized.replace("//", "/")
        }

        val emulatedPrefix = "/storage/emulated/0"
        while (normalized.startsWith("$emulatedPrefix$emulatedPrefix")) {
            normalized = normalized.removePrefix(emulatedPrefix)
        }
        while (normalized.startsWith("$emulatedPrefix/$emulatedPrefix")) {
            normalized = normalized.removePrefix(emulatedPrefix).trimStart('/')
            normalized = "$emulatedPrefix/$normalized"
        }

        if (normalized.length > 1 && normalized.endsWith('/')) {
            normalized = normalized.substring(0, normalized.length - 1)
        }

        try {
            val externalStorage = try {
                Environment.getExternalStorageDirectory()?.absolutePath
            } catch (_: Exception) { null } ?: "/storage/emulated/0"

            if (normalized.startsWith("/") && !normalized.startsWith(externalStorage)) {
                val candidate = File(normalized).canonicalPath
                if (candidate.startsWith(externalStorage)) {
                    normalized = candidate
                }
            }
        } catch (_: Exception) {}

        return normalized
    }

    /**
     * Set of standard audio file extensions.
     */
    val DEFAULT_AUDIO_EXTENSIONS = setOf(
        "mp3", "flac", "wav", "m4a", "aac", "ogg", "oga", "opus", "wma", "ape",
        "alac", "aiff", "dsd", "dsf", "dff", "mid", "midi"
    )

    /**
     * Checks if child is equal to or a subdirectory of parent.
     * Enforces path boundary check to avoid false matches (e.g., "Music2" will NOT match "Music").
     */
    fun isFolderSubdirectoryOrEqual(parentFolder: String, childPath: String): Boolean {
        val normParent = sanitizeAndNormalizePath(parentFolder)
        val normChild = sanitizeAndNormalizePath(childPath)

        if (normParent.isEmpty() || normChild.isEmpty()) return false

        if (normParent.equals(normChild, ignoreCase = true)) return true

        val parentPrefix = if (normParent.endsWith('/')) normParent else "$normParent/"
        return normChild.startsWith(parentPrefix, ignoreCase = true)
    }

    /**
     * Checks if childPath belongs to any of the specified parentFolders.
     */
    fun isPathInFolders(childPath: String?, parentFolders: Collection<String>): Boolean {
        if (parentFolders.isEmpty() || childPath.isNullOrBlank()) return false
        val normChild = sanitizeAndNormalizePath(childPath)
        val normParents = parentFolders.map { sanitizeAndNormalizePath(it) }.filter { it.isNotEmpty() }

        return normParents.any { normParent ->
            normParent.equals(normChild, ignoreCase = true) ||
                normChild.startsWith(if (normParent.endsWith('/')) normParent else "$normParent/", ignoreCase = true)
        }
    }

    /**
     * Checks if the given filename or path has an audio extension.
     */
    fun isAudioFile(fileNameOrPath: String, customAllowedFormats: Set<String>? = null): Boolean {
        val ext = fileNameOrPath.substringAfterLast('.', "").lowercase(Locale.ROOT)
        if (ext.isEmpty()) return false
        return customAllowedFormats?.contains(ext) ?: DEFAULT_AUDIO_EXTENSIONS.contains(ext)
    }

    /**
     * Extracts the relative folder path of a file with respect to a base folder.
     */
    fun extractFolderRelativePath(baseFolder: String, fullFilePath: String): String {
        val normBase = sanitizeAndNormalizePath(baseFolder)
        val normFull = sanitizeAndNormalizePath(fullFilePath)
        val parentDir = normFull.substringBeforeLast('/', "")
        if (parentDir.isEmpty() || parentDir.equals(normBase, ignoreCase = true)) {
            return ""
        }
        val basePrefix = if (normBase.endsWith('/')) normBase else "$normBase/"
        return if (parentDir.startsWith(basePrefix, ignoreCase = true)) {
            parentDir.removePrefix(basePrefix)
        } else {
            ""
        }
    }

    /**
     * Returns a list of standard common music/audio folders on the device that actually exist.
     * Useful for suggestions in MediaScanSettingsScreen even when the song library is empty.
     */
    fun getCommonMediaFolders(context: Context): List<String> {
        val candidates = mutableListOf<String>()

        try {
            Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_MUSIC)?.absolutePath?.let { candidates.add(it) }
        } catch (_: Exception) {}

        try {
            Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS)?.absolutePath?.let { candidates.add(it) }
        } catch (_: Exception) {}

        try {
            Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_PODCASTS)?.absolutePath?.let { candidates.add(it) }
        } catch (_: Exception) {}

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            try {
                Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_AUDIOBOOKS)?.absolutePath?.let { candidates.add(it) }
            } catch (_: Exception) {}
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            try {
                Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_RECORDINGS)?.absolutePath?.let { candidates.add(it) }
            } catch (_: Exception) {}
        }

        val extStorage = try {
            Environment.getExternalStorageDirectory()
        } catch (_: Exception) { null } ?: File("/storage/emulated/0")

        listOf("Music", "Download", "Podcasts", "Audiobooks", "Recordings").forEach { sub ->
            candidates.add(File(extStorage, sub).absolutePath)
        }

        try {
            val storageDir = File("/storage")
            if (storageDir.exists() && storageDir.isDirectory) {
                storageDir.listFiles()?.forEach { file ->
                    if (file.isDirectory && file.name != "emulated" && file.name != "self" && !file.name.startsWith(".")) {
                        val musicSub = File(file, "Music")
                        if (musicSub.exists() && musicSub.isDirectory) {
                            candidates.add(musicSub.absolutePath)
                        } else {
                            candidates.add(file.absolutePath)
                        }
                    }
                }
            }
        } catch (_: Exception) {}

        return candidates
            .map { sanitizeAndNormalizePath(it) }
            .filter { path ->
                path.isNotEmpty() && try {
                    val file = File(path)
                    file.exists() && file.isDirectory && file.canRead()
                } catch (_: Exception) {
                    false
                }
            }
            .distinct()
            .sorted()
    }
}
