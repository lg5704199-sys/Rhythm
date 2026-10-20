/*
 * SPDX-FileCopyrightText: 2024-2026 Anjishnu Nandi <https://github.com/cromaguy>
 * SPDX-License-Identifier: GPL-3.0-or-later
 */

package chromahub.rhythm.app.features.local.data.repository

import org.junit.Assert.assertEquals
import org.junit.Assert.assertFalse
import org.junit.Assert.assertNotEquals
import org.junit.Assert.assertTrue
import org.junit.Test

class ArtistArtworkFilenameTest {

    @Test
    fun getArtistImageFileName_nonAsciiArtistsDoNotCollide() {
        val artist1 = "はろける"
        val artist2 = "初音ミク"
        val artist3 = "重音テト"

        val file1 = MusicRepository.getArtistImageFileName(artist1)
        val file2 = MusicRepository.getArtistImageFileName(artist2)
        val file3 = MusicRepository.getArtistImageFileName(artist3)

        assertNotEquals(file1, file2)
        assertNotEquals(file2, file3)
        assertNotEquals(file1, file3)

        assertFalse(file1.removeSuffix(".jpg").all { it == '_' })
        assertFalse(file2.removeSuffix(".jpg").all { it == '_' })
        assertFalse(file3.removeSuffix(".jpg").all { it == '_' })

        assertTrue("Expected slug to contain artist name: $file1", file1.startsWith("はろける_"))
        assertTrue("Expected slug to contain artist name: $file2", file2.startsWith("初音ミク_"))
        assertTrue("Expected slug to contain artist name: $file3", file3.startsWith("重音テト_"))
    }

    @Test
    fun getArtistImageFileName_artistsWithPunctuationDoNotCollide() {
        val fileSlash = MusicRepository.getArtistImageFileName("AC/DC")
        val fileDash = MusicRepository.getArtistImageFileName("AC-DC")
        val fileSpace = MusicRepository.getArtistImageFileName("AC DC")

        assertNotEquals(fileSlash, fileDash)
        assertNotEquals(fileDash, fileSpace)
        assertNotEquals(fileSlash, fileSpace)
    }

    @Test
    fun getArtistImageFileName_filesystemSafety() {
        val dangerousName = "Artist/With:Forbidden*Chars?\"<>|\r\n\t"
        val fileName = MusicRepository.getArtistImageFileName(dangerousName)

        val forbiddenChars = listOf('/', '\\', ':', '*', '?', '"', '<', '>', '|', '\r', '\n', '\t')
        for (char in forbiddenChars) {
            assertFalse("Filename contains forbidden char '$char': $fileName", fileName.contains(char))
        }
        assertTrue(fileName.endsWith(".jpg"))
    }

    @Test
    fun getArtistImageFileName_longNamesAreBounded() {
        val veryLongName = "A".repeat(300)
        val fileName = MusicRepository.getArtistImageFileName(veryLongName)

        assertTrue("Filename length exceeds safe limit: ${fileName.length}", fileName.length <= 100)
        assertTrue(fileName.endsWith(".jpg"))
    }

    @Test
    fun legacyArtistImageFileName_demonstratesLegacyCollisionAndSafeMigrationFilter() {
        val legacy1 = MusicRepository.getLegacyArtistImageFileName("はろける")
        val legacy2 = MusicRepository.getLegacyArtistImageFileName("初音ミク")
        val legacy3 = MusicRepository.getLegacyArtistImageFileName("重音テト")

        assertEquals("____.jpg", legacy1)
        assertEquals("____.jpg", legacy2)
        assertEquals("____.jpg", legacy3)

        assertTrue(legacy1.removeSuffix(".jpg").all { it == '_' })

        val validLegacy = MusicRepository.getLegacyArtistImageFileName("Taylor Swift")
        assertEquals("Taylor_Swift.jpg", validLegacy)
        assertFalse(validLegacy.removeSuffix(".jpg").all { it == '_' })
    }

    @Test
    fun getArtistImageFileName_caseInsensitiveHashConsistency() {
        val file1 = MusicRepository.getArtistImageFileName("Taylor Swift")
        val file2 = MusicRepository.getArtistImageFileName("taylor swift")

        val hash1 = file1.substringAfterLast('_').removeSuffix(".jpg")
        val hash2 = file2.substringAfterLast('_').removeSuffix(".jpg")
        assertEquals(hash1, hash2)
    }
}
