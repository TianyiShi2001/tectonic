/* This is dvipdfmx, an eXtended version of dvipdfm by Mark A. Wicks.

    Copyright (C) 2002-2016 by Jin-Hwan Cho and Shunsaku Hirata,
    the dvipdfmx project team.

    Copyright (C) 1998, 1999 by Mark A. Wicks <mwicks@kettering.edu>

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.
*/
#![allow(
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]

use super::dpx_mem::{new, xstrdup};
use super::dpx_numbers::{tt_get_unsigned_pair, tt_get_unsigned_quad};
use crate::mfree;
use crate::{ttstub_input_close, ttstub_input_open, ttstub_input_read, ttstub_input_seek};
#[cfg(not(target_env = "msvc"))]
use libc::mkstemp;
use libc::{close, free, getenv, memcmp, remove, strcat, strcpy, strlen, strncmp, strrchr};
#[cfg(target_env = "msvc")]
extern "C" {
    #[link_name = "dpx_win32_mktemp_s"]
    fn mktemp_s(template: *mut libc::c_char, size: libc::size_t) -> libc::c_int;
}

pub type __ssize_t = i64;
pub type size_t = u64;
pub type ssize_t = __ssize_t;

use crate::TTInputFormat;

use bridge::rust_input_handle_t;
/* quasi-hack to get the primary input */
static mut verbose: i32 = 0i32;
#[no_mangle]
pub static mut keep_cache: i32 = 0i32;
#[no_mangle]
pub unsafe extern "C" fn dpx_file_set_verbose(mut level: i32) {
    verbose = level;
}
static mut _sbuf: [i8; 128] = [0; 128];
/*
 * SFNT type sigs:
 *  `true' (0x74727565): TrueType (Mac)
 *  `typ1' (0x74797031) (Mac): PostScript font housed in a sfnt wrapper
 *  0x00010000: TrueType (Win)/OpenType
 *  `OTTO': PostScript CFF font with OpenType wrapper
 *  `ttcf': TrueType Collection
 */
unsafe extern "C" fn check_stream_is_truetype(mut handle: rust_input_handle_t) -> bool {
    let mut n: i32 = 0;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    n = ttstub_input_read(handle, _sbuf.as_mut_ptr(), 4i32 as size_t) as i32;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    if n != 4i32 {
        return false;
    }
    if memcmp(
        _sbuf.as_mut_ptr() as *const libc::c_void,
        b"true\x00" as *const u8 as *const i8 as *const libc::c_void,
        4,
    ) == 0
        || memcmp(
            _sbuf.as_mut_ptr() as *const libc::c_void,
            b"\x00\x01\x00\x00\x00" as *const u8 as *const i8 as *const libc::c_void,
            4,
        ) == 0
    {
        /* This doesn't help... */
        return true;
    }
    if memcmp(
        _sbuf.as_mut_ptr() as *const libc::c_void,
        b"ttcf\x00" as *const u8 as *const i8 as *const libc::c_void,
        4,
    ) == 0
    {
        return true;
    }
    false
}
/* "OpenType" is only for ".otf" here */
unsafe extern "C" fn check_stream_is_opentype(mut handle: rust_input_handle_t) -> bool {
    let mut n: i32 = 0;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    n = ttstub_input_read(handle, _sbuf.as_mut_ptr(), 4i32 as size_t) as i32;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    if n != 4i32 {
        return false;
    }
    if memcmp(
        _sbuf.as_mut_ptr() as *const libc::c_void,
        b"OTTO\x00" as *const u8 as *const i8 as *const libc::c_void,
        4,
    ) == 0
    {
        return true;
    }
    false
}
unsafe extern "C" fn check_stream_is_type1(mut handle: rust_input_handle_t) -> bool {
    let mut p: *mut i8 = _sbuf.as_mut_ptr();
    let mut n: i32 = 0;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    n = ttstub_input_read(handle, p, 21i32 as size_t) as i32;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    if n != 21i32 {
        return false;
    }
    if *p.offset(0) as i32 != 0x80i32 as i8 as i32
        || (*p.offset(1) as i32) < 0i32
        || *p.offset(1) as i32 > 3i32
    {
        return false;
    }
    if memcmp(
        p.offset(6) as *const libc::c_void,
        b"%!PS-AdobeFont\x00" as *const u8 as *const i8 as *const libc::c_void,
        14,
    ) == 0
        || memcmp(
            p.offset(6) as *const libc::c_void,
            b"%!FontType1\x00" as *const u8 as *const i8 as *const libc::c_void,
            11,
        ) == 0
    {
        return true;
    }
    if memcmp(
        p.offset(6) as *const libc::c_void,
        b"%!PS\x00" as *const u8 as *const i8 as *const libc::c_void,
        4,
    ) == 0
    {
        /* This was #if-0'd out:
         * p[20] = '\0'; p += 6;
         * warn!("Ambiguous PostScript resource type: {}", (char *) p);
         */
        return true;
    }
    false
}
unsafe extern "C" fn check_stream_is_dfont(mut handle: rust_input_handle_t) -> bool {
    let mut n: i32 = 0;
    let mut pos = 0_u32;
    ttstub_input_seek(handle, 0i32 as ssize_t, 0i32);
    tt_get_unsigned_quad(handle);
    pos = tt_get_unsigned_quad(handle);
    ttstub_input_seek(handle, pos.wrapping_add(0x18_u32) as ssize_t, 0i32);
    ttstub_input_seek(
        handle,
        pos.wrapping_add(tt_get_unsigned_pair(handle) as u32) as ssize_t,
        0i32,
    );
    n = tt_get_unsigned_pair(handle) as i32;
    for _ in 0..=n {
        if tt_get_unsigned_quad(handle) as u64 == 0x73666e74 {
            /* "sfnt" */
            return true;
        }
        tt_get_unsigned_quad(handle);
    }
    false
}
/* ensuresuffix() returns a copy of basename if sfx is "". */
unsafe extern "C" fn ensuresuffix(mut basename: *const i8, mut sfx: *const i8) -> *mut i8 {
    let mut q: *mut i8 = 0 as *mut i8;
    let mut p: *mut i8 = 0 as *mut i8;
    p = new((strlen(basename).wrapping_add(strlen(sfx)).wrapping_add(1))
        .wrapping_mul(::std::mem::size_of::<i8>()) as _) as *mut i8;
    strcpy(p, basename);
    q = strrchr(p, '.' as i32);
    if q.is_null() && *sfx.offset(0) as i32 != 0 {
        strcat(p, sfx);
    }
    p
}
/* tmp freed here */
/* Tectonic-enabled I/O alternatives */
#[no_mangle]
pub unsafe extern "C" fn dpx_tt_open(
    mut filename: *const i8,
    mut suffix: *const i8,
    mut format: TTInputFormat,
) -> rust_input_handle_t {
    let mut q: *mut i8 = 0 as *mut i8;
    let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
    q = ensuresuffix(filename, suffix);
    handle = ttstub_input_open(q, format, 0i32);
    free(q as *mut libc::c_void);
    handle
}
/* Search order:
 *   SFDFONTS (TDS 1.1)
 *   ttf2pk   (text file)
 *   ttf2tfm  (text file)
 *   dvipdfm  (text file)
 */
#[no_mangle]
pub unsafe extern "C" fn dpx_open_type1_file(mut filename: *const i8) -> rust_input_handle_t {
    let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
    handle = ttstub_input_open(filename, TTInputFormat::TYPE1, 0i32);
    if handle.is_null() {
        return 0 as *mut libc::c_void;
    }
    if !check_stream_is_type1(handle) {
        ttstub_input_close(handle);
        return 0 as *mut libc::c_void;
    }
    handle
}
#[no_mangle]
pub unsafe extern "C" fn dpx_open_truetype_file(mut filename: *const i8) -> rust_input_handle_t {
    let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
    handle = ttstub_input_open(filename, TTInputFormat::TRUETYPE, 0i32);
    if handle.is_null() {
        return 0 as *mut libc::c_void;
    }
    if !check_stream_is_truetype(handle) {
        ttstub_input_close(handle);
        return 0 as *mut libc::c_void;
    }
    handle
}
#[no_mangle]
pub unsafe extern "C" fn dpx_open_opentype_file(mut filename: *const i8) -> rust_input_handle_t {
    let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
    let mut q: *mut i8 = 0 as *mut i8;
    q = ensuresuffix(filename, b".otf\x00" as *const u8 as *const i8);
    handle = ttstub_input_open(q, TTInputFormat::OPENTYPE, 0i32);
    free(q as *mut libc::c_void);
    if handle.is_null() {
        return 0 as *mut libc::c_void;
    }
    if !check_stream_is_opentype(handle) {
        ttstub_input_close(handle);
        return 0 as *mut libc::c_void;
    }
    handle
}
#[no_mangle]
pub unsafe extern "C" fn dpx_open_dfont_file(mut filename: *const i8) -> rust_input_handle_t {
    let mut q: *mut i8 = 0 as *mut i8;
    let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
    let mut len: i32 = strlen(filename) as i32;
    if len > 6i32
        && strncmp(
            filename.offset(len as isize).offset(-6),
            b".dfont\x00" as *const u8 as *const i8,
            6,
        ) != 0
    {
        /* I've double-checked that we're accurately representing the original
         * code -- the above strncmp() is *not* missing a logical negation.
         */
        q = new(
            ((len + 6i32) as u32 as u64).wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32,
        ) as *mut i8;
        strcpy(q, filename);
        strcat(q, b"/rsrc\x00" as *const u8 as *const i8);
    } else {
        q = xstrdup(filename)
    }
    handle = ttstub_input_open(q, TTInputFormat::TRUETYPE, 0i32);
    free(q as *mut libc::c_void);
    if handle.is_null() {
        return 0 as *mut libc::c_void;
    }
    if !check_stream_is_dfont(handle) {
        ttstub_input_close(handle);
        return 0 as *mut libc::c_void;
    }
    handle
}
unsafe extern "C" fn dpx_get_tmpdir() -> *mut i8 {
    let mut i: size_t = 0;
    let mut ret: *mut i8 = 0 as *mut i8;
    let mut _tmpd: *const i8 = 0 as *const i8;
    _tmpd = getenv(b"TMPDIR\x00" as *const u8 as *const i8);
    if _tmpd.is_null() {
        _tmpd = b"/tmp\x00" as *const u8 as *const i8
    }
    ret = xstrdup(_tmpd);
    i = strlen(ret) as _;
    while i > 1i32 as u64 && *ret.offset(i.wrapping_sub(1i32 as u64) as isize) as i32 == '/' as i32
    {
        *ret.offset(i.wrapping_sub(1i32 as u64) as isize) = '\u{0}' as i32 as i8;
        i = i.wrapping_sub(1)
    }
    ret
}
#[no_mangle]
pub unsafe extern "C" fn dpx_create_temp_file() -> *mut i8 {
    let mut tmpdir: *mut i8 = 0 as *mut i8;
    let mut n: size_t = 0;
    let mut tmp: *mut i8 = 0 as *mut i8;
    #[cfg(not(target_env = "msvc"))]
    const TEMPLATE: &[u8] = b"/dvipdfmx.XXXXXX\x00";
    #[cfg(target_env = "msvc")]
    const TEMPLATE: &[u8] = b"\\dvipdfmx.XXXXXX\x00";
    tmpdir = dpx_get_tmpdir();
    n = strlen(tmpdir)
        .wrapping_add(strlen(TEMPLATE.as_ptr() as *const u8 as *const i8))
        .wrapping_add(1) as _;
    tmp = new((n as u32 as u64).wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32) as *mut i8;
    strcpy(tmp, tmpdir);
    free(tmpdir as *mut libc::c_void);
    strcat(tmp, TEMPLATE.as_ptr() as *const u8 as *const i8);
    #[cfg(not(target_env = "msvc"))]
    {
        let mut _fd: i32 = mkstemp(tmp);
        if _fd != -1i32 {
            close(_fd);
        } else {
            tmp = mfree(tmp as *mut libc::c_void) as *mut i8
        }
    }
    #[cfg(target_env = "msvc")]
    {
        if mktemp_s(tmp, n as _) != 0 {
            tmp = mfree(tmp as *mut libc::c_void) as *mut i8;
        }
    }
    tmp
}
#[no_mangle]
pub unsafe extern "C" fn dpx_delete_old_cache(mut life: i32) {
    /* This used to delete files in tmpdir, but that code was ripped out since
     * it would have been annoying to port to Windows. */
    if life == -2i32 {
        keep_cache = -1i32
    };
}
#[no_mangle]
pub unsafe extern "C" fn dpx_delete_temp_file(mut tmp: *mut i8, mut force: i32) {
    if tmp.is_null() {
        return;
    }
    if force != 0 || keep_cache != 1i32 {
        remove(tmp);
    }
    free(tmp as *mut libc::c_void);
}
/* dpx_file_apply_filter() is used for converting unsupported graphics
 * format to one of the formats that dvipdfmx can natively handle.
 * 'input' is the filename of the original file and 'output' is actually
 * temporal files 'generated' by the above routine.
 * This should be system dependent. (MiKTeX may want something different)
 * Please modify as appropriate (see also pdfximage.c and dvipdfmx.c).
 */
#[no_mangle]
pub unsafe extern "C" fn dpx_file_apply_filter(
    mut _cmdtmpl: *const i8,
    mut _input: *const i8,
    mut _output: *const i8,
    mut _version: u8,
) -> i32 {
    /* Tectonic: defused */
    -1i32
}
