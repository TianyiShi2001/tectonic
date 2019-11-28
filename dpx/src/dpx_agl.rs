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
    unused_mut
)]

use crate::DisplayExt;
use crate::{info, warn};
use crate::{streq_ptr, strstartswith};
use std::ffi::CStr;

use super::dpx_dpxfile::dpx_tt_open;
use super::dpx_dpxutil::{ht_append_table, ht_clear_table, ht_init_table, ht_lookup_table};
use super::dpx_mem::new;
use super::dpx_mfileio::tt_mfgets;
use super::dpx_pdfparse::{parse_ident, skip_white};
use super::dpx_unicode::{UC_UTF16BE_encode_char, UC_is_valid};
use crate::ttstub_input_close;
use libc::{free, memcmp, memcpy, strchr, strcmp, strcpy, strlen, strncpy, strtol};

pub type __ssize_t = i64;
pub type size_t = u64;
pub type ssize_t = __ssize_t;

use crate::TTInputFormat;

#[derive(Copy, Clone)]
#[repr(C)]
pub struct agl_name {
    pub name: *mut i8,
    pub suffix: *mut i8,
    pub n_components: i32,
    pub unicodes: [i32; 16],
    pub alternate: *mut agl_name,
    pub is_predef: i32,
}
use super::dpx_dpxutil::ht_entry;
use super::dpx_dpxutil::ht_table;
pub type hval_free_func = Option<unsafe extern "C" fn(_: *mut libc::c_void) -> ()>;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct C2RustUnnamed_0 {
    pub key: *const i8,
    pub otl_tag: *const i8,
    pub suffixes: [*const i8; 16],
}
/* quasi-hack to get the primary input */
/* tectonic/core-strutils.h: miscellaneous C string utilities
   Copyright 2016-2018 the Tectonic Project
   Licensed under the MIT License.
*/
/* Note that we explicitly do *not* change this on Windows. For maximum
 * portability, we should probably accept *either* forward or backward slashes
 * as directory separators. */
static mut verbose: i32 = 0i32;
#[no_mangle]
pub unsafe extern "C" fn agl_set_verbose(mut level: i32) {
    verbose = level;
}
unsafe extern "C" fn agl_new_name() -> *mut agl_name {
    let agln =
        new((1_u64).wrapping_mul(::std::mem::size_of::<agl_name>() as u64) as u32) as *mut agl_name;
    (*agln).name = 0 as *mut i8;
    (*agln).suffix = 0 as *mut i8;
    (*agln).n_components = 0i32;
    (*agln).alternate = 0 as *mut agl_name;
    (*agln).is_predef = 0i32;
    agln
}
unsafe extern "C" fn agl_release_name(mut agln: *mut agl_name) {
    while !agln.is_null() {
        let next = (*agln).alternate;
        free((*agln).name as *mut libc::c_void);
        free((*agln).suffix as *mut libc::c_void);
        (*agln).name = 0 as *mut i8;
        free(agln as *mut libc::c_void);
        agln = next
    }
}
#[no_mangle]
pub unsafe extern "C" fn agl_chop_suffix(
    mut glyphname: *const i8,
    mut suffix: *mut *mut i8,
) -> *mut i8 {
    let mut name;
    assert!(!glyphname.is_null() && !suffix.is_null());
    let mut p = strchr(glyphname, '.' as i32);
    if !p.is_null() {
        let len = strlen(glyphname).wrapping_sub(strlen(p)) as i32;
        if len < 1i32 {
            name = 0 as *mut i8;
            *suffix = new((strlen(glyphname) as u32 as u64)
                .wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32)
                as *mut i8;
            strcpy(*suffix, glyphname.offset(1));
        } else {
            p = p.offset(1);
            name = new(
                ((len + 1i32) as u32 as u64).wrapping_mul(::std::mem::size_of::<i8>() as u64)
                    as u32,
            ) as *mut i8;
            strncpy(name, glyphname, len as _);
            *name.offset(len as isize) = '\u{0}' as i32 as i8;
            if *p.offset(0) as i32 == '\u{0}' as i32 {
                *suffix = 0 as *mut i8
            } else {
                *suffix =
                    new((strlen(p).wrapping_add(1)).wrapping_mul(::std::mem::size_of::<i8>()) as _)
                        as *mut i8;
                strcpy(*suffix, p);
            }
        }
    } else {
        name =
            new((strlen(glyphname).wrapping_add(1)).wrapping_mul(::std::mem::size_of::<i8>()) as _)
                as *mut i8;
        strcpy(name, glyphname);
        *suffix = 0 as *mut i8
    }
    name
}
static mut modifiers: [*const i8; 21] = [
    b"acute\x00" as *const u8 as *const i8,
    b"breve\x00" as *const u8 as *const i8,
    b"caron\x00" as *const u8 as *const i8,
    b"cedilla\x00" as *const u8 as *const i8,
    b"circumflex\x00" as *const u8 as *const i8,
    b"dieresis\x00" as *const u8 as *const i8,
    b"dotaccent\x00" as *const u8 as *const i8,
    b"grave\x00" as *const u8 as *const i8,
    b"hungarumlaut\x00" as *const u8 as *const i8,
    b"macron\x00" as *const u8 as *const i8,
    b"ogonek\x00" as *const u8 as *const i8,
    b"ring\x00" as *const u8 as *const i8,
    b"tilde\x00" as *const u8 as *const i8,
    b"commaaccent\x00" as *const u8 as *const i8,
    b"slash\x00" as *const u8 as *const i8,
    b"ampersand\x00" as *const u8 as *const i8,
    b"exclam\x00" as *const u8 as *const i8,
    b"exclamdown\x00" as *const u8 as *const i8,
    b"question\x00" as *const u8 as *const i8,
    b"questiondown\x00" as *const u8 as *const i8,
    0 as *const i8,
];
unsafe extern "C" fn skip_capital(mut p: *mut *const i8, mut endptr: *const i8) -> i32 {
    let len = endptr.wrapping_offset_from(*p) as i32;
    if len >= 2i32
        && (**p as i32 == 'A' as i32 && *(*p).offset(1) as i32 == 'E' as i32
            || **p as i32 == 'O' as i32 && *(*p).offset(1) as i32 == 'E' as i32)
    {
        *p = (*p).offset(2);
        2
    } else if len >= 3i32
        && **p as i32 == 'E' as i32
        && *(*p).offset(1) as i32 == 't' as i32
        && *(*p).offset(2) as i32 == 'h' as i32
    {
        *p = (*p).offset(3);
        3
    } else if len >= 5i32
        && **p as i32 == 'T' as i32
        && *(*p).offset(1) as i32 == 'h' as i32
        && *(*p).offset(2) as i32 == 'o' as i32
        && *(*p).offset(3) as i32 == 'r' as i32
        && *(*p).offset(4) as i32 == 'n' as i32
    {
        *p = (*p).offset(5);
        5
    } else if len >= 1i32 && **p as i32 >= 'A' as i32 && **p as i32 <= 'Z' as i32 {
        *p = (*p).offset(1);
        1
    } else {
        0
    }
}
unsafe extern "C" fn skip_modifier(mut p: *mut *const i8, mut endptr: *const i8) -> size_t {
    let mut slen: size_t = 0i32 as size_t;
    let len = endptr.wrapping_offset_from(*p) as usize;
    let mut i = 0;
    while !modifiers[i].is_null() {
        if len >= strlen(modifiers[i])
            && memcmp(
                *p as *const libc::c_void,
                modifiers[i] as *const libc::c_void,
                len,
            ) == 0
        {
            slen = strlen(modifiers[i]) as _;
            *p = (*p).offset(slen as isize);
            break;
        } else {
            i += 1;
        }
    }
    slen
}
unsafe extern "C" fn is_smallcap(mut glyphname: *const i8) -> bool {
    if glyphname.is_null() {
        return false;
    }
    let mut p = glyphname as *const i8;
    let len = strlen(glyphname);
    if len < 6
        || strcmp(
            p.offset(len as isize).offset(-5),
            b"small\x00" as *const u8 as *const i8,
        ) != 0
    {
        return false;
    }
    let endptr = p.offset(len as isize).offset(-5) as *const i8;
    let len = len.wrapping_sub(5);
    let mut slen = skip_modifier(&mut p, endptr);
    if slen == len as _ {
        return true;
    } else {
        if slen > 0i32 as u64 {
            /* ??? */
            return false;
        }
    }
    let mut len = len.wrapping_sub(skip_capital(&mut p, endptr) as _) as usize;
    if len == 0 {
        return true;
        /* Asmall, AEsmall, etc */
    }
    while len > 0 {
        /* allow multiple accent */
        slen = skip_modifier(&mut p, endptr);
        if slen == 0i32 as u64 {
            return false;
        }
        len = len.wrapping_sub(slen as _)
    }
    true
}
static mut var_list: [C2RustUnnamed_0; 14] = [
    {
        let mut init = C2RustUnnamed_0 {
            key: b"small\x00" as *const u8 as *const i8,
            otl_tag: b"smcp\x00" as *const u8 as *const i8,
            suffixes: [
                b"sc\x00" as *const u8 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"swash\x00" as *const u8 as *const i8,
            otl_tag: b"swsh\x00" as *const u8 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"superior\x00" as *const u8 as *const i8,
            otl_tag: b"sups\x00" as *const u8 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"inferior\x00" as *const u8 as *const i8,
            otl_tag: b"sinf\x00" as *const u8 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"numerator\x00" as *const u8 as *const i8,
            otl_tag: b"numr\x00" as *const u8 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"denominator\x00" as *const u8 as *const i8,
            otl_tag: b"dnom\x00" as *const u8 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"oldstyle\x00" as *const u8 as *const i8,
            otl_tag: b"onum\x00" as *const u8 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"display\x00" as *const u8 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"text\x00" as *const u8 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"big\x00" as *const u8 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"bigg\x00" as *const u8 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"Big\x00" as *const u8 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: b"Bigg\x00" as *const u8 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
    {
        let mut init = C2RustUnnamed_0 {
            key: 0 as *const i8,
            otl_tag: 0 as *const i8,
            suffixes: [
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
                0 as *const i8,
            ],
        };
        init
    },
];
#[no_mangle]
pub unsafe extern "C" fn agl_suffix_to_otltag(mut suffix: *const i8) -> *const i8 {
    let mut i = 0;
    while !var_list[i].key.is_null() {
        let mut j = 0;
        while !var_list[i].suffixes[j].is_null() {
            if streq_ptr(suffix, var_list[i].suffixes[j]) {
                return var_list[i].otl_tag;
            }
            j += 1
        }
        if streq_ptr(suffix, var_list[i].key) {
            return var_list[i].otl_tag;
        }
        if !var_list[i].otl_tag.is_null() && streq_ptr(suffix, var_list[i].otl_tag) as i32 != 0 {
            return var_list[i].otl_tag;
        }
        i += 1
    }
    0 as *const i8
}
unsafe extern "C" fn agl_guess_name(mut glyphname: *const i8) -> ssize_t {
    if is_smallcap(glyphname) {
        return 0i32 as ssize_t;
    }
    let len = strlen(glyphname);
    let mut i = 1;
    while !var_list[i].key.is_null() {
        if len > strlen(var_list[i].key)
            && streq_ptr(
                glyphname
                    .offset(len as isize)
                    .offset(-(strlen(var_list[i].key) as isize)),
                var_list[i].key,
            ) as i32
                != 0
        {
            return i as ssize_t;
        }
        i += 1
    }
    -1 as ssize_t
}
unsafe extern "C" fn agl_normalized_name(mut glyphname: *mut i8) -> *mut agl_name {
    if glyphname.is_null() {
        return 0 as *mut agl_name;
    }
    let agln = agl_new_name();
    let suffix = strchr(glyphname, '.' as i32);
    if !suffix.is_null() {
        let n = strlen(glyphname).wrapping_sub(strlen(suffix)) as i32;
        if *suffix.offset(1) as i32 != '\u{0}' as i32 {
            (*agln).suffix = new((strlen(suffix) as u32 as u64)
                .wrapping_mul(::std::mem::size_of::<i8>() as u64)
                as u32) as *mut i8;
            strcpy((*agln).suffix, suffix.offset(1));
        }
        (*agln).name =
            new(((n + 1i32) as u32 as u64).wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32)
                as *mut i8;
        memcpy(
            (*agln).name as *mut libc::c_void,
            glyphname as *const libc::c_void,
            n as _,
        );
        *(*agln).name.offset(n as isize) = '\u{0}' as i32 as i8
    } else if is_smallcap(glyphname) {
        let n = strlen(glyphname).wrapping_sub(5) as i32;
        (*agln).suffix =
            new((3_u64).wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32) as *mut i8;
        strcpy((*agln).suffix, b"sc\x00" as *const u8 as *const i8);
        (*agln).name =
            new(((n + 1i32) as u32 as u64).wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32)
                as *mut i8;
        for i in 0..n {
            *(*agln).name.offset(i as isize) =
                (if libc::isupper(*glyphname.offset(i as isize) as _) != 0 {
                    *glyphname.offset(i as isize) as i32 + 32i32
                } else {
                    *glyphname.offset(i as isize) as i32
                }) as i8;
        }
        *(*agln).name.offset(n as isize) = '\u{0}' as i32 as i8
    } else {
        let var_idx = agl_guess_name(glyphname);
        let n;
        if var_idx < 0i32 as i64 || var_list[var_idx as usize].key.is_null() {
            n = strlen(glyphname) as i32
        } else {
            n = strlen(glyphname).wrapping_sub(strlen(var_list[var_idx as usize].key)) as i32;
            if !var_list[var_idx as usize].suffixes[0].is_null() {
                (*agln).suffix = new((strlen(var_list[var_idx as usize].suffixes[0])
                    .wrapping_add(1))
                .wrapping_mul(::std::mem::size_of::<i8>())
                    as _) as *mut i8;
                strcpy((*agln).suffix, var_list[var_idx as usize].suffixes[0]);
            } else {
                (*agln).suffix = new((strlen(var_list[var_idx as usize].key).wrapping_add(1))
                    .wrapping_mul(::std::mem::size_of::<i8>())
                    as _) as *mut i8;
                strcpy((*agln).suffix, var_list[var_idx as usize].key);
            }
        }
        (*agln).name =
            new(((n + 1i32) as u32 as u64).wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32)
                as *mut i8;
        memcpy(
            (*agln).name as *mut libc::c_void,
            glyphname as *const libc::c_void,
            n as _,
        );
        *(*agln).name.offset(n as isize) = '\u{0}' as i32 as i8
    }
    agln
}
static mut aglmap: ht_table = ht_table {
    count: 0,
    hval_free_fn: None,
    table: [0 as *const ht_entry as *mut ht_entry; 503],
};
#[inline]
unsafe extern "C" fn hval_free(mut hval: *mut libc::c_void) {
    agl_release_name(hval as *mut agl_name);
}
#[no_mangle]
pub unsafe extern "C" fn agl_init_map() {
    ht_init_table(
        &mut aglmap,
        Some(hval_free as unsafe extern "C" fn(_: *mut libc::c_void) -> ()),
    );
    agl_load_listfile(b"texglyphlist.txt\x00" as *const u8 as *const i8, 0i32);
    if agl_load_listfile(b"pdfglyphlist.txt\x00" as *const u8 as *const i8, 1i32) < 0i32 {
        warn!("Failed to load AGL file \"{}\"...", "pdfglyphlist.txt");
    }
    if agl_load_listfile(b"glyphlist.txt\x00" as *const u8 as *const i8, 0i32) < 0i32 {
        warn!("Failed to load AGL file \"{}\"...", "glyphlist.txt");
    };
}
#[no_mangle]
pub unsafe extern "C" fn agl_close_map() {
    ht_clear_table(&mut aglmap);
}
/*
 * References:
 *
 *  Unicode and Glyph Names, ver. 2.3., Adobe Solution Network
 *  http://partners.adobe.com/asn/tech/type/unicodegn.jsp
 */
/* Hash */
unsafe extern "C" fn agl_load_listfile(mut filename: *const i8, mut is_predef: i32) -> i32 {
    let mut count: i32 = 0i32;
    let mut wbuf: [i8; 1024] = [0; 1024];
    if filename.is_null() {
        return -1i32;
    }
    let handle = dpx_tt_open(
        filename,
        b".txt\x00" as *const u8 as *const i8,
        TTInputFormat::FONTMAP,
    );
    if handle.is_null() {
        return -1i32;
    }
    if verbose != 0 {
        info!("<AGL:{}", CStr::from_ptr(filename).display());
    }
    loop {
        let mut p = tt_mfgets(wbuf.as_mut_ptr(), 1024i32, handle) as *const i8;
        if p.is_null() {
            break;
        }
        let mut unicodes: [i32; 16] = [0; 16];
        let endptr = p.offset(strlen(p) as isize);
        skip_white(&mut p, endptr);
        /* Need table version check. */
        if p.is_null() || *p.offset(0) as i32 == '#' as i32 || p >= endptr {
            continue;
        }
        let mut nextptr = strchr(p, ';' as i32) as *mut i8;
        if nextptr.is_null() || nextptr == p as *mut i8 {
            continue;
        }
        let name = parse_ident(&mut p, nextptr);
        skip_white(&mut p, endptr);
        if name.is_null() || *p.offset(0) as i32 != ';' as i32 {
            warn!(
                "Invalid AGL entry: {}",
                CStr::from_ptr(wbuf.as_ptr()).display()
            );
            free(name as *mut libc::c_void);
        } else {
            p = p.offset(1);
            skip_white(&mut p, endptr);
            let mut n_unicodes = 0i32;
            while p < endptr
                && (*p.offset(0) as i32 >= '0' as i32 && *p.offset(0) as i32 <= '9' as i32
                    || *p.offset(0) as i32 >= 'A' as i32 && *p.offset(0) as i32 <= 'F' as i32)
            {
                if n_unicodes >= 16i32 {
                    warn!("Too many Unicode values");
                    break;
                } else {
                    let fresh0 = n_unicodes;
                    n_unicodes += 1;
                    unicodes[fresh0 as usize] = strtol(p, &mut nextptr, 16i32) as i32;
                    p = nextptr;
                    skip_white(&mut p, endptr);
                }
            }
            if n_unicodes == 0i32 {
                warn!(
                    "AGL entry ignored (no mapping): {}",
                    CStr::from_ptr(wbuf.as_ptr()).display(),
                );
                free(name as *mut libc::c_void);
            } else {
                let agln = agl_normalized_name(name);
                (*agln).is_predef = is_predef;
                (*agln).n_components = n_unicodes;
                for i in 0..n_unicodes as usize {
                    (*agln).unicodes[i] = unicodes[i];
                }
                let mut duplicate = ht_lookup_table(
                    &mut aglmap,
                    name as *const libc::c_void,
                    strlen(name) as i32,
                ) as *mut agl_name;
                if duplicate.is_null() {
                    ht_append_table(
                        &mut aglmap,
                        name as *const libc::c_void,
                        strlen(name) as i32,
                        agln as *mut libc::c_void,
                    );
                } else {
                    while !(*duplicate).alternate.is_null() {
                        duplicate = (*duplicate).alternate
                    }
                    (*duplicate).alternate = agln
                }
                if verbose > 3i32 {
                    if !(*agln).suffix.is_null() {
                        info!(
                            "agl: {} [{}.{}] -->",
                            CStr::from_ptr(name).display(),
                            CStr::from_ptr((*agln).name).display(),
                            CStr::from_ptr((*agln).suffix).display(),
                        );
                    } else {
                        info!(
                            "agl: {} [{}] -->",
                            CStr::from_ptr(name).display(),
                            CStr::from_ptr((*agln).name).display(),
                        );
                    }
                    for i in 0..(*agln).n_components as usize {
                        if (*agln).unicodes[i] > 0xffffi32 {
                            info!(" U+{:06X}", (*agln).unicodes[i],);
                        } else {
                            info!(" U+{:04X}", (*agln).unicodes[i],);
                        }
                    }
                    info!("\n");
                }
                free(name as *mut libc::c_void);
                count += 1
            }
        }
    }
    ttstub_input_close(handle);
    if verbose != 0 {
        info!(">");
    }
    count
}
#[no_mangle]
pub unsafe extern "C" fn agl_lookup_list(mut glyphname: *const i8) -> *mut agl_name {
    if glyphname.is_null() {
        return 0 as *mut agl_name;
    }
    ht_lookup_table(
        &mut aglmap,
        glyphname as *const libc::c_void,
        strlen(glyphname) as i32,
    ) as *mut agl_name
}
#[no_mangle]
pub unsafe extern "C" fn agl_name_is_unicode(mut glyphname: *const i8) -> bool {
    if glyphname.is_null() {
        return false;
    }
    let suffix = strchr(glyphname, '.' as i32);
    let len = if !suffix.is_null() {
        suffix.wrapping_offset_from(glyphname) as i64 as size_t
    } else {
        strlen(glyphname) as _
    };
    /*
     * uni02ac is invalid glyph name and mapped to th empty string.
     */
    if len >= 7i32 as u64
        && len.wrapping_sub(3i32 as u64).wrapping_rem(4i32 as u64) == 0i32 as u64
        && !strstartswith(glyphname, b"uni\x00" as *const u8 as *const i8).is_null()
    {
        let c = *glyphname.offset(3);
        /*
         * Check if the 4th character is uppercase hexadecimal digit.
         * "union" should not be treated as Unicode glyph name.
         */
        if libc::isdigit(c as _) != 0 || c as i32 >= 'A' as i32 && c as i32 <= 'F' as i32 {
            return true;
        } else {
            return false;
        }
    } else {
        if len <= 7i32 as u64 && len >= 5i32 as u64 && *glyphname.offset(0) as i32 == 'u' as i32 {
            for i in 1..len - 1 {
                let c = *glyphname.offset(i as isize);
                if libc::isdigit(c as _) == 0 && ((c as i32) < 'A' as i32 || c as i32 > 'F' as i32)
                {
                    return false;
                }
            }
            return true;
        }
    }
    false
}
#[no_mangle]
pub unsafe extern "C" fn agl_name_convert_unicode(mut glyphname: *const i8) -> i32 {
    if !agl_name_is_unicode(glyphname) {
        return -1i32;
    }
    if strlen(glyphname) > 7 && *glyphname.offset(7) as i32 != '.' as i32 {
        warn!("Mapping to multiple Unicode characters not supported.");
        return -1i32;
    }
    let mut p = if *glyphname.offset(1) as i32 == 'n' as i32 {
        glyphname.offset(3)
    } else {
        glyphname.offset(1)
    };
    let mut ucv = 0;
    while *p as i32 != '\u{0}' as i32 && *p as i32 != '.' as i32 {
        if libc::isdigit(*p as _) == 0 && ((*p as i32) < 'A' as i32 || *p as i32 > 'F' as i32) {
            warn!(
                "Invalid char {} in Unicode glyph name {}.",
                char::from(*p as u8),
                CStr::from_ptr(glyphname).display(),
            );
            return -1i32;
        }
        ucv <<= 4i32;
        ucv += if libc::isdigit(*p as _) != 0 {
            *p as i32 - '0' as i32
        } else {
            *p as i32 - 'A' as i32 + 10i32
        };
        p = p.offset(1)
    }
    if !UC_is_valid(ucv) {
        if ucv < 0x10000i32 {
            warn!("Invalid Unicode code value U+{:04X}.", ucv,);
        } else {
            warn!("Invalid Unicode code value U+{:06X}.", ucv,);
        }
        ucv = -1i32
    }
    ucv
}
unsafe extern "C" fn xtol(mut start: *const i8, mut len: i32) -> i32 {
    let mut v: i32 = 0i32;
    loop {
        let fresh1 = len;
        len = len - 1;
        if !(fresh1 > 0i32) {
            break;
        }
        v <<= 4i32;
        if libc::isdigit(*start as _) != 0 {
            v += *start as i32 - '0' as i32
        } else if *start as i32 >= 'A' as i32 && *start as i32 <= 'F' as i32 {
            v += *start as i32 - 'A' as i32 + 10i32
        } else {
            return -1i32;
        }
        start = start.offset(1)
    }
    v
}
unsafe extern "C" fn put_unicode_glyph(
    mut name: *const i8,
    mut dstpp: *mut *mut u8,
    mut limptr: *mut u8,
) -> i32 {
    let mut len = 0;
    let mut p = name;
    if *p.offset(1) as i32 != 'n' as i32 {
        p = p.offset(1);
        let ucv = xtol(p, strlen(p) as i32);
        len = (len as u64).wrapping_add(UC_UTF16BE_encode_char(ucv, dstpp, limptr)) as i32 as i32
    } else {
        p = p.offset(3);
        while *p as i32 != '\u{0}' as i32 {
            let ucv = xtol(p, 4i32);
            len =
                (len as u64).wrapping_add(UC_UTF16BE_encode_char(ucv, dstpp, limptr)) as i32 as i32;
            p = p.offset(4)
        }
    }
    len
}
#[no_mangle]
pub unsafe extern "C" fn agl_sput_UTF16BE(
    mut glyphstr: *const i8,
    mut dstpp: *mut *mut u8,
    mut limptr: *mut u8,
    mut fail_count: *mut i32,
) -> i32 {
    let mut len: i32 = 0i32;
    let mut count: i32 = 0i32;
    assert!(!glyphstr.is_null() && !dstpp.is_null());
    let mut p = glyphstr;
    let mut endptr = strchr(p, '.' as i32) as *const i8;
    if endptr.is_null() {
        endptr = p.offset(strlen(p) as isize)
    }
    while p < endptr {
        let mut delim = strchr(p, '_' as i32) as *const i8;
        if delim == p {
            /*
             * Glyph names starting with a underscore or two subsequent
             * underscore in glyph name not allowed?
             */
            warn!(
                "Invalid glyph name component in \"{}\".",
                CStr::from_ptr(glyphstr).display()
            );
            count += 1;
            if !fail_count.is_null() {
                *fail_count = count
            }
            return len;
        /* Cannot continue */
        } else {
            if delim.is_null() || delim > endptr {
                delim = endptr
            }
        }
        let sub_len = delim.wrapping_offset_from(p) as i64 as i32;
        let name = new(((sub_len + 1i32) as u32 as u64)
            .wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32) as *mut i8;
        memcpy(
            name as *mut libc::c_void,
            p as *const libc::c_void,
            sub_len as _,
        );
        *name.offset(sub_len as isize) = '\u{0}' as i32 as i8;
        if agl_name_is_unicode(name) {
            let sub_len = put_unicode_glyph(name, dstpp, limptr);
            if sub_len > 0i32 {
                len += sub_len
            } else {
                count += 1
            }
        } else {
            let mut agln1 = agl_lookup_list(name);
            if agln1.is_null()
                || (*agln1).n_components == 1i32
                    && ((*agln1).unicodes[0] as i64 >= 0xe000
                        && (*agln1).unicodes[0] as i64 <= 0xf8ff
                        || (*agln1).unicodes[0] as i64 >= 0xf0000
                            && (*agln1).unicodes[0] as i64 <= 0xffffd
                        || (*agln1).unicodes[0] as i64 >= 0x100000
                            && (*agln1).unicodes[0] as i64 <= 0x10fffd)
            {
                let agln0 = agl_normalized_name(name);
                if !agln0.is_null() {
                    if verbose > 1i32 && !(*agln0).suffix.is_null() {
                        warn!(
                            "agl: fix {} --> {}.{}",
                            CStr::from_ptr(name).display(),
                            CStr::from_ptr((*agln0).name).display(),
                            CStr::from_ptr((*agln0).suffix).display(),
                        );
                    }
                    agln1 = agl_lookup_list((*agln0).name);
                    agl_release_name(agln0);
                }
            }
            if !agln1.is_null() {
                for i in 0..(*agln1).n_components as usize {
                    len = (len as u64).wrapping_add(UC_UTF16BE_encode_char(
                        (*agln1).unicodes[i],
                        dstpp,
                        limptr,
                    )) as i32 as i32;
                }
            } else {
                if verbose != 0 {
                    warn!(
                        "No Unicode mapping for glyph name \"{}\" found.",
                        CStr::from_ptr(name).display()
                    )
                }
                count += 1
            }
        }
        free(name as *mut libc::c_void);
        p = delim.offset(1)
    }
    if !fail_count.is_null() {
        *fail_count = count
    }
    len
}
#[no_mangle]
pub unsafe extern "C" fn agl_get_unicodes(
    mut glyphstr: *const i8,
    mut unicodes: *mut i32,
    mut max_unicodes: i32,
) -> i32 {
    let mut count: i32 = 0i32;
    let mut p = glyphstr;
    let mut endptr = strchr(p, '.' as i32) as *const i8;
    if endptr.is_null() {
        endptr = p.offset(strlen(p) as isize)
    }
    while p < endptr {
        let mut delim = strchr(p, '_' as i32) as *const i8;
        if delim == p {
            /*
             * Glyph names starting with a underscore or two subsequent
             * underscore in glyph name not allowed?
             */
            warn!(
                "Invalid glyph name component in \"{}\".",
                CStr::from_ptr(glyphstr).display()
            );
            return -1i32;
        /* Cannot continue */
        } else {
            if delim.is_null() || delim > endptr {
                delim = endptr
            }
        }
        let sub_len = delim.wrapping_offset_from(p) as i32;
        let name = new(((sub_len + 1i32) as u32 as u64)
            .wrapping_mul(::std::mem::size_of::<i8>() as u64) as u32) as *mut i8;
        memcpy(
            name as *mut libc::c_void,
            p as *const libc::c_void,
            sub_len as _,
        );
        *name.offset(sub_len as isize) = '\u{0}' as i32 as i8;
        if agl_name_is_unicode(name) {
            p = name;
            if *p.offset(1) as i32 != 'n' as i32 {
                /* uXXXXXXXX */
                if count >= max_unicodes {
                    free(name as *mut libc::c_void);
                    return -1i32;
                }
                p = p.offset(1);
                let fresh2 = count;
                count = count + 1;
                *unicodes.offset(fresh2 as isize) = xtol(p, strlen(p) as i32)
            } else {
                p = p.offset(3);
                while *p as i32 != '\u{0}' as i32 {
                    if count >= max_unicodes {
                        free(name as *mut libc::c_void);
                        return -1i32;
                    }
                    let fresh3 = count;
                    count = count + 1;
                    *unicodes.offset(fresh3 as isize) = xtol(p, 4i32);
                    p = p.offset(4)
                }
            }
        } else {
            let mut agln1 = agl_lookup_list(name);
            if agln1.is_null()
                || (*agln1).n_components == 1i32
                    && ((*agln1).unicodes[0] as i64 >= 0xe000
                        && (*agln1).unicodes[0] as i64 <= 0xf8ff
                        || (*agln1).unicodes[0] as i64 >= 0xf0000
                            && (*agln1).unicodes[0] as i64 <= 0xffffd
                        || (*agln1).unicodes[0] as i64 >= 0x100000
                            && (*agln1).unicodes[0] as i64 <= 0x10fffd)
            {
                let mut agln0 = agl_normalized_name(name);
                if !agln0.is_null() {
                    if verbose > 1i32 && !(*agln0).suffix.is_null() {
                        warn!(
                            "agl: fix {} --> {}.{}",
                            CStr::from_ptr(name).display(),
                            CStr::from_ptr((*agln0).name).display(),
                            CStr::from_ptr((*agln0).suffix).display(),
                        );
                    }
                    agln1 = agl_lookup_list((*agln0).name);
                    agl_release_name(agln0);
                }
            }
            if !agln1.is_null() {
                if count + (*agln1).n_components > max_unicodes {
                    free(name as *mut libc::c_void);
                    return -1i32;
                }
                for i in 0..(*agln1).n_components {
                    let fresh4 = count;
                    count = count + 1;
                    *unicodes.offset(fresh4 as isize) = (*agln1).unicodes[i as usize];
                }
            } else {
                if verbose > 1i32 {
                    warn!(
                        "No Unicode mapping for glyph name \"{}\" found.",
                        CStr::from_ptr(name).display()
                    )
                }
                free(name as *mut libc::c_void);
                return -1i32;
            }
        }
        free(name as *mut libc::c_void);
        p = delim.offset(1)
    }
    count
}
