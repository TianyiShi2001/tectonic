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
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]

use crate::mfree;
use crate::streq_ptr;
use crate::{info, warn};

use super::dpx_cff::{
    cff_add_string, cff_close, cff_get_seac_sid, cff_glyph_lookup, cff_index_size, cff_new_index,
    cff_pack_charsets, cff_pack_encoding, cff_pack_index, cff_put_header, cff_release_charsets,
    cff_release_index, cff_set_name, cff_update_string, CffIndex, Pack,
};
use super::dpx_cff_dict::{
    cff_dict_add, cff_dict_get, cff_dict_known, cff_dict_pack, cff_dict_set, cff_dict_update,
};
use super::dpx_error::{dpx_message, dpx_warning};
use super::dpx_mem::{new, renew};
use super::dpx_pdfencoding::{pdf_create_ToUnicode_CMap, pdf_encoding_get_encoding};
use super::dpx_pdffont::{
    pdf_font, pdf_font_get_descriptor, pdf_font_get_encoding, pdf_font_get_fontname,
    pdf_font_get_ident, pdf_font_get_mapname, pdf_font_get_resource, pdf_font_get_uniqueTag,
    pdf_font_get_usedchars, pdf_font_get_verbose, pdf_font_is_in_use, pdf_font_set_flags,
    pdf_font_set_fontname, pdf_font_set_subtype,
};
use super::dpx_t1_char::{t1char_convert_charstring, t1char_get_metrics};
use super::dpx_t1_load::{is_pfb, t1_get_fontname, t1_get_standard_glyph, t1_load_font};
use super::dpx_tfm::{tfm_get_width, tfm_open};
use crate::dpx_pdfobj::{
    pdf_add_array, pdf_add_dict, pdf_add_stream, pdf_array_length, pdf_lookup_dict, pdf_new_array,
    pdf_new_name, pdf_new_number, pdf_new_stream, pdf_new_string, pdf_obj, pdf_ref_obj,
    pdf_release_obj, pdf_stream_dataptr, pdf_stream_dict, pdf_stream_length,
};
use crate::{ttstub_input_close, ttstub_input_open};
use bridge::_tt_abort;
use libc::{free, memset, sprintf, strlen, strstr};

pub type size_t = u64;

use crate::TTInputFormat;

pub type rust_input_handle_t = *mut libc::c_void;

use super::dpx_cff::cff_index;
/* quasi-hack to get the primary input */
/* CFF Data Types */
/* SID SID number */
/* offset(0) */
/* size offset(0) */
/* 1-byte unsigned number specifies the size
of an Offset field or fields, range 1-4 */
pub type l_offset = u32;

use super::dpx_cff::cff_font;
/* format major version (starting at 1) */
/* format minor version (starting at 0) */
/* Header size (bytes)                  */
/* Absolute offset (0) size             */
/* Dictionary */
/* encoded data value (as u8 or u16) */
/* opname                                 */
/* number of values                        */
/* values                                  */

use super::dpx_cff::cff_charsets;
/* 1, 2, 3, or 4-byte offset */
pub type s_SID = u16;
use super::dpx_cff::cff_encoding;
use super::dpx_cff::cff_map;
use super::dpx_cff::cff_range1;

use super::dpx_t1_char::t1_ginfo;

/* tectonic/core-strutils.h: miscellaneous C string utilities
   Copyright 2016-2018 the Tectonic Project
   Licensed under the MIT License.
*/
/* Note that we explicitly do *not* change this on Windows. For maximum
 * portability, we should probably accept *either* forward or backward slashes
 * as directory separators. */

/* Force bold at small text sizes */
unsafe extern "C" fn is_basefont(mut name: *const i8) -> bool {
    static mut basefonts: [*const i8; 14] = [
        b"Courier\x00" as *const u8 as *const i8,
        b"Courier-Bold\x00" as *const u8 as *const i8,
        b"Courier-Oblique\x00" as *const u8 as *const i8,
        b"Courier-BoldOblique\x00" as *const u8 as *const i8,
        b"Helvetica\x00" as *const u8 as *const i8,
        b"Helvetica-Bold\x00" as *const u8 as *const i8,
        b"Helvetica-Oblique\x00" as *const u8 as *const i8,
        b"Helvetica-BoldOblique\x00" as *const u8 as *const i8,
        b"Symbol\x00" as *const u8 as *const i8,
        b"Times-Roman\x00" as *const u8 as *const i8,
        b"Times-Bold\x00" as *const u8 as *const i8,
        b"Times-Italic\x00" as *const u8 as *const i8,
        b"Times-BoldItalic\x00" as *const u8 as *const i8,
        b"ZapfDingbats\x00" as *const u8 as *const i8,
    ];
    let mut i: i32 = 0;
    i = 0i32;
    while i < 14i32 {
        if streq_ptr(name, basefonts[i as usize]) {
            return true;
        }
        i += 1
    }
    false
}
#[no_mangle]
pub unsafe extern "C" fn pdf_font_open_type1(mut font: *mut pdf_font) -> i32 {
    let mut ident: *mut i8 = 0 as *mut i8;
    let mut fontname: [i8; 128] = [0; 128];
    assert!(!font.is_null());
    ident = pdf_font_get_ident(font);
    if is_basefont(ident) {
        pdf_font_set_fontname(font, ident);
        pdf_font_set_subtype(font, 0i32);
        pdf_font_set_flags(font, 1i32 << 0i32 | 1i32 << 2i32);
    } else {
        let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
        handle = ttstub_input_open(ident, TTInputFormat::TYPE1, 0i32);
        /* NOTE: skipping qcheck_filetype() call in dpx_find_type1_file but we
         * call is_pfb() in just a second anyway.
         */
        if handle.is_null() {
            return -1i32;
        }
        memset(fontname.as_mut_ptr() as *mut libc::c_void, 0i32, 127 + 1);
        if !is_pfb(handle) || t1_get_fontname(handle, fontname.as_mut_ptr()) < 0i32 {
            _tt_abort(
                b"Failed to read Type 1 font \"%s\".\x00" as *const u8 as *const i8,
                ident,
            );
        }
        ttstub_input_close(handle);
        pdf_font_set_fontname(font, fontname.as_mut_ptr());
        pdf_font_set_subtype(font, 0i32);
    }
    0i32
}
unsafe extern "C" fn get_font_attr(mut font: *mut pdf_font, cffont: &cff_font) {
    let mut fontname: *mut i8 = 0 as *mut i8;
    let mut descriptor: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut capheight: f64 = 0.;
    let mut ascent: f64 = 0.;
    let mut descent: f64 = 0.;
    let mut italicangle: f64 = 0.;
    let mut stemv: f64 = 0.;
    let mut defaultwidth: f64 = 0.;
    let mut nominalwidth: f64 = 0.;
    let mut flags: i32 = 0i32;
    let mut gid: i32 = 0;
    let mut i: i32 = 0;
    static mut L_c: [*const i8; 5] = [
        b"H\x00" as *const u8 as *const i8,
        b"P\x00" as *const u8 as *const i8,
        b"Pi\x00" as *const u8 as *const i8,
        b"Rho\x00" as *const u8 as *const i8,
        0 as *const i8,
    ];
    static mut L_d: [*const i8; 5] = [
        b"p\x00" as *const u8 as *const i8,
        b"q\x00" as *const u8 as *const i8,
        b"mu\x00" as *const u8 as *const i8,
        b"eta\x00" as *const u8 as *const i8,
        0 as *const i8,
    ];
    static mut L_a: [*const i8; 4] = [
        b"b\x00" as *const u8 as *const i8,
        b"h\x00" as *const u8 as *const i8,
        b"lambda\x00" as *const u8 as *const i8,
        0 as *const i8,
    ];
    let mut gm = t1_ginfo::new();
    defaultwidth = 500.0f64;
    nominalwidth = 0.0f64;
    /*
     * CapHeight, Ascent, and Descent is meaningfull only for Latin/Greek/Cyrillic.
     * The BlueValues and OtherBlues also have those information.
     */
    if cff_dict_known(cffont.topdict, b"FontBBox\x00" as *const u8 as *const i8) != 0 {
        /* Default values */
        ascent = cff_dict_get(
            cffont.topdict,
            b"FontBBox\x00" as *const u8 as *const i8,
            3i32,
        );
        capheight = ascent;
        descent = cff_dict_get(
            cffont.topdict,
            b"FontBBox\x00" as *const u8 as *const i8,
            1i32,
        )
    } else {
        capheight = 680.0f64;
        ascent = 690.0f64;
        descent = -190.0f64
    }
    if cff_dict_known(
        *cffont.private.offset(0),
        b"StdVW\x00" as *const u8 as *const i8,
    ) != 0
    {
        stemv = cff_dict_get(
            *cffont.private.offset(0),
            b"StdVW\x00" as *const u8 as *const i8,
            0i32,
        )
    } else {
        /*
         * We may use the following values for StemV:
         *  Thin - ExtraLight: <= 50
         *  Light: 71
         *  Regular(Normal): 88
         *  Medium: 109
         *  SemiBold(DemiBold): 135
         *  Bold - Heavy: >= 166
         */
        stemv = 88.0f64
    }
    if cff_dict_known(cffont.topdict, b"ItalicAngle\x00" as *const u8 as *const i8) != 0 {
        italicangle = cff_dict_get(
            cffont.topdict,
            b"ItalicAngle\x00" as *const u8 as *const i8,
            0i32,
        );
        if italicangle != 0.0f64 {
            flags |= 1i32 << 6i32
        }
    } else {
        italicangle = 0.0f64
    }
    /*
     * Use "space", "H", "p", and "b" for various values.
     * Those characters should not "seac". (no accent)
     */
    gid = cff_glyph_lookup(cffont, b"space\x00" as *const u8 as *const i8) as i32; /* FIXME */
    if gid >= 0i32 && gid < (*cffont.cstrings).count as i32 {
        t1char_get_metrics(
            (*cffont.cstrings)
                .data
                .offset(*(*cffont.cstrings).offset.offset(gid as isize) as isize)
                .offset(-1),
            (*(*cffont.cstrings).offset.offset((gid + 1i32) as isize))
                .wrapping_sub(*(*cffont.cstrings).offset.offset(gid as isize)) as i32,
            *cffont.subrs.offset(0),
            &mut gm,
        );
        defaultwidth = gm.wx
    }
    i = 0i32;
    while !L_c[i as usize].is_null() {
        gid = cff_glyph_lookup(cffont, L_c[i as usize]) as i32;
        if gid >= 0i32 && gid < (*cffont.cstrings).count as i32 {
            t1char_get_metrics(
                (*cffont.cstrings)
                    .data
                    .offset(*(*cffont.cstrings).offset.offset(gid as isize) as isize)
                    .offset(-1),
                (*(*cffont.cstrings).offset.offset((gid + 1i32) as isize))
                    .wrapping_sub(*(*cffont.cstrings).offset.offset(gid as isize))
                    as i32,
                *cffont.subrs.offset(0),
                &mut gm,
            );
            capheight = gm.bbox.ury;
            break;
        } else {
            i += 1
        }
    }
    i = 0i32;
    while !L_d[i as usize].is_null() {
        gid = cff_glyph_lookup(cffont, L_d[i as usize]) as i32;
        if gid >= 0i32 && gid < (*cffont.cstrings).count as i32 {
            t1char_get_metrics(
                (*cffont.cstrings)
                    .data
                    .offset(*(*cffont.cstrings).offset.offset(gid as isize) as isize)
                    .offset(-1),
                (*(*cffont.cstrings).offset.offset((gid + 1i32) as isize))
                    .wrapping_sub(*(*cffont.cstrings).offset.offset(gid as isize))
                    as i32,
                *cffont.subrs.offset(0),
                &mut gm,
            );
            descent = gm.bbox.lly;
            break;
        } else {
            i += 1
        }
    }
    i = 0i32;
    while !L_a[i as usize].is_null() {
        gid = cff_glyph_lookup(cffont, L_a[i as usize]) as i32;
        if gid >= 0i32 && gid < (*cffont.cstrings).count as i32 {
            t1char_get_metrics(
                (*cffont.cstrings)
                    .data
                    .offset(*(*cffont.cstrings).offset.offset(gid as isize) as isize)
                    .offset(-1),
                (*(*cffont.cstrings).offset.offset((gid + 1i32) as isize))
                    .wrapping_sub(*(*cffont.cstrings).offset.offset(gid as isize))
                    as i32,
                *cffont.subrs.offset(0),
                &mut gm,
            );
            ascent = gm.bbox.ury;
            break;
        } else {
            i += 1
        }
    }
    if defaultwidth != 0.0f64 {
        cff_dict_add(
            *cffont.private.offset(0),
            b"defaultWidthX\x00" as *const u8 as *const i8,
            1i32,
        );
        cff_dict_set(
            *cffont.private.offset(0),
            b"defaultWidthX\x00" as *const u8 as *const i8,
            0i32,
            defaultwidth,
        );
    }
    if nominalwidth != 0.0f64 {
        cff_dict_add(
            *cffont.private.offset(0),
            b"nominalWidthX\x00" as *const u8 as *const i8,
            1i32,
        );
        cff_dict_set(
            *cffont.private.offset(0),
            b"nominalWidthX\x00" as *const u8 as *const i8,
            0i32,
            nominalwidth,
        );
    }
    if cff_dict_known(
        *cffont.private.offset(0),
        b"ForceBold\x00" as *const u8 as *const i8,
    ) != 0
        && cff_dict_get(
            *cffont.private.offset(0),
            b"ForceBold\x00" as *const u8 as *const i8,
            0i32,
        ) != 0.
    {
        flags |= 1i32 << 18i32
    }
    if cff_dict_known(
        *cffont.private.offset(0),
        b"IsFixedPitch\x00" as *const u8 as *const i8,
    ) != 0
        && cff_dict_get(
            *cffont.private.offset(0),
            b"IsFixedPitch\x00" as *const u8 as *const i8,
            0i32,
        ) != 0.
    {
        flags |= 1i32 << 0i32
    }
    fontname = pdf_font_get_fontname(font);
    descriptor = pdf_font_get_descriptor(font);
    if !fontname.is_null() && strstr(fontname, b"Sans\x00" as *const u8 as *const i8).is_null() {
        flags |= 1i32 << 1i32
    }
    if !fontname.is_null() && !strstr(fontname, b"Caps\x00" as *const u8 as *const i8).is_null() {
        flags |= 1i32 << 17i32
    }
    flags |= 1i32 << 2i32;
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"CapHeight\x00" as *const u8 as *const i8),
        pdf_new_number(capheight),
    );
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"Ascent\x00" as *const u8 as *const i8),
        pdf_new_number(ascent),
    );
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"Descent\x00" as *const u8 as *const i8),
        pdf_new_number(descent),
    );
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"ItalicAngle\x00" as *const u8 as *const i8),
        pdf_new_number(italicangle),
    );
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"StemV\x00" as *const u8 as *const i8),
        pdf_new_number(stemv),
    );
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"Flags\x00" as *const u8 as *const i8),
        pdf_new_number(flags as f64),
    );
}
unsafe extern "C" fn add_metrics(
    mut font: *mut pdf_font,
    cffont: &cff_font,
    mut enc_vec: *mut *mut i8,
    mut widths: *mut f64,
    mut num_glyphs: i32,
) {
    let mut fontdict: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut descriptor: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut tmp_array: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut code: i32 = 0;
    let mut firstchar: i32 = 0;
    let mut lastchar: i32 = 0;
    let mut val: f64 = 0.;
    let mut i: i32 = 0;
    let mut tfm_id: i32 = 0;
    let mut usedchars: *mut i8 = 0 as *mut i8;
    let mut scaling: f64 = 0.;
    fontdict = pdf_font_get_resource(font);
    descriptor = pdf_font_get_descriptor(font);
    usedchars = pdf_font_get_usedchars(font);
    /*
     * The original FontBBox of the font is preserved, instead
     * of replacing it with tight bounding box calculated from
     * charstrings, to prevent Acrobat 4 from greeking text as
     * much as possible.
     */
    if cff_dict_known(cffont.topdict, b"FontBBox\x00" as *const u8 as *const i8) == 0 {
        panic!("No FontBBox?");
    }
    /* The widhts array in the font dictionary must be given relative
     * to the default scaling of 1000:1, not relative to the scaling
     * given by the font matrix.
     */
    if cff_dict_known(cffont.topdict, b"FontMatrix\x00" as *const u8 as *const i8) != 0 {
        scaling = 1000i32 as f64
            * cff_dict_get(
                cffont.topdict,
                b"FontMatrix\x00" as *const u8 as *const i8,
                0i32,
            )
    } else {
        scaling = 1i32 as f64
    }
    tmp_array = pdf_new_array();
    i = 0i32;
    while i < 4i32 {
        val = cff_dict_get(cffont.topdict, b"FontBBox\x00" as *const u8 as *const i8, i);
        pdf_add_array(
            tmp_array,
            pdf_new_number((val / 1.0f64 + 0.5f64).floor() * 1.0f64),
        );
        i += 1
    }
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"FontBBox\x00" as *const u8 as *const i8),
        tmp_array,
    );
    tmp_array = pdf_new_array();
    if num_glyphs <= 1i32 {
        /* This must be an error. */
        lastchar = 0i32;
        firstchar = lastchar;
        pdf_add_array(tmp_array, pdf_new_number(0.0f64));
    } else {
        firstchar = 255i32;
        lastchar = 0i32;
        code = 0i32;
        while code < 256i32 {
            if *usedchars.offset(code as isize) != 0 {
                if code < firstchar {
                    firstchar = code
                }
                if code > lastchar {
                    lastchar = code
                }
            }
            code += 1
        }
        if firstchar > lastchar {
            warn!("No glyphs actually used???");
            pdf_release_obj(tmp_array);
            return;
        }
        /* PLEASE FIX THIS
         * It's wrong to use TFM width here... We should warn if TFM width
         * and actual glyph width are different.
         */
        tfm_id = tfm_open(pdf_font_get_mapname(font), 0i32);
        code = firstchar;
        while code <= lastchar {
            if *usedchars.offset(code as isize) != 0 {
                let mut width: f64 = 0.;
                if tfm_id < 0i32 {
                    /* tfm is not found */
                    width = scaling
                        * *widths.offset(
                            cff_glyph_lookup(cffont, *enc_vec.offset(code as isize)) as isize
                        )
                } else {
                    let mut diff: f64 = 0.;
                    width = 1000.0f64 * tfm_get_width(tfm_id, code);
                    diff = width
                        - scaling
                            * *widths
                                .offset(cff_glyph_lookup(cffont, *enc_vec.offset(code as isize))
                                    as isize);
                    if diff.abs() > 1.0f64 {
                        dpx_warning(
                            b"Glyph width mismatch for TFM and font (%s)\x00" as *const u8
                                as *const i8,
                            pdf_font_get_mapname(font),
                        );
                        warn!(
                            "TFM: {} vs. Type1 font: {}",
                            width,
                            *widths
                                .offset(cff_glyph_lookup(cffont, *enc_vec.offset(code as isize))
                                    as isize),
                        );
                    }
                }
                pdf_add_array(
                    tmp_array,
                    pdf_new_number((width / 0.1f64 + 0.5f64).floor() * 0.1f64),
                );
            } else {
                pdf_add_array(tmp_array, pdf_new_number(0.0f64));
            }
            code += 1
        }
    }
    if pdf_array_length(tmp_array) > 0_u32 {
        pdf_add_dict(
            fontdict,
            pdf_new_name(b"Widths\x00" as *const u8 as *const i8),
            pdf_ref_obj(tmp_array),
        );
    }
    pdf_release_obj(tmp_array);
    pdf_add_dict(
        fontdict,
        pdf_new_name(b"FirstChar\x00" as *const u8 as *const i8),
        pdf_new_number(firstchar as f64),
    );
    pdf_add_dict(
        fontdict,
        pdf_new_name(b"LastChar\x00" as *const u8 as *const i8),
        pdf_new_number(lastchar as f64),
    );
}
unsafe extern "C" fn write_fontfile(
    mut font: *mut pdf_font,
    cffont: &cff_font,
    mut pdfcharset: *mut pdf_obj,
) -> i32 {
    let mut descriptor: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut fontfile: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut stream_dict: *mut pdf_obj = 0 as *mut pdf_obj;
    let mut wbuf: [u8; 1024] = [0; 1024];
    descriptor = pdf_font_get_descriptor(font);
    let mut topdict = CffIndex::new(1);

    /*
     * Force existence of Encoding.
     */
    if cff_dict_known(cffont.topdict, b"CharStrings\x00" as *const u8 as *const i8) == 0 {
        cff_dict_add(
            cffont.topdict,
            b"CharStrings\x00" as *const u8 as *const i8,
            1i32,
        );
    }
    if cff_dict_known(cffont.topdict, b"charset\x00" as *const u8 as *const i8) == 0 {
        cff_dict_add(
            cffont.topdict,
            b"charset\x00" as *const u8 as *const i8,
            1i32,
        );
    }
    if cff_dict_known(cffont.topdict, b"Encoding\x00" as *const u8 as *const i8) == 0 {
        cff_dict_add(
            cffont.topdict,
            b"Encoding\x00" as *const u8 as *const i8,
            1i32,
        );
    }
    let mut private_size = cff_dict_pack(*cffont.private.offset(0), &mut wbuf[..]);
    /* Private dict is required (but may have size 0) */
    if cff_dict_known(cffont.topdict, b"Private\x00" as *const u8 as *const i8) == 0 {
        cff_dict_add(
            cffont.topdict,
            b"Private\x00" as *const u8 as *const i8,
            2i32,
        );
    }
    topdict.offset[1] = (cff_dict_pack(cffont.topdict, &mut wbuf[..]) + 1) as l_offset;
    /*
     * Estimate total size of fontfile.
     */
    let charstring_len = cff_index_size(cffont.cstrings); /* header size */
    let mut stream_data_len = 4_usize;
    stream_data_len += cff_index_size(cffont.name);
    stream_data_len += topdict.size();
    stream_data_len += cff_index_size(cffont.string);
    stream_data_len += cff_index_size(cffont.gsubr);
    /* We are using format 1 for Encoding and format 0 for charset.
     * TODO: Should implement cff_xxx_size().
     */
    stream_data_len += 2
        + (*cffont.encoding).num_entries as usize * 2
        + 1
        + (*cffont.encoding).num_supps as usize * 3;
    stream_data_len += 1 + (*cffont.charsets).num_entries as usize * 2;
    stream_data_len += charstring_len;
    stream_data_len += private_size;
    /*
     * Now we create FontFile data.
     */
    let mut stream_data = vec![0u8; stream_data_len];
    /*
     * Data Layout order as described in CFF spec., sec 2 "Data Layout".
     */
    let mut offset = 0_usize;
    /* Header */
    offset += cff_put_header(cffont, &mut stream_data[offset..]);
    /* Name */
    offset += cff_pack_index(cffont.name, &mut stream_data[offset..]);
    /* Top DICT */
    let topdict_offset = offset;
    offset += topdict.size();
    /* Strings */
    offset += cff_pack_index(cffont.string, &mut stream_data[offset..]);
    /* Global Subrs */
    offset += cff_pack_index(cffont.gsubr, &mut stream_data[offset..]);
    /* Encoding */
    /* TODO: don't write Encoding entry if the font is always used
     * with PDF Encoding information. Applies to type1c.c as well.
     */
    cff_dict_set(
        cffont.topdict,
        b"Encoding\x00" as *const u8 as *const i8,
        0i32,
        offset as f64,
    );
    offset += cff_pack_encoding(cffont, &mut stream_data[offset..]);
    /* charset */
    cff_dict_set(
        cffont.topdict,
        b"charset\x00" as *const u8 as *const i8,
        0i32,
        offset as f64,
    );
    offset += cff_pack_charsets(cffont, &mut stream_data[offset..]);
    /* CharStrings */
    cff_dict_set(
        cffont.topdict,
        b"CharStrings\x00" as *const u8 as *const i8,
        0i32,
        offset as f64,
    );
    offset += cff_pack_index(
        cffont.cstrings,
        &mut stream_data[offset..offset + charstring_len],
    );
    /* Private */
    if !(*cffont.private.offset(0)).is_null() && private_size > 0 {
        private_size = cff_dict_pack(
            *cffont.private.offset(0),
            &mut stream_data[offset..offset + private_size],
        );
        cff_dict_set(
            cffont.topdict,
            b"Private\x00" as *const u8 as *const i8,
            1i32,
            offset as f64,
        );
        cff_dict_set(
            cffont.topdict,
            b"Private\x00" as *const u8 as *const i8,
            0i32,
            private_size as f64,
        );
    }
    offset += private_size;
    /* Finally Top DICT */
    topdict.data = vec![0; (topdict.offset[topdict.count as usize]) as usize - 1];
    cff_dict_pack(cffont.topdict, &mut topdict.data[..]);
    let len = topdict.size();
    topdict.pack(&mut stream_data[topdict_offset..topdict_offset + len]);
    /* Copyright and Trademark Notice ommited. */
    /* Flush Font File */
    fontfile = pdf_new_stream(1i32 << 0i32);
    stream_dict = pdf_stream_dict(fontfile);
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"FontFile3\x00" as *const u8 as *const i8),
        pdf_ref_obj(fontfile),
    );
    pdf_add_dict(
        stream_dict,
        pdf_new_name(b"Subtype\x00" as *const u8 as *const i8),
        pdf_new_name(b"Type1C\x00" as *const u8 as *const i8),
    );
    pdf_add_stream(
        fontfile,
        stream_data.as_ptr() as *mut libc::c_void,
        offset as i32,
    );
    pdf_release_obj(fontfile);
    pdf_add_dict(
        descriptor,
        pdf_new_name(b"CharSet\x00" as *const u8 as *const i8),
        pdf_new_string(
            pdf_stream_dataptr(pdfcharset),
            pdf_stream_length(pdfcharset) as size_t,
        ),
    );
    offset as i32
}
#[no_mangle]
pub unsafe extern "C" fn pdf_font_load_type1(mut font: *mut pdf_font) -> i32 {
    let mut fontdict: *mut pdf_obj = 0 as *mut pdf_obj; /* Actually string object */
    let mut pdfcharset: *mut pdf_obj = 0 as *mut pdf_obj; /* With pseudo unique tag */
    let mut encoding_id: i32 = 0;
    let mut usedchars: *mut i8 = 0 as *mut i8;
    let mut ident: *mut i8 = 0 as *mut i8;
    let mut fontname: *mut i8 = 0 as *mut i8;
    let mut uniqueTag: *mut i8 = 0 as *mut i8;
    let mut fullname: *mut i8 = 0 as *mut i8;
    let mut cffont: *mut cff_font = 0 as *mut cff_font;
    let mut charset: *mut cff_charsets = 0 as *mut cff_charsets;
    let mut enc_vec: *mut *mut i8 = 0 as *mut *mut i8;
    let mut defaultwidth: f64 = 0.;
    let mut nominalwidth: f64 = 0.;
    let mut widths: *mut f64 = 0 as *mut f64;
    let mut GIDMap: *mut u16 = 0 as *mut u16;
    let mut num_glyphs: u16 = 0i32 as u16;
    let mut offset: i32 = 0;
    let mut code: i32 = 0;
    let mut verbose: i32 = 0;
    let mut handle: rust_input_handle_t = 0 as *mut libc::c_void;
    assert!(!font.is_null());
    if !pdf_font_is_in_use(font) {
        return 0i32;
    }
    verbose = pdf_font_get_verbose();
    encoding_id = pdf_font_get_encoding(font);
    fontdict = pdf_font_get_resource(font);
    pdf_font_get_descriptor(font);
    usedchars = pdf_font_get_usedchars(font);
    ident = pdf_font_get_ident(font);
    fontname = pdf_font_get_fontname(font);
    uniqueTag = pdf_font_get_uniqueTag(font);
    if usedchars.is_null() || ident.is_null() || fontname.is_null() {
        panic!("Type1: Unexpected error.");
    }
    handle = ttstub_input_open(ident, TTInputFormat::TYPE1, 0i32);
    if handle.is_null() {
        _tt_abort(
            b"Type1: Could not open Type1 font: %s\x00" as *const u8 as *const i8,
            ident,
        );
    }
    GIDMap = 0 as *mut u16;
    num_glyphs = 0i32 as u16;
    if encoding_id >= 0i32 {
        enc_vec = 0 as *mut *mut i8
    } else {
        enc_vec = new((256_u64).wrapping_mul(::std::mem::size_of::<*mut i8>() as u64) as u32)
            as *mut *mut i8;
        code = 0i32;
        while code <= 0xffi32 {
            let ref mut fresh0 = *enc_vec.offset(code as isize);
            *fresh0 = 0 as *mut i8;
            code += 1
        }
    }
    cffont = t1_load_font(enc_vec, 0i32, handle);
    if cffont.is_null() {
        _tt_abort(
            b"Could not load Type 1 font: %s\x00" as *const u8 as *const i8,
            ident,
        );
    }
    let cffont = &mut *cffont;
    ttstub_input_close(handle);
    fullname =
        new((strlen(fontname).wrapping_add(8)).wrapping_mul(::std::mem::size_of::<i8>()) as _)
            as *mut i8;
    sprintf(
        fullname,
        b"%6s+%s\x00" as *const u8 as *const i8,
        uniqueTag,
        fontname,
    );
    /* Encoding related things. */
    if encoding_id >= 0i32 {
        enc_vec = pdf_encoding_get_encoding(encoding_id)
    } else {
        /* Create enc_vec and ToUnicode CMap for built-in encoding. */
        let mut tounicode: *mut pdf_obj = 0 as *mut pdf_obj;
        if pdf_lookup_dict(fontdict, b"ToUnicode\x00" as *const u8 as *const i8).is_null() {
            tounicode = pdf_create_ToUnicode_CMap(fullname, enc_vec, usedchars);
            if !tounicode.is_null() {
                pdf_add_dict(
                    fontdict,
                    pdf_new_name(b"ToUnicode\x00" as *const u8 as *const i8),
                    pdf_ref_obj(tounicode),
                );
                pdf_release_obj(tounicode);
            }
        }
    }
    cff_set_name(cffont, fullname);
    free(fullname as *mut libc::c_void);
    /* defaultWidthX, CapHeight, etc. */
    get_font_attr(font, cffont);
    if cff_dict_known(
        *cffont.private.offset(0),
        b"defaultWidthX\x00" as *const u8 as *const i8,
    ) != 0
    {
        defaultwidth = cff_dict_get(
            *cffont.private.offset(0),
            b"defaultWidthX\x00" as *const u8 as *const i8,
            0i32,
        )
    } else {
        defaultwidth = 0.0f64
    }
    if cff_dict_known(
        *cffont.private.offset(0),
        b"nominalWidthX\x00" as *const u8 as *const i8,
    ) != 0
    {
        nominalwidth = cff_dict_get(
            *cffont.private.offset(0),
            b"nominalWidthX\x00" as *const u8 as *const i8,
            0i32,
        )
    } else {
        nominalwidth = 0.0f64
    }
    /* Create CFF encoding, charset, sort glyphs */
    GIDMap = new((1024_u64).wrapping_mul(::std::mem::size_of::<u16>() as u64) as u32) as *mut u16; /* FIXME */
    pdfcharset = pdf_new_stream(0i32);
    let mut prev: i32 = 0;
    let mut duplicate: i32 = 0;
    let mut gid: i32 = 0;
    let mut glyph: *mut i8 = 0 as *mut i8;
    let mut sid: s_SID = 0;
    cffont.encoding = new((1_u64).wrapping_mul(::std::mem::size_of::<cff_encoding>() as u64) as u32)
        as *mut cff_encoding;
    (*cffont.encoding).format = 1i32 as u8;
    (*cffont.encoding).num_entries = 0i32 as u8;
    (*cffont.encoding).data.range1 = new((256_u64)
        .wrapping_mul(::std::mem::size_of::<cff_range1>() as u64)
        as u32) as *mut cff_range1;
    (*cffont.encoding).num_supps = 0i32 as u8;
    (*cffont.encoding).supp =
        new((256_u64).wrapping_mul(::std::mem::size_of::<cff_map>() as u64) as u32) as *mut cff_map;
    charset = new((1_u64).wrapping_mul(::std::mem::size_of::<cff_charsets>() as u64) as u32)
        as *mut cff_charsets;
    (*charset).format = 0i32 as u8;
    (*charset).num_entries = 0i32 as u16;
    (*charset).data.glyphs =
        new((1024_u64).wrapping_mul(::std::mem::size_of::<s_SID>() as u64) as u32) as *mut s_SID;
    gid = cff_glyph_lookup(cffont, b".notdef\x00" as *const u8 as *const i8) as i32;
    if gid < 0i32 {
        panic!("Type 1 font with no \".notdef\" glyph???");
    }
    *GIDMap.offset(0) = gid as u16;
    if verbose > 2i32 {
        info!("[glyphs:/.notdef");
    }
    num_glyphs = 1i32 as u16;
    prev = -2i32;
    code = 0i32;
    while code <= 0xffi32 {
        glyph = *enc_vec.offset(code as isize);
        if !(*usedchars.offset(code as isize) == 0) {
            if streq_ptr(glyph, b".notdef\x00" as *const u8 as *const i8) {
                dpx_warning(
                    b"Character mapped to .notdef used in font: %s\x00" as *const u8 as *const i8,
                    fontname,
                );
                *usedchars.offset(code as isize) = 0_i8
            } else {
                gid = cff_glyph_lookup(cffont, glyph) as i32;
                if gid < 1i32 || gid >= (*cffont.cstrings).count as i32 {
                    dpx_warning(
                        b"Glyph \"%s\" missing in font \"%s\".\x00" as *const u8 as *const i8,
                        glyph,
                        fontname,
                    );
                    *usedchars.offset(code as isize) = 0_i8
                } else {
                    duplicate = 0i32;
                    while duplicate < code {
                        if *usedchars.offset(duplicate as isize) as i32 != 0
                            && !(*enc_vec.offset(duplicate as isize)).is_null()
                            && streq_ptr(*enc_vec.offset(duplicate as isize), glyph) as i32 != 0
                        {
                            break;
                        }
                        duplicate += 1
                    }
                    sid = cff_add_string(cffont, glyph, 1i32);
                    if duplicate < code {
                        /* found duplicates */
                        (*(*cffont.encoding)
                            .supp
                            .offset((*cffont.encoding).num_supps as isize))
                        .code = duplicate as u8;
                        (*(*cffont.encoding)
                            .supp
                            .offset((*cffont.encoding).num_supps as isize))
                        .glyph = sid;
                        (*cffont.encoding).num_supps =
                            ((*cffont.encoding).num_supps as i32 + 1i32) as u8
                    } else {
                        *GIDMap.offset(num_glyphs as isize) = gid as u16;
                        *(*charset)
                            .data
                            .glyphs
                            .offset((*charset).num_entries as isize) = sid;
                        (*charset).num_entries = ((*charset).num_entries as i32 + 1i32) as u16;
                        if code != prev + 1i32 {
                            (*cffont.encoding).num_entries =
                                ((*cffont.encoding).num_entries as i32 + 1i32) as u8;
                            (*(*cffont.encoding)
                                .data
                                .range1
                                .offset(((*cffont.encoding).num_entries as i32 - 1i32) as isize))
                            .first = code as s_SID;
                            (*(*cffont.encoding)
                                .data
                                .range1
                                .offset(((*cffont.encoding).num_entries as i32 - 1i32) as isize))
                            .n_left = 0i32 as u8
                        } else {
                            let ref mut fresh1 = (*(*cffont.encoding)
                                .data
                                .range1
                                .offset(((*cffont.encoding).num_entries as i32 - 1i32) as isize))
                            .n_left;
                            *fresh1 = (*fresh1 as i32 + 1i32) as u8
                        }
                        prev = code;
                        num_glyphs = num_glyphs.wrapping_add(1);
                        if verbose > 2i32 {
                            dpx_message(b"/%s\x00" as *const u8 as *const i8, glyph);
                        }
                        /* CharSet is actually string object. */
                        pdf_add_stream(
                            pdfcharset,
                            b"/\x00" as *const u8 as *const i8 as *const libc::c_void,
                            1i32,
                        );
                        pdf_add_stream(
                            pdfcharset,
                            glyph as *const libc::c_void,
                            strlen(glyph) as i32,
                        );
                    }
                }
            }
        }
        code += 1
    }
    if (*cffont.encoding).num_supps as i32 > 0i32 {
        (*cffont.encoding).format = ((*cffont.encoding).format as i32 | 0x80i32) as u8
    } else {
        (*cffont.encoding).supp =
            mfree((*cffont.encoding).supp as *mut libc::c_void) as *mut cff_map
    }
    widths = new(((*cffont.cstrings).count as u32 as u64)
        .wrapping_mul(::std::mem::size_of::<f64>() as u64) as u32) as *mut f64;
    /* No more strings will be added. The Type 1 seac operator may add another
     * glyph but the glyph name of those glyphs are contained in standard
     * string. The String Index will not be modified after here. BUT: We
     * cannot update the String Index yet because then we wouldn't be able to
     * find the GIDs of the base and accent characters (unless they have been
     * used already).
     */
    let mut cstring: *mut cff_index = 0 as *mut cff_index;
    let mut gm = t1_ginfo::new();
    let mut gid_0: u16 = 0;
    let mut gid_orig: u16 = 0;
    let mut dstlen_max: i32 = 0;
    let mut srclen: i32 = 0;
    let mut srcptr: *mut u8 = 0 as *mut u8;
    let mut dstptr: *mut u8 = 0 as *mut u8;
    dstlen_max = 0i64 as i32;
    offset = dstlen_max;
    cstring = cff_new_index((*cffont.cstrings).count);
    (*cstring).data = 0 as *mut u8;
    *(*cstring).offset.offset(0) = 1i32 as l_offset;
    let mut current_block_150: u64;
    /* The num_glyphs increases if "seac" operators are used. */
    gid_0 = 0i32 as u16;
    while (gid_0 as i32) < num_glyphs as i32 {
        if offset + 65536i32 >= dstlen_max {
            dstlen_max += 65536i32 * 2i32;
            (*cstring).data = renew(
                (*cstring).data as *mut libc::c_void,
                (dstlen_max as u32 as u64).wrapping_mul(::std::mem::size_of::<u8>() as u64) as u32,
            ) as *mut u8
        }
        gid_orig = *GIDMap.offset(gid_0 as isize);
        dstptr = (*cstring)
            .data
            .offset(*(*cstring).offset.offset(gid_0 as isize) as isize)
            .offset(-1);
        srcptr = (*cffont.cstrings)
            .data
            .offset(*(*cffont.cstrings).offset.offset(gid_orig as isize) as isize)
            .offset(-1);
        srclen = (*(*cffont.cstrings)
            .offset
            .offset((gid_orig as i32 + 1i32) as isize))
        .wrapping_sub(*(*cffont.cstrings).offset.offset(gid_orig as isize)) as i32;
        offset += t1char_convert_charstring(
            dstptr,
            65536i32,
            srcptr,
            srclen,
            *cffont.subrs.offset(0),
            defaultwidth,
            nominalwidth,
            &mut gm,
        );
        *(*cstring).offset.offset((gid_0 as i32 + 1i32) as isize) = (offset + 1i32) as l_offset;
        if gm.use_seac != 0 {
            let mut bchar_gid: i32 = 0;
            let mut achar_gid: i32 = 0;
            let mut i: i32 = 0;
            let mut bchar_name: *const i8 = 0 as *const i8;
            let mut achar_name: *const i8 = 0 as *const i8;
            /*
             * NOTE:
             *  1. seac.achar and seac.bchar must be contained in the CFF standard string.
             *  2. Those characters need not to be encoded.
             *  3. num_glyphs == charsets->num_entries + 1.
             */
            achar_name = t1_get_standard_glyph(gm.seac.achar as i32);
            achar_gid = cff_glyph_lookup(cffont, achar_name) as i32;
            bchar_name = t1_get_standard_glyph(gm.seac.bchar as i32);
            bchar_gid = cff_glyph_lookup(cffont, bchar_name) as i32;
            if achar_gid < 0i32 {
                dpx_warning(
                    b"Accent char \"%s\" not found. Invalid use of \"seac\" operator.\x00"
                        as *const u8 as *const i8,
                    achar_name,
                );
                current_block_150 = 1069630499025798221;
            } else if bchar_gid < 0i32 {
                dpx_warning(
                    b"Base char \"%s\" not found. Invalid use of \"seac\" operator.\x00"
                        as *const u8 as *const i8,
                    bchar_name,
                );
                current_block_150 = 1069630499025798221;
            } else {
                i = 0i32;
                while i < num_glyphs as i32 {
                    if *GIDMap.offset(i as isize) as i32 == achar_gid {
                        break;
                    }
                    i += 1
                }
                if i == num_glyphs as i32 {
                    if verbose > 2i32 {
                        dpx_message(b"/%s\x00" as *const u8 as *const i8, achar_name);
                    }
                    let fresh2 = num_glyphs;
                    num_glyphs = num_glyphs.wrapping_add(1);
                    *GIDMap.offset(fresh2 as isize) = achar_gid as u16;
                    *(*charset)
                        .data
                        .glyphs
                        .offset((*charset).num_entries as isize) =
                        cff_get_seac_sid(cffont, achar_name) as s_SID;
                    (*charset).num_entries = ((*charset).num_entries as i32 + 1i32) as u16
                }
                i = 0i32;
                while i < num_glyphs as i32 {
                    if *GIDMap.offset(i as isize) as i32 == bchar_gid {
                        break;
                    }
                    i += 1
                }
                if i == num_glyphs as i32 {
                    if verbose > 2i32 {
                        dpx_message(b"/%s\x00" as *const u8 as *const i8, bchar_name);
                    }
                    let fresh3 = num_glyphs;
                    num_glyphs = num_glyphs.wrapping_add(1);
                    *GIDMap.offset(fresh3 as isize) = bchar_gid as u16;
                    *(*charset)
                        .data
                        .glyphs
                        .offset((*charset).num_entries as isize) =
                        cff_get_seac_sid(cffont, bchar_name) as s_SID;
                    (*charset).num_entries = ((*charset).num_entries as i32 + 1i32) as u16
                }
                current_block_150 = 17100064147490331435;
            }
        } else {
            current_block_150 = 17100064147490331435;
        }
        match current_block_150 {
            17100064147490331435 => *widths.offset(gid_0 as isize) = gm.wx,
            _ => {}
        }
        gid_0 = gid_0.wrapping_add(1)
    }
    (*cstring).count = num_glyphs;
    cff_release_index(*cffont.subrs.offset(0));
    let ref mut fresh4 = *cffont.subrs.offset(0);
    *fresh4 = 0 as *mut cff_index;
    cffont.subrs = mfree(cffont.subrs as *mut libc::c_void) as *mut *mut cff_index;
    cff_release_index(cffont.cstrings);
    cffont.cstrings = cstring;
    cff_release_charsets(cffont.charsets);
    cffont.charsets = charset;
    if verbose > 2i32 {
        info!("]");
    }
    /* Now we can update the String Index */
    cff_dict_update(cffont.topdict, cffont);
    cff_dict_update(*cffont.private.offset(0), cffont);
    cff_update_string(cffont);
    add_metrics(font, cffont, enc_vec, widths, num_glyphs as i32);
    offset = write_fontfile(font, cffont, pdfcharset);
    if verbose > 1i32 {
        info!("[{} glyphs][{} bytes]", num_glyphs, offset);
    }
    pdf_release_obj(pdfcharset);
    cff_close(cffont);
    /* Cleanup */
    if encoding_id < 0i32 && !enc_vec.is_null() {
        code = 0i32;
        while code < 256i32 {
            let ref mut fresh5 = *enc_vec.offset(code as isize);
            *fresh5 = mfree(*enc_vec.offset(code as isize) as *mut libc::c_void) as *mut i8;
            code += 1
        }
        free(enc_vec as *mut libc::c_void);
    }
    free(widths as *mut libc::c_void);
    free(GIDMap as *mut libc::c_void);
    /* Maybe writing Charset is recommended for subsetted font. */
    0i32
}