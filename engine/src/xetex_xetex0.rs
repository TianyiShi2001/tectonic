#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]

use bridge::DisplayExt;
use std::ffi::CStr;
use std::io::Write;
use std::ptr;

use super::xetex_ini::Selector;
use super::xetex_io::{
    bytesFromUTF8, make_utf16_name, name_of_input_file, offsetsFromUTF8, tt_xetex_open_input,
    u_open_in,
};
use crate::core_memory::{mfree, xmalloc_array, xrealloc};
#[cfg(target_os = "macos")]
use crate::xetex_aatfont as aat;
use crate::xetex_consts::*;
use crate::xetex_errors::{confusion, error, fatal_error, overflow, pdf_error};
use crate::xetex_ext::{
    apply_mapping, apply_tfm_font_mapping, check_for_tfm_font_mapping, find_native_font,
    get_encoding_mode_and_info, get_font_char_range, get_glyph_bounds,
    get_native_char_height_depth, get_native_char_sidebearings, getnativechardp, getnativecharht,
    getnativecharic, getnativecharwd, gr_font_get_named, gr_font_get_named_1, gr_print_font_name,
    linebreak_next, linebreak_start, load_tfm_font_mapping, map_char_to_glyph, map_glyph_to_index,
    measure_native_glyph, measure_native_node, ot_font_get, ot_font_get_1, ot_font_get_2,
    ot_font_get_3, ot_get_font_metrics, print_glyph_name, print_utf8_str,
    real_get_native_glyph_italic_correction, real_get_native_italic_correction,
    real_get_native_word_cp, release_font_engine,
};
use crate::xetex_ini::{
    _xeq_level_array, active_width, adjust_tail, after_token, align_ptr, align_state,
    area_delimiter, arith_error, avail, bchar, best_height_plus_depth, breadth_max, buf_size,
    buffer, cancel_boundary, cond_ptr, cur_align, cur_area, cur_boundary, cur_box, cur_chr,
    cur_cmd, cur_cs, cur_dir, cur_ext, cur_group, cur_head, cur_if, cur_input, cur_l, cur_lang,
    cur_level, cur_list, cur_loop, cur_mark, cur_name, cur_order, cur_pre_head, cur_pre_tail,
    cur_ptr, cur_q, cur_r, cur_span, cur_tail, cur_tok, cur_val, cur_val1, cur_val_level,
    dead_cycles, def_ref, deletions_allowed, depth_threshold, dig, disc_ptr, empty, error_count,
    error_line, expand_depth, expand_depth_count, ext_delimiter, false_bchar,
    file_line_error_style_p, file_name_quote_char, file_offset, first, first_count, fmem_ptr,
    font_in_short_display, font_ptr, font_used, force_eof, gave_char_warning_help, half_error_line,
    hash, hash_extra, hash_high, hash_used, help_line, help_ptr, hi_mem_min, history, if_limit,
    if_line, init_pool_ptr, init_str_ptr, ins_disc, insert_penalties, insert_src_special_auto,
    insert_src_special_every_par, insert_src_special_every_vbox, interaction, is_hyph,
    is_in_csname, job_name, last, last_badness, last_glue, last_kern, last_leftmost_char,
    last_node_type, last_penalty, last_rightmost_char, lft_hit, lig_stack, ligature_present, line,
    lo_mem_max, loaded_font_design_size, loaded_font_flags, loaded_font_letter_space,
    loaded_font_mapping, log_file, log_opened, long_help_seen, long_state, mag_set, main_f, main_h,
    main_i, main_j, main_k, main_p, main_pp, main_ppp, main_s, mapped_text, max_buf_stack,
    max_nest_stack, max_print_line, max_reg_help_line, max_reg_num, max_strings, mem_end,
    name_in_progress, name_length, name_length16, name_of_file, name_of_file16,
    native_font_type_flag, native_len, native_text, native_text_size, nest, nest_ptr, nest_size,
    no_new_control_sequence, old_setting, open_parens, output_active, pack_begin_line,
    page_contents, page_so_far, page_tail, par_loc, par_token, pdf_last_x_pos, pdf_last_y_pos,
    pool_ptr, pool_size, pre_adjust_tail, prev_class, prim, prim_eqtb, prim_used, pseudo_files,
    pstack, quoted_filename, radix, read_file, read_open, rover, rt_hit, rust_stdout, sa_chain,
    sa_level, sa_null, sa_root, save_native_len, scanner_status, selector, set_box_allowed,
    shown_mode, skip_line, space_class, stop_at_space, str_pool, str_ptr, str_start, tally,
    temp_ptr, term_offset, tex_remainder, texmf_log_name, total_shrink, total_stretch, trick_buf,
    trick_count, use_err_help, used_tectonic_coda_tokens, warning_index, write_file, write_open,
    xtx_ligature_present, LR_problems, LR_ptr, BASE_PTR, BCHAR_LABEL, CHAR_BASE, DEPTH_BASE,
    EOF_SEEN, EQTB, EQTB_TOP, EXTEN_BASE, FONT_AREA, FONT_BC, FONT_BCHAR, FONT_CHECK, FONT_DSIZE,
    FONT_EC, FONT_FALSE_BCHAR, FONT_FLAGS, FONT_GLUE, FONT_INFO, FONT_LAYOUT_ENGINE,
    FONT_LETTER_SPACE, FONT_MAPPING, FONT_MAX, FONT_MEM_SIZE, FONT_NAME, FONT_PARAMS, FONT_SIZE,
    FULL_SOURCE_FILENAME_STACK, GRP_STACK, HEIGHT_BASE, HYPHEN_CHAR, IF_STACK, INPUT_FILE,
    INPUT_PTR, INPUT_STACK, IN_OPEN, ITALIC_BASE, KERN_BASE, LIG_KERN_BASE, LINE_STACK,
    MAX_IN_OPEN, MAX_IN_STACK, MAX_PARAM_STACK, MAX_SAVE_STACK, MEM, PARAM_BASE, PARAM_PTR,
    PARAM_SIZE, PARAM_STACK, SAVE_PTR, SAVE_SIZE, SAVE_STACK, SKEW_CHAR, SOURCE_FILENAME_STACK,
    STACK_SIZE, WIDTH_BASE,
};
use crate::xetex_ini::{b16x4, b32x2, memory_word, prefixed_command};
use crate::xetex_io::{input_line, open_or_close_in, set_input_file_encoding, u_close};
use crate::xetex_layout_interface::*;
use crate::xetex_linebreak::line_break;
use crate::xetex_math::{
    after_math, append_choices, build_choices, fin_mlist, flush_math, init_math, math_ac,
    math_fraction, math_left_right, math_limit_switch, math_radical, resume_after_display,
    start_eq_no, sub_sup,
};
use crate::xetex_output::{
    print, print_char, print_cs, print_cstr, print_current_string, print_esc, print_esc_cstr,
    print_file_line, print_file_name, print_hex, print_int, print_ln, print_native_word, print_nl,
    print_nl_cstr, print_raw_char, print_roman_int, print_sa_num, print_scaled, print_size,
    print_write_whatsit, sprint_cs,
};
use crate::xetex_pagebuilder::build_page;
use crate::xetex_pic::{count_pdf_file_pages, load_picture};
use crate::xetex_scaledmath::{mult_and_add, round_xn_over_d, tex_round, x_over_n, xn_over_d};
use crate::xetex_shipout::{finalize_dvi_file, new_edge, out_what, ship_out};
use crate::xetex_stringpool::{
    append_str, length, make_string, search_string, slow_make_string, str_eq_buf, str_eq_str,
};
use crate::xetex_synctex::{synctex_start_input, synctex_terminate};
use crate::xetex_texmfmp::{
    getmd5sum, gettexstring, is_new_source, make_src_special, maketexstring, remember_source_info,
};
use crate::xetex_xetexd::{is_char_node, is_non_discardable_node, print_c_string};
use bridge::{
    ttstub_input_close, ttstub_input_getc, ttstub_issue_warning, ttstub_output_close,
    ttstub_output_open, ttstub_output_putc,
};
use bridge::{TTHistory, TTInputFormat};

use libc::{free, memcpy, strcat, strcpy, strlen};

use bridge::InputHandleWrapper;
pub(crate) type scaled_t = i32;
pub(crate) type CFDictionaryRef = *mut libc::c_void;

pub(crate) type UTF16_code = u16;
pub(crate) type UTF8_code = u8;
pub(crate) type UnicodeScalar = i32;
pub(crate) type eight_bits = u8;
pub(crate) type pool_pointer = i32;
pub(crate) type str_number = i32;
pub(crate) type packed_UTF16_code = u16;
pub(crate) type small_number = i16;
pub(crate) type glue_ord = u8;
pub(crate) type group_code = u8;
pub(crate) type internal_font_number = i32;
pub(crate) type font_index = i32;
pub(crate) type nine_bits = i32;
pub(crate) type save_pointer = i32;

#[inline]
pub(crate) unsafe fn cur_length() -> pool_pointer {
    pool_ptr - *str_start.offset((str_ptr - 65536i32) as isize)
}
unsafe extern "C" fn int_error(mut n: i32) {
    print_cstr(b" (");
    print_int(n);
    print_char(')' as i32);
    error();
}
pub(crate) unsafe fn badness(mut t: scaled_t, mut s: scaled_t) -> i32 {
    if t == 0 {
        return 0;
    }
    if s <= 0 {
        return INF_BAD;
    }
    let r;
    if t <= 7230584 {
        /* magic constant */
        r = (t * 297) / s
    } else if s >= 1663497 {
        /* magic constant */
        r = t / (s / 297)
    } else {
        r = t
    }
    if r > 1290 {
        /* magic constant */
        return INF_BAD;
    }
    (r * r * r + 0x20000i32) / 0x40000i32
}

pub(crate) unsafe fn LLIST_link(p: isize) -> *mut i32 {
    &mut MEM[p as usize].b32.s1
}
pub(crate) unsafe fn LLIST_info(p: isize) -> *mut i32 {
    &mut MEM[p as usize].b32.s0
}

/// half of LLIST_info(p)
pub(crate) unsafe fn NODE_type(p: isize) -> *mut u16 {
    &mut MEM[p as usize].b16.s1
}
/// the other half of LLIST_info(p)
pub(crate) unsafe fn NODE_subtype(p: isize) -> *mut u16 {
    &mut MEM[p as usize].b16.s0
}
/// aka "llink" in doubly-linked list
pub(crate) unsafe fn GLUE_NODE_glue_ptr(p: isize) -> *mut i32 {
    &mut MEM[(p + 1) as usize].b32.s0
}
/// aka "rlink" in double-linked list
pub(crate) unsafe fn GLUE_NODE_leader_ptr(p: isize) -> *mut i32 {
    &mut MEM[(p + 1) as usize].b32.s1
}
/// was originally the `mem[x+1].int` field
pub(crate) unsafe fn PENALTY_NODE_penalty(p: isize) -> *mut i32 {
    &mut MEM[(p + 1) as usize].b32.s1
}

/// aka "type" of a node
pub(crate) unsafe fn GLUE_SPEC_stretch_order(p: isize) -> *mut u16 {
    &mut MEM[p as usize].b16.s1
}
/// aka "subtype" of a node
pub(crate) unsafe fn GLUE_SPEC_shrink_order(p: isize) -> *mut u16 {
    &mut MEM[p as usize].b16.s0
}
/// a scaled
pub(crate) unsafe fn GLUE_SPEC_stretch(p: isize) -> *mut i32 {
    &mut MEM[(p + 2) as usize].b32.s1
}
/// a scaled
pub(crate) unsafe fn GLUE_SPEC_shrink(p: isize) -> *mut i32 {
    &mut MEM[(p + 3) as usize].b32.s1
}

/// subtype; records L/R direction mode
pub(crate) unsafe fn BOX_lr_mode(p: isize) -> *mut u16 {
    &mut MEM[p as usize].b16.s0
}
/// a scaled; 1 <=> WEB const `width_offset`
pub(crate) unsafe fn BOX_width(p: isize) -> *mut i32 {
    &mut MEM[(p + 1) as usize].b32.s1
}
/// a scaled; 2 <=> WEB const `depth_offset`
pub(crate) unsafe fn BOX_depth(p: isize) -> *mut i32 {
    &mut MEM[(p + 2) as usize].b32.s1
}
/// a scaled; 3 <=> WEB const `height_offset`
pub(crate) unsafe fn BOX_height(p: isize) -> *mut i32 {
    &mut MEM[(p + 3) as usize].b32.s1
}
/// a scaled
pub(crate) unsafe fn BOX_shift_amount(p: isize) -> *mut i32 {
    &mut MEM[(p + 4) as usize].b32.s1
}
/// aka `link` of p+5
pub(crate) unsafe fn BOX_list_ptr(p: isize) -> *mut i32 {
    &mut MEM[(p + 5) as usize].b32.s1
}
/// aka `type` of p+5
pub(crate) unsafe fn BOX_glue_sign(p: isize) -> *mut u16 {
    &mut MEM[(p + 5) as usize].b16.s1
}
/// aka `subtype` of p+5
pub(crate) unsafe fn BOX_glue_order(p: isize) -> *mut u16 {
    &mut MEM[(p + 5) as usize].b16.s0
}
/// the glue ratio
pub(crate) unsafe fn BOX_glue_set(p: isize) -> *mut f64 {
    &mut MEM[(p + 6) as usize].gr
}

/// "new left_edge position relative to cur_h"
pub(crate) unsafe fn EDGE_NODE_edge_dist(p: isize) -> *mut i32 {
    &mut MEM[(p + 2) as usize].b32.s1
}

/*:112*/
/*118:*/
pub(crate) unsafe fn show_token_list(mut p: i32, mut q: i32, mut l: i32) {
    let mut m: i32 = 0;
    let mut c: i32 = 0;
    let mut match_chr: i32 = 0;
    let mut n: UTF16_code = 0;
    match_chr = '#' as i32;
    n = '0' as i32 as UTF16_code;
    tally = 0i32;
    while p != TEX_NULL && tally < l {
        /*332:*/
        if p == q {
            first_count = tally;
            trick_count = tally + 1i32 + error_line - half_error_line;
            if trick_count < error_line {
                trick_count = error_line
            }
        }
        if p < hi_mem_min || p > mem_end {
            print_esc_cstr(b"CLOBBERED.");
            return;
        }
        if MEM[p as usize].b32.s0 >= CS_TOKEN_FLAG {
            print_cs(MEM[p as usize].b32.s0 - CS_TOKEN_FLAG);
        } else {
            m = MEM[p as usize].b32.s0 / MAX_CHAR_VAL;
            c = MEM[p as usize].b32.s0 % MAX_CHAR_VAL;
            if MEM[p as usize].b32.s0 < 0 {
                print_esc_cstr(b"BAD.");
            } else {
                /*306:*/
                match m as u16 {
                    LEFT_BRACE | RIGHT_BRACE | MATH_SHIFT | TAB_MARK | SUP_MARK | SUB_MARK
                    | SPACER | LETTER | OTHER_CHAR => print_char(c),
                    MAC_PARAM => {
                        print_char(c);
                        print_char(c);
                    }
                    OUT_PARAM => {
                        print_char(match_chr);
                        if c <= 9i32 {
                            print_char(c + 48i32);
                        } else {
                            print_char('!' as i32);
                            return;
                        }
                    }
                    MATCH => {
                        match_chr = c;
                        print_char(c);
                        n = n.wrapping_add(1);
                        print_char(n as i32);
                        if n as i32 > '9' as i32 {
                            return;
                        }
                    }
                    END_MATCH => {
                        if c == 0 {
                            print_cstr(b"->");
                        }
                    }
                    _ => print_esc_cstr(b"BAD."),
                }
            }
        }
        p = *LLIST_link(p as isize);
    }
    if p != TEX_NULL {
        print_esc_cstr(b"ETC.");
    };
}
pub(crate) unsafe fn runaway() {
    let mut p: i32 = TEX_NULL;
    if scanner_status as i32 > SKIPPING {
        match scanner_status as i32 {
            DEFINING => {
                print_nl_cstr(b"Runaway definition");
                p = def_ref
            }
            MATCHING => {
                print_nl_cstr(b"Runaway argument");
                p = 4999999i32 - 3i32
            }
            ALIGNING => {
                print_nl_cstr(b"Runaway preamble");
                p = 4999999i32 - 4i32
            }
            ABSORBING => {
                print_nl_cstr(b"Runaway text");
                p = def_ref
            }
            _ => {}
        }
        print_char('?' as i32);
        print_ln();
        show_token_list(MEM[p as usize].b32.s1, TEX_NULL, error_line - 10);
    };
}
pub(crate) unsafe fn get_avail() -> i32 {
    let mut p = avail;
    if p != TEX_NULL {
        avail = *LLIST_link(avail as _);
    } else if mem_end < MEM_TOP {
        mem_end += 1;
        p = mem_end
    } else {
        hi_mem_min -= 1;
        p = hi_mem_min;
        if is_char_node(lo_mem_max) {
            runaway();
            overflow(b"main memory size", MEM_TOP + 1);
        }
    }
    MEM[p as usize].b32.s1 = TEX_NULL;
    p
}
pub(crate) unsafe fn flush_list(mut p: i32) {
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    if p != TEX_NULL {
        r = p;
        loop {
            q = r;
            r = MEM[r as usize].b32.s1;
            if r == TEX_NULL {
                break;
            }
        }
        MEM[q as usize].b32.s1 = avail;
        avail = p
    };
}
pub(crate) unsafe fn get_node(mut s: i32) -> i32 {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut t: i32 = 0;

    'restart: loop {
        p = rover;
        loop {
            /*131: */
            q = p + MEM[p as usize].b32.s0;
            while MEM[q as usize].b32.s1 == MAX_HALFWORD {
                t = MEM[(q + 1) as usize].b32.s1;
                if q == rover {
                    rover = t
                }
                MEM[(t + 1) as usize].b32.s0 = MEM[(q + 1) as usize].b32.s0;
                MEM[(MEM[(q + 1) as usize].b32.s0 + 1) as usize].b32.s1 = t;
                q = q + MEM[q as usize].b32.s0
            }
            r = q - s;
            if r > p + 1 {
                /*132: */
                MEM[p as usize].b32.s0 = r - p;
                rover = p;
                return found(r, s);
            }
            if r == p {
                if MEM[(p + 1) as usize].b32.s1 != p {
                    /*133: */
                    rover = MEM[(p + 1) as usize].b32.s1;
                    t = MEM[(p + 1) as usize].b32.s0;
                    MEM[(rover + 1) as usize].b32.s0 = t;
                    MEM[(t + 1) as usize].b32.s1 = rover;
                    return found(r, s);
                }
            }
            MEM[p as usize].b32.s0 = q - p;
            p = MEM[(p + 1) as usize].b32.s1;
            if p == rover {
                break;
            }
        }
        if s == 0x40000000 {
            return MAX_HALFWORD;
        }
        if lo_mem_max + 2 < hi_mem_min {
            if lo_mem_max + 2 <= MAX_HALFWORD {
                /*130: */
                if hi_mem_min - lo_mem_max >= 1998 {
                    t = lo_mem_max + 1000;
                } else {
                    t = lo_mem_max + 1 + (hi_mem_min - lo_mem_max) / 2;
                }
                p = MEM[(rover + 1) as usize].b32.s0;
                q = lo_mem_max;
                MEM[(p + 1) as usize].b32.s1 = q;
                MEM[(rover + 1) as usize].b32.s0 = q;
                if t > MAX_HALFWORD {
                    t = MAX_HALFWORD
                }
                MEM[(q + 1) as usize].b32.s1 = rover;
                MEM[(q + 1) as usize].b32.s0 = p;
                MEM[q as usize].b32.s1 = MAX_HALFWORD;
                MEM[q as usize].b32.s0 = t - lo_mem_max;
                lo_mem_max = t;
                MEM[lo_mem_max as usize].b32.s1 = TEX_NULL;
                MEM[lo_mem_max as usize].b32.s0 = TEX_NULL;
                rover = q;
                continue 'restart;
            }
        }
        break 'restart;
    }
    overflow(b"main memory size", MEM_TOP + 1);

    unsafe fn found(r: i32, s: i32) -> i32 {
        MEM[r as usize].b32.s1 = TEX_NULL;
        if s >= MEDIUM_NODE_SIZE {
            MEM[(r + s - 1) as usize].b32.s0 = cur_input.synctex_tag;
            MEM[(r + s - 1) as usize].b32.s1 = line
        }
        return r;
    }
}
pub(crate) unsafe fn free_node(mut p: i32, mut s: i32) {
    let mut q: i32 = 0;
    MEM[p as usize].b32.s0 = s;
    MEM[p as usize].b32.s1 = 0x3fffffff;
    q = MEM[(rover + 1) as usize].b32.s0;
    MEM[(p + 1) as usize].b32.s0 = q;
    MEM[(p + 1) as usize].b32.s1 = rover;
    MEM[(rover + 1) as usize].b32.s0 = p;
    MEM[(q + 1) as usize].b32.s1 = p;
}
pub(crate) unsafe fn new_null_box() -> i32 {
    let mut p: i32 = 0;
    p = get_node(8i32);
    MEM[p as usize].b16.s1 = 0_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s1 = 0;
    MEM[(p + 2) as usize].b32.s1 = 0;
    MEM[(p + 3) as usize].b32.s1 = 0;
    MEM[(p + 4) as usize].b32.s1 = 0;
    MEM[(p + 5) as usize].b32.s1 = TEX_NULL;
    MEM[(p + 5) as usize].b16.s1 = 0_u16;
    MEM[(p + 5) as usize].b16.s0 = 0_u16;
    MEM[(p + 6) as usize].gr = 0.0f64;
    p
}
pub(crate) unsafe fn new_rule() -> i32 {
    let mut p: i32 = 0;
    p = get_node(5i32);
    MEM[p as usize].b16.s1 = 2_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s1 = -0x40000000;
    MEM[(p + 2) as usize].b32.s1 = -0x40000000;
    MEM[(p + 3) as usize].b32.s1 = -0x40000000;
    p
}
pub(crate) unsafe fn new_ligature(mut f: internal_font_number, mut c: u16, mut q: i32) -> i32 {
    let mut p: i32 = 0;
    p = get_node(2i32);
    MEM[p as usize].b16.s1 = 6_u16;
    MEM[(p + 1) as usize].b16.s1 = f as u16;
    MEM[(p + 1) as usize].b16.s0 = c;
    MEM[(p + 1) as usize].b32.s1 = q;
    MEM[p as usize].b16.s0 = 0_u16;
    p
}
pub(crate) unsafe fn new_lig_item(mut c: u16) -> i32 {
    let mut p: i32 = 0;
    p = get_node(2i32);
    MEM[p as usize].b16.s0 = c;
    MEM[(p + 1) as usize].b32.s1 = TEX_NULL;
    p
}
pub(crate) unsafe fn new_disc() -> i32 {
    let mut p: i32 = 0;
    p = get_node(2i32);
    MEM[p as usize].b16.s1 = 7_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s0 = TEX_NULL;
    MEM[(p + 1) as usize].b32.s1 = TEX_NULL;
    p
}
pub(crate) unsafe fn copy_native_glyph_info(mut src: i32, mut dest: i32) {
    let mut glyph_count: i32 = 0;
    if !MEM[(src + 5) as usize].ptr.is_null() {
        glyph_count = MEM[(src + 4) as usize].b16.s0 as i32;
        MEM[(dest + 5) as usize].ptr =
            xmalloc_array::<libc::c_char>(glyph_count as usize * NATIVE_GLYPH_INFO_SIZE as usize)
                as *mut _;
        memcpy(
            MEM[(dest + 5) as usize].ptr,
            MEM[(src + 5) as usize].ptr,
            (glyph_count * 10i32) as usize,
        );
        MEM[(dest + 4) as usize].b16.s0 = glyph_count as u16
    };
}
pub(crate) unsafe fn new_math(mut w: scaled_t, mut s: small_number) -> i32 {
    let mut p: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 9_u16;
    MEM[p as usize].b16.s0 = s as u16;
    MEM[(p + 1) as usize].b32.s1 = w;
    p
}
pub(crate) unsafe fn new_spec(mut p: i32) -> i32 {
    let mut q: i32 = 0;
    q = get_node(4i32);
    MEM[q as usize] = MEM[p as usize];
    MEM[q as usize].b32.s1 = TEX_NULL;
    MEM[(q + 1) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1;
    MEM[(q + 2) as usize].b32.s1 = MEM[(p + 2) as usize].b32.s1;
    MEM[(q + 3) as usize].b32.s1 = MEM[(p + 3) as usize].b32.s1;
    q
}
pub(crate) unsafe fn new_param_glue(mut n: small_number) -> i32 {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 10_u16;
    MEM[p as usize].b16.s0 = (n as i32 + 1) as u16;
    MEM[(p + 1) as usize].b32.s1 = TEX_NULL;
    q = EQTB[(GLUE_BASE + n as i32) as usize].b32.s1;
    MEM[(p + 1) as usize].b32.s0 = q;
    MEM[q as usize].b32.s1 += 1;
    p
}
pub(crate) unsafe fn new_glue(mut q: i32) -> i32 {
    let mut p: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 10_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s1 = TEX_NULL;
    MEM[(p + 1) as usize].b32.s0 = q;
    MEM[q as usize].b32.s1 += 1;
    p
}
pub(crate) unsafe fn new_skip_param(mut n: small_number) -> i32 {
    let mut p: i32 = 0;
    temp_ptr = new_spec(EQTB[(GLUE_BASE + n as i32) as usize].b32.s1);
    p = new_glue(temp_ptr);
    MEM[temp_ptr as usize].b32.s1 = TEX_NULL;
    MEM[p as usize].b16.s0 = (n as i32 + 1) as u16;
    p
}
pub(crate) unsafe fn new_kern(mut w: scaled_t) -> i32 {
    let mut p: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 11_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s1 = w;
    p
}
pub(crate) unsafe fn new_penalty(mut m: i32) -> i32 {
    let mut p: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 12_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s1 = m;
    p
}
/*:165*/
pub(crate) unsafe fn prev_rightmost(mut s: i32, mut e: i32) -> i32 {
    let mut p: i32 = 0;
    p = s;
    if p == TEX_NULL {
        return TEX_NULL;
    }
    while MEM[p as usize].b32.s1 != e {
        p = MEM[p as usize].b32.s1;
        if p == TEX_NULL {
            return TEX_NULL;
        }
    }
    p
}
pub(crate) unsafe fn short_display(mut p: i32) {
    let mut n: i32 = 0;
    while p > 0i32 {
        if is_char_node(p) {
            if p <= mem_end {
                if MEM[p as usize].b16.s1 as i32 != font_in_short_display {
                    if MEM[p as usize].b16.s1 as i32 > FONT_MAX as i32 {
                        print_char('*' as i32);
                    } else {
                        /*279:*/
                        print_esc(
                            (*hash.offset((FONT_ID_BASE + MEM[p as usize].b16.s1 as i32) as isize))
                                .s1,
                        );
                    }
                    print_char(' ' as i32);
                    font_in_short_display = MEM[p as usize].b16.s1 as i32
                }
                print(MEM[p as usize].b16.s0 as i32);
            }
        } else {
            /*183:*/
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 3 | 4 | 5 | 13 => print_cstr(b"[]"),
                8 => match MEM[p as usize].b16.s0 as i32 {
                    40 | 41 => {
                        if MEM[(p + 4) as usize].b16.s2 as i32 != font_in_short_display {
                            print_esc(
                                (*hash.offset(
                                    (FONT_ID_BASE + MEM[(p + 4) as usize].b16.s2 as i32) as isize,
                                ))
                                .s1,
                            );
                            print_char(' ' as i32);
                            font_in_short_display = MEM[(p + 4) as usize].b16.s2 as i32
                        }
                        print_native_word(p);
                    }
                    _ => print_cstr(b"[]"),
                },
                2 => print_char('|' as i32),
                10 => {
                    if MEM[(p + 1) as usize].b32.s0 != 0 {
                        print_char(' ' as i32);
                    }
                }
                9 => {
                    if MEM[p as usize].b16.s0 as i32 >= 4 {
                        print_cstr(b"[]");
                    } else {
                        print_char('$' as i32);
                    }
                }
                6 => short_display(MEM[(p + 1) as usize].b32.s1),
                7 => {
                    short_display(MEM[(p + 1) as usize].b32.s0);
                    short_display(MEM[(p + 1) as usize].b32.s1);
                    n = MEM[p as usize].b16.s0 as i32;
                    while n > 0i32 {
                        if MEM[p as usize].b32.s1 != TEX_NULL {
                            p = MEM[p as usize].b32.s1
                        }
                        n -= 1
                    }
                }
                _ => {}
            }
        }
        p = MEM[p as usize].b32.s1
    }
}
pub(crate) unsafe fn print_font_and_char(mut p: i32) {
    if p > mem_end {
        print_esc_cstr(b"CLOBBERED.");
    } else {
        if MEM[p as usize].b16.s1 as i32 > FONT_MAX as i32 {
            print_char('*' as i32);
        } else {
            /*279: */
            print_esc((*hash.offset((FONT_ID_BASE + MEM[p as usize].b16.s1 as i32) as isize)).s1);
        }
        print_char(' ' as i32);
        print(MEM[p as usize].b16.s0 as i32);
    };
}
pub(crate) unsafe fn print_mark(mut p: i32) {
    print_char('{' as i32);
    if p < hi_mem_min || p > mem_end {
        print_esc_cstr(b"CLOBBERED.");
    } else {
        show_token_list(MEM[p as usize].b32.s1, TEX_NULL, max_print_line - 10);
    }
    print_char('}' as i32);
}
pub(crate) unsafe fn print_rule_dimen(mut d: scaled_t) {
    if d == -0x40000000i32 {
        print_char('*' as i32);
    } else {
        print_scaled(d);
    };
}
pub(crate) unsafe fn print_glue(mut d: scaled_t, mut order: i32, mut s: *const i8) {
    print_scaled(d);
    if order < 0i32 || order > 3i32 {
        print_cstr(b"foul");
    } else if order > 0i32 {
        print_cstr(b"fil");
        while order > 1i32 {
            print_char('l' as i32);
            order -= 1
        }
    } else if !s.is_null() {
        print_cstr(CStr::from_ptr(s).to_bytes());
    };
}
pub(crate) unsafe fn print_spec(mut p: i32, mut s: *const i8) {
    if p < 0i32 || p >= lo_mem_max {
        print_char('*' as i32);
    } else {
        print_scaled(MEM[(p + 1) as usize].b32.s1);
        if !s.is_null() {
            print_cstr(CStr::from_ptr(s).to_bytes());
        }
        if MEM[(p + 2) as usize].b32.s1 != 0 {
            print_cstr(b" plus ");
            print_glue(
                MEM[(p + 2) as usize].b32.s1,
                MEM[p as usize].b16.s1 as i32,
                s,
            );
        }
        if MEM[(p + 3) as usize].b32.s1 != 0 {
            print_cstr(b" minus ");
            print_glue(
                MEM[(p + 3) as usize].b32.s1,
                MEM[p as usize].b16.s0 as i32,
                s,
            );
        }
    };
}
pub(crate) unsafe fn print_fam_and_char(mut p: i32) {
    let mut c: i32 = 0;
    print_esc_cstr(b"fam");
    print_int(MEM[p as usize].b16.s1 as i32 % 256 % 256);
    print_char(' ' as i32);
    c = (MEM[p as usize].b16.s0 as i64 + (MEM[p as usize].b16.s1 as i32 / 256) as i64 * 65536)
        as i32;
    if (c as i64) < 65536 {
        print(c);
    } else {
        print_char(c);
    };
}
pub(crate) unsafe fn print_delimiter(mut p: i32) {
    let mut a: i32 = 0;
    a = ((MEM[p as usize].b16.s3 as i32 % 256 * 256) as i64
        + (MEM[p as usize].b16.s2 as i64 + (MEM[p as usize].b16.s3 as i32 / 256) as i64 * 65536))
        as i32;
    a = ((a * 4096i32 + MEM[p as usize].b16.s1 as i32 % 256 * 256) as i64
        + (MEM[p as usize].b16.s0 as i64 + (MEM[p as usize].b16.s1 as i32 / 256) as i64 * 65536))
        as i32;
    if a < 0i32 {
        print_int(a);
    } else {
        print_hex(a);
    };
}
pub(crate) unsafe fn print_subsidiary_data(mut p: i32, mut c: UTF16_code) {
    if cur_length() >= depth_threshold {
        if MEM[p as usize].b32.s1 != 0 {
            print_cstr(b" []");
        }
    } else {
        *str_pool.offset(pool_ptr as isize) = c;
        pool_ptr += 1;
        temp_ptr = p;
        match MEM[p as usize].b32.s1 {
            1 => {
                print_ln();
                print_current_string();
                print_fam_and_char(p);
            }
            2 => show_info(),
            3 => {
                if MEM[p as usize].b32.s0 == TEX_NULL {
                    print_ln();
                    print_current_string();
                    print_cstr(b"{}");
                } else {
                    show_info();
                }
            }
            _ => {}
        }
        pool_ptr -= 1
    };
}
pub(crate) unsafe fn print_style(mut c: i32) {
    match c / 2i32 {
        0 => print_esc_cstr(b"displaystyle"),
        1 => print_esc_cstr(b"textstyle"),
        2 => print_esc_cstr(b"scriptstyle"),
        3 => print_esc_cstr(b"scriptscriptstyle"),
        _ => print_cstr(b"Unknown style!"),
    };
}
pub(crate) unsafe fn print_skip_param(mut n: i32) {
    match n {
        0 => print_esc_cstr(b"lineskip"),
        1 => print_esc_cstr(b"baselineskip"),
        2 => print_esc_cstr(b"parskip"),
        3 => print_esc_cstr(b"abovedisplayskip"),
        4 => print_esc_cstr(b"belowdisplayskip"),
        5 => print_esc_cstr(b"abovedisplayshortskip"),
        6 => print_esc_cstr(b"belowdisplayshortskip"),
        7 => print_esc_cstr(b"leftskip"),
        8 => print_esc_cstr(b"rightskip"),
        9 => print_esc_cstr(b"topskip"),
        10 => print_esc_cstr(b"splittopskip"),
        11 => print_esc_cstr(b"tabskip"),
        12 => print_esc_cstr(b"spaceskip"),
        13 => print_esc_cstr(b"xspaceskip"),
        14 => print_esc_cstr(b"parfillskip"),
        15 => print_esc_cstr(b"XeTeXlinebreakskip"),
        16 => print_esc_cstr(b"thinmuskip"),
        17 => print_esc_cstr(b"medmuskip"),
        18 => print_esc_cstr(b"thickmuskip"),
        _ => print_cstr(b"[unknown glue parameter!]"),
    };
}
pub(crate) unsafe fn show_node_list(mut p: i32) {
    let mut n: i32 = 0;
    let mut i: i32 = 0;
    let mut g: f64 = 0.;
    if cur_length() > depth_threshold {
        if p > TEX_NULL {
            print_cstr(b" []");
        }
        return;
    }
    n = 0i32;
    while p > 0i32 {
        print_ln();
        print_current_string();
        if p > mem_end {
            print_cstr(b"Bad link, display aborted.");
            return;
        }
        n += 1;
        if n > breadth_max {
            print_cstr(b"etc.");
            return;
        }
        if is_char_node(p) {
            print_font_and_char(p);
        } else {
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 13 => {
                    if MEM[p as usize].b16.s1 as i32 == 0 {
                        print_esc('h' as i32);
                    } else if MEM[p as usize].b16.s1 as i32 == 1 {
                        print_esc('v' as i32);
                    } else {
                        print_esc_cstr(b"unset");
                    }
                    print_cstr(b"box(");
                    print_scaled(MEM[(p + 3) as usize].b32.s1);
                    print_char('+' as i32);
                    print_scaled(MEM[(p + 2) as usize].b32.s1);
                    print_cstr(b")x");
                    print_scaled(MEM[(p + 1) as usize].b32.s1);
                    if MEM[p as usize].b16.s1 as i32 == 13 {
                        /*193:*/
                        if MEM[p as usize].b16.s0 as i32 != 0 {
                            print_cstr(b" (");
                            print_int(MEM[p as usize].b16.s0 as i32 + 1);
                            print_cstr(b" columns)");
                        }
                        if MEM[(p + 6) as usize].b32.s1 != 0 {
                            print_cstr(b", stretch ");
                            print_glue(
                                MEM[(p + 6) as usize].b32.s1,
                                MEM[(p + 5) as usize].b16.s0 as i32,
                                ptr::null(),
                            );
                        }
                        if MEM[(p + 4) as usize].b32.s1 != 0 {
                            print_cstr(b", shrink ");
                            print_glue(
                                MEM[(p + 4) as usize].b32.s1,
                                MEM[(p + 5) as usize].b16.s1 as i32,
                                ptr::null(),
                            );
                        }
                    } else {
                        g = MEM[(p + 6) as usize].gr;
                        if g != 0.0f64 && MEM[(p + 5) as usize].b16.s1 as i32 != 0 {
                            print_cstr(b", glue set ");
                            if MEM[(p + 5) as usize].b16.s1 as i32 == 2 {
                                print_cstr(b"- ");
                            }
                            if g.abs() > 20000.0f64 {
                                if g > 0.0f64 {
                                    print_char('>' as i32);
                                } else {
                                    print_cstr(b"< -");
                                }
                                print_glue(
                                    (20000i32 as i64 * 65536) as scaled_t,
                                    MEM[(p + 5) as usize].b16.s0 as i32,
                                    ptr::null(),
                                );
                            } else {
                                print_glue(
                                    tex_round(65536 as f64 * g),
                                    MEM[(p + 5) as usize].b16.s0 as i32,
                                    ptr::null(),
                                );
                            }
                        }
                        if MEM[(p + 4) as usize].b32.s1 != 0 {
                            print_cstr(b", shifted ");
                            print_scaled(MEM[(p + 4) as usize].b32.s1);
                        }
                        /*1491:*/
                        if MEM[p as usize].b16.s1 as i32 == 0 && MEM[p as usize].b16.s0 as i32 == 2
                        {
                            print_cstr(b", display");
                        }
                    }
                    *str_pool.offset(pool_ptr as isize) = '.' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 5) as usize].b32.s1);
                    pool_ptr -= 1
                }
                2 => {
                    print_esc_cstr(b"rule(");
                    print_rule_dimen(MEM[(p + 3) as usize].b32.s1);
                    print_char('+' as i32);
                    print_rule_dimen(MEM[(p + 2) as usize].b32.s1);
                    print_cstr(b")x");
                    print_rule_dimen(MEM[(p + 1) as usize].b32.s1);
                }
                3 => {
                    print_esc_cstr(b"insert");
                    print_int(MEM[p as usize].b16.s0 as i32);
                    print_cstr(b", natural size ");
                    print_scaled(MEM[(p + 3) as usize].b32.s1);
                    print_cstr(b"; split(");
                    print_spec(MEM[(p + 4) as usize].b32.s1, ptr::null());
                    print_char(',' as i32);
                    print_scaled(MEM[(p + 2) as usize].b32.s1);
                    print_cstr(b"); float cost ");
                    print_int(MEM[(p + 1) as usize].b32.s1);
                    *str_pool.offset(pool_ptr as isize) = '.' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 4) as usize].b32.s0);
                    pool_ptr -= 1
                }
                8 => match MEM[p as usize].b16.s0 as i32 {
                    0 => {
                        print_write_whatsit(b"openout", p);
                        print_char('=' as i32);
                        print_file_name(
                            MEM[(p + 1) as usize].b32.s1,
                            MEM[(p + 2) as usize].b32.s0,
                            MEM[(p + 2) as usize].b32.s1,
                        );
                    }
                    1 => {
                        print_write_whatsit(b"write", p);
                        print_mark(MEM[(p + 1) as usize].b32.s1);
                    }
                    2 => print_write_whatsit(b"closeout", p),
                    3 => {
                        print_esc_cstr(b"special");
                        print_mark(MEM[(p + 1) as usize].b32.s1);
                    }
                    4 => {
                        print_esc_cstr(b"setlanguage");
                        print_int(MEM[(p + 1) as usize].b32.s1);
                        print_cstr(b" (hyphenmin ");
                        print_int(MEM[(p + 1) as usize].b16.s1 as i32);
                        print_char(',' as i32);
                        print_int(MEM[(p + 1) as usize].b16.s0 as i32);
                        print_char(')' as i32);
                    }
                    40 | 41 => {
                        print_esc(
                            (*hash.offset(
                                (FONT_ID_BASE + MEM[(p + 4) as usize].b16.s2 as i32) as isize,
                            ))
                            .s1,
                        );
                        print_char(' ' as i32);
                        print_native_word(p);
                    }
                    42 => {
                        print_esc(
                            (*hash.offset(
                                (FONT_ID_BASE + MEM[(p + 4) as usize].b16.s2 as i32) as isize,
                            ))
                            .s1,
                        );
                        print_cstr(b" glyph#");
                        print_int(MEM[(p + 4) as usize].b16.s1 as i32);
                    }
                    43 | 44 => {
                        if MEM[p as usize].b16.s0 as i32 == 43 {
                            print_esc_cstr(b"XeTeXpicfile");
                        } else {
                            print_esc_cstr(b"XeTeXpdffile");
                        }
                        print_cstr(b"( ");
                        i = 0i32;
                        while i < MEM[(p + 4) as usize].b16.s1 as i32 {
                            print_raw_char(
                                *(&mut MEM[(p + 9) as usize] as *mut memory_word as *mut u8)
                                    .offset(i as isize)
                                    as UTF16_code,
                                true,
                            );
                            i += 1
                        }
                        print('\"' as i32);
                    }
                    6 => print_esc_cstr(b"pdfsavepos"),
                    _ => print_cstr(b"whatsit?"),
                },
                10 => {
                    if MEM[p as usize].b16.s0 as i32 >= 100 {
                        /*198: */
                        print_esc_cstr(b""); /*:244 */
                        if MEM[p as usize].b16.s0 as i32 == 101 {
                            print_char('c' as i32); /*214:*/
                        } else if MEM[p as usize].b16.s0 as i32 == 102 {
                            print_char('x' as i32);
                        }
                        print_cstr(b"leaders ");
                        print_spec(MEM[(p + 1) as usize].b32.s0, ptr::null());
                        *str_pool.offset(pool_ptr as isize) = '.' as i32 as packed_UTF16_code;
                        pool_ptr += 1;
                        show_node_list(MEM[(p + 1) as usize].b32.s1);
                        pool_ptr -= 1
                    } else {
                        print_esc_cstr(b"glue");
                        if MEM[p as usize].b16.s0 as i32 != 0 {
                            print_char('(' as i32);
                            if (MEM[p as usize].b16.s0 as i32) < 98 {
                                print_skip_param(MEM[p as usize].b16.s0 as i32 - 1);
                            } else if MEM[p as usize].b16.s0 as i32 == 98 {
                                print_esc_cstr(b"nonscript");
                            } else {
                                print_esc_cstr(b"mskip");
                            }
                            print_char(')' as i32);
                        }
                        if MEM[p as usize].b16.s0 as i32 != 98 {
                            print_char(' ' as i32);
                            if (MEM[p as usize].b16.s0 as i32) < 98 {
                                print_spec(MEM[(p + 1) as usize].b32.s0, ptr::null());
                            } else {
                                print_spec(
                                    MEM[(p + 1) as usize].b32.s0,
                                    b"mu\x00" as *const u8 as *const i8,
                                );
                            }
                        }
                    }
                }
                11 => {
                    if MEM[p as usize].b16.s0 as i32 != 99 {
                        print_esc_cstr(b"kern");
                        if MEM[p as usize].b16.s0 as i32 != 0 {
                            print_char(' ' as i32);
                        }
                        print_scaled(MEM[(p + 1) as usize].b32.s1);
                        if MEM[p as usize].b16.s0 as i32 == 2 {
                            print_cstr(b" (for accent)");
                        } else if MEM[p as usize].b16.s0 as i32 == 3 {
                            print_cstr(b" (space adjustment)");
                        }
                    } else {
                        print_esc_cstr(b"mkern");
                        print_scaled(MEM[(p + 1) as usize].b32.s1);
                        print_cstr(b"mu");
                    }
                }
                40 => {
                    print_esc_cstr(b"kern");
                    print_scaled(MEM[(p + 1) as usize].b32.s1);
                    if MEM[p as usize].b16.s0 as i32 == 0 {
                        print_cstr(b" (left margin)");
                    } else {
                        print_cstr(b" (right margin)");
                    }
                }
                9 => {
                    if MEM[p as usize].b16.s0 as i32 > 1 {
                        if MEM[p as usize].b16.s0 as i32 & 1 != 0 {
                            print_esc_cstr(b"end");
                        } else {
                            print_esc_cstr(b"begin");
                        }
                        if MEM[p as usize].b16.s0 as i32 > 8 {
                            print_char('R' as i32);
                        } else if MEM[p as usize].b16.s0 as i32 > 4 {
                            print_char('L' as i32);
                        } else {
                            print_char('M' as i32);
                        }
                    } else {
                        print_esc_cstr(b"math");
                        if MEM[p as usize].b16.s0 as i32 == 0 {
                            print_cstr(b"on");
                        } else {
                            print_cstr(b"off");
                        }
                        if MEM[(p + 1) as usize].b32.s1 != 0 {
                            print_cstr(b", surrounded ");
                            print_scaled(MEM[(p + 1) as usize].b32.s1);
                        }
                    }
                }
                6 => {
                    print_font_and_char(p + 1i32);
                    print_cstr(b" (ligature ");
                    if MEM[p as usize].b16.s0 as i32 > 1 {
                        print_char('|' as i32);
                    }
                    font_in_short_display = MEM[(p + 1) as usize].b16.s1 as i32;
                    short_display(MEM[(p + 1) as usize].b32.s1);
                    if MEM[p as usize].b16.s0 as i32 & 1 != 0 {
                        print_char('|' as i32);
                    }
                    print_char(')' as i32);
                }
                12 => {
                    print_esc_cstr(b"penalty ");
                    print_int(MEM[(p + 1) as usize].b32.s1);
                }
                7 => {
                    print_esc_cstr(b"discretionary");
                    if MEM[p as usize].b16.s0 as i32 > 0 {
                        print_cstr(b" replacing ");
                        print_int(MEM[p as usize].b16.s0 as i32);
                    }
                    *str_pool.offset(pool_ptr as isize) = '.' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 1) as usize].b32.s0);
                    pool_ptr -= 1;
                    *str_pool.offset(pool_ptr as isize) = '|' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 1) as usize].b32.s1);
                    pool_ptr -= 1
                }
                4 => {
                    print_esc_cstr(b"mark");
                    if MEM[(p + 1) as usize].b32.s0 != 0 {
                        print_char('s' as i32);
                        print_int(MEM[(p + 1) as usize].b32.s0);
                    }
                    print_mark(MEM[(p + 1) as usize].b32.s1);
                }
                5 => {
                    print_esc_cstr(b"vadjust");
                    if MEM[p as usize].b16.s0 as i32 != 0 {
                        print_cstr(b" pre ");
                    }
                    *str_pool.offset(pool_ptr as isize) = '.' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 1) as usize].b32.s1);
                    pool_ptr -= 1
                }
                14 => print_style(MEM[p as usize].b16.s0 as i32),
                15 => {
                    print_esc_cstr(b"mathchoice");
                    *str_pool.offset(pool_ptr as isize) = 'D' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 1) as usize].b32.s0);
                    pool_ptr -= 1;
                    *str_pool.offset(pool_ptr as isize) = 'T' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 1) as usize].b32.s1);
                    pool_ptr -= 1;
                    *str_pool.offset(pool_ptr as isize) = 'S' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 2) as usize].b32.s0);
                    pool_ptr -= 1;
                    *str_pool.offset(pool_ptr as isize) = 's' as i32 as packed_UTF16_code;
                    pool_ptr += 1;
                    show_node_list(MEM[(p + 2) as usize].b32.s1);
                    pool_ptr -= 1
                }
                16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 27 | 26 | 29 | 28 | 30 | 31 => {
                    match MEM[p as usize].b16.s1 as i32 {
                        16 => print_esc_cstr(b"mathord"),
                        17 => print_esc_cstr(b"mathop"),
                        18 => print_esc_cstr(b"mathbin"),
                        19 => print_esc_cstr(b"mathrel"),
                        20 => print_esc_cstr(b"mathopen"),
                        21 => print_esc_cstr(b"mathclose"),
                        22 => print_esc_cstr(b"mathpunct"),
                        23 => print_esc_cstr(b"mathinner"),
                        27 => print_esc_cstr(b"overline"),
                        26 => print_esc_cstr(b"underline"),
                        29 => print_esc_cstr(b"vcenter"),
                        24 => {
                            print_esc_cstr(b"radical");
                            print_delimiter(p + 4i32);
                        }
                        28 => {
                            print_esc_cstr(b"accent");
                            print_fam_and_char(p + 4i32);
                        }
                        30 => {
                            print_esc_cstr(b"left");
                            print_delimiter(p + 1i32);
                        }
                        31 => {
                            if MEM[p as usize].b16.s0 as i32 == 0 {
                                print_esc_cstr(b"right");
                            } else {
                                print_esc_cstr(b"middle");
                            }
                            print_delimiter(p + 1i32);
                        }
                        _ => {}
                    }
                    if (MEM[p as usize].b16.s1 as i32) < 30 {
                        if MEM[p as usize].b16.s0 as i32 != 0 {
                            if MEM[p as usize].b16.s0 as i32 == 1 {
                                print_esc_cstr(b"limits");
                            } else {
                                print_esc_cstr(b"nolimits");
                            }
                        }
                        print_subsidiary_data(p + 1i32, '.' as i32 as UTF16_code);
                    }
                    print_subsidiary_data(p + 2i32, '^' as i32 as UTF16_code);
                    print_subsidiary_data(p + 3i32, '_' as i32 as UTF16_code);
                }
                25 => {
                    print_esc_cstr(b"fraction, thickness ");
                    if MEM[(p + 1) as usize].b32.s1 == 0x40000000 {
                        print_cstr(b"= default");
                    } else {
                        print_scaled(MEM[(p + 1) as usize].b32.s1);
                    }
                    if MEM[(p + 4) as usize].b16.s3 as i32 % 256 != 0
                        || MEM[(p + 4) as usize].b16.s2 as i64
                            + (MEM[(p + 4) as usize].b16.s3 as i32 / 256) as i64 * 65536
                            != 0i32 as i64
                        || MEM[(p + 4) as usize].b16.s1 as i32 % 256 != 0
                        || MEM[(p + 4) as usize].b16.s0 as i64
                            + (MEM[(p + 4) as usize].b16.s1 as i32 / 256) as i64 * 65536
                            != 0i32 as i64
                    {
                        print_cstr(b", left-delimiter ");
                        print_delimiter(p + 4i32);
                    }
                    if MEM[(p + 5) as usize].b16.s3 as i32 % 256 != 0
                        || MEM[(p + 5) as usize].b16.s2 as i64
                            + (MEM[(p + 5) as usize].b16.s3 as i32 / 256) as i64 * 65536
                            != 0i32 as i64
                        || MEM[(p + 5) as usize].b16.s1 as i32 % 256 != 0
                        || MEM[(p + 5) as usize].b16.s0 as i64
                            + (MEM[(p + 5) as usize].b16.s1 as i32 / 256) as i64 * 65536
                            != 0i32 as i64
                    {
                        print_cstr(b", right-delimiter ");
                        print_delimiter(p + 5i32);
                    }
                    print_subsidiary_data(p + 2i32, '\\' as i32 as UTF16_code);
                    print_subsidiary_data(p + 3i32, '/' as i32 as UTF16_code);
                }
                _ => print_cstr(b"Unknown node type!"),
            }
        }
        p = MEM[p as usize].b32.s1
    }
}
pub(crate) unsafe fn show_box(mut p: i32) {
    depth_threshold = EQTB[(INT_BASE + 25i32) as usize].b32.s1;
    breadth_max = EQTB[(INT_BASE + 24i32) as usize].b32.s1;
    if breadth_max <= 0i32 {
        breadth_max = 5i32
    }
    if pool_ptr + depth_threshold >= pool_size {
        depth_threshold = pool_size - pool_ptr - 1i32
    }
    show_node_list(p);
    print_ln();
}
pub(crate) unsafe fn short_display_n(mut p: i32, mut m: i32) {
    breadth_max = m;
    depth_threshold = pool_size - pool_ptr - 1i32;
    show_node_list(p);
}
pub(crate) unsafe fn delete_token_ref(mut p: i32) {
    if MEM[p as usize].b32.s0 == TEX_NULL {
        flush_list(p);
    } else {
        MEM[p as usize].b32.s0 -= 1;
    };
}
pub(crate) unsafe fn delete_glue_ref(mut p: i32) {
    if MEM[p as usize].b32.s1 == TEX_NULL {
        free_node(p, 4i32);
    } else {
        MEM[p as usize].b32.s1 -= 1;
    };
}
pub(crate) unsafe fn flush_node_list(mut p: i32) {
    let mut current_block: u64;
    let mut q: i32 = 0;
    while p != TEX_NULL {
        q = MEM[p as usize].b32.s1;
        if is_char_node(p) {
            MEM[p as usize].b32.s1 = avail;
            avail = p
        } else {
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 13 => {
                    flush_node_list(MEM[(p + 5) as usize].b32.s1);
                    free_node(p, 8i32);
                    current_block = 16791665189521845338;
                }
                2 => {
                    free_node(p, 5i32);
                    current_block = 16791665189521845338;
                }
                3 => {
                    flush_node_list(MEM[(p + 4) as usize].b32.s0);
                    delete_glue_ref(MEM[(p + 4) as usize].b32.s1);
                    free_node(p, 5i32);
                    current_block = 16791665189521845338;
                }
                8 => {
                    match MEM[p as usize].b16.s0 as i32 {
                        0 => free_node(p, 3i32),
                        1 | 3 => {
                            delete_token_ref(MEM[(p + 1) as usize].b32.s1);
                            free_node(p, 2i32);
                        }
                        2 | 4 => free_node(p, 2i32),
                        40 | 41 => {
                            if !MEM[(p + 5) as usize].ptr.is_null() {
                                MEM[(p + 5) as usize].ptr = mfree(MEM[(p + 5) as usize].ptr);
                                MEM[(p + 4) as usize].b16.s0 = 0_u16
                            }
                            free_node(p, MEM[(p + 4) as usize].b16.s3 as i32);
                        }
                        42 => free_node(p, 5i32),
                        43 | 44 => {
                            free_node(
                                p,
                                (9i32 as u64).wrapping_add(
                                    (MEM[(p + 4) as usize].b16.s1 as u64)
                                        .wrapping_add(::std::mem::size_of::<memory_word>() as u64)
                                        .wrapping_sub(1i32 as u64)
                                        .wrapping_div(::std::mem::size_of::<memory_word>() as u64),
                                ) as i32,
                            );
                        }
                        6 => free_node(p, 2i32),
                        _ => confusion(b"ext3"),
                    }
                    current_block = 16791665189521845338;
                }
                10 => {
                    if MEM[MEM[(p + 1) as usize].b32.s0 as usize].b32.s1 == TEX_NULL {
                        free_node(MEM[(p + 1) as usize].b32.s0, 4);
                    } else {
                        MEM[MEM[(p + 1) as usize].b32.s0 as usize].b32.s1 -= 1
                    }
                    if MEM[(p + 1) as usize].b32.s1 != TEX_NULL {
                        flush_node_list(MEM[(p + 1) as usize].b32.s1);
                    }
                    free_node(p, 3i32);
                    current_block = 16791665189521845338;
                }
                11 | 9 | 12 => {
                    free_node(p, 3i32);
                    current_block = 16791665189521845338;
                }
                40 => {
                    free_node(p, 3i32);
                    current_block = 16791665189521845338;
                }
                6 => {
                    flush_node_list(MEM[(p + 1) as usize].b32.s1);
                    current_block = 8062065914618164218;
                }
                4 => {
                    delete_token_ref(MEM[(p + 1) as usize].b32.s1);
                    current_block = 8062065914618164218;
                }
                7 => {
                    flush_node_list(MEM[(p + 1) as usize].b32.s0);
                    flush_node_list(MEM[(p + 1) as usize].b32.s1);
                    current_block = 8062065914618164218;
                }
                5 => {
                    flush_node_list(MEM[(p + 1) as usize].b32.s1);
                    current_block = 8062065914618164218;
                }
                14 => {
                    free_node(p, 3i32);
                    current_block = 16791665189521845338;
                }
                15 => {
                    flush_node_list(MEM[(p + 1) as usize].b32.s0);
                    flush_node_list(MEM[(p + 1) as usize].b32.s1);
                    flush_node_list(MEM[(p + 2) as usize].b32.s0);
                    flush_node_list(MEM[(p + 2) as usize].b32.s1);
                    free_node(p, 3i32);
                    current_block = 16791665189521845338;
                }
                16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 27 | 26 | 29 | 28 => {
                    if MEM[(p + 1) as usize].b32.s1 >= 2 {
                        flush_node_list(MEM[(p + 1) as usize].b32.s0);
                    }
                    if MEM[(p + 2) as usize].b32.s1 >= 2 {
                        flush_node_list(MEM[(p + 2) as usize].b32.s0);
                    }
                    if MEM[(p + 3) as usize].b32.s1 >= 2 {
                        flush_node_list(MEM[(p + 3) as usize].b32.s0);
                    }
                    if MEM[p as usize].b16.s1 as i32 == 24 {
                        free_node(p, 5i32);
                    } else if MEM[p as usize].b16.s1 as i32 == 28 {
                        free_node(p, 5i32);
                    } else {
                        free_node(p, 4i32);
                    }
                    current_block = 16791665189521845338;
                }
                30 | 31 => {
                    free_node(p, 4i32);
                    current_block = 16791665189521845338;
                }
                25 => {
                    flush_node_list(MEM[(p + 2) as usize].b32.s0);
                    flush_node_list(MEM[(p + 3) as usize].b32.s0);
                    free_node(p, 6i32);
                    current_block = 16791665189521845338;
                }
                _ => confusion(b"flushing"),
            }
            match current_block {
                16791665189521845338 => {}
                _ => free_node(p, 2i32),
            }
        }
        p = q
    }
}
pub(crate) unsafe fn copy_node_list(mut p: i32) -> i32 {
    let mut h: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut words: u8 = 0;
    h = get_avail();
    q = h;
    while p != TEX_NULL {
        words = 1_u8;
        if is_char_node(p) {
            r = get_avail()
        } else {
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 13 => {
                    r = get_node(8i32);
                    MEM[(r + 8 - 1) as usize].b32.s0 = MEM[(p + 8 - 1) as usize].b32.s0;
                    MEM[(r + 8 - 1) as usize].b32.s1 = MEM[(p + 8 - 1) as usize].b32.s1;
                    MEM[(r + 6) as usize] = MEM[(p + 6) as usize];
                    MEM[(r + 5) as usize] = MEM[(p + 5) as usize];
                    MEM[(r + 5) as usize].b32.s1 = copy_node_list(MEM[(p + 5) as usize].b32.s1);
                    words = 5_u8
                }
                2 => {
                    r = get_node(5i32);
                    words = (5i32 - 1i32) as u8
                }
                3 => {
                    r = get_node(5i32);
                    MEM[(r + 4) as usize] = MEM[(p + 4) as usize];
                    MEM[MEM[(p + 4) as usize].b32.s1 as usize].b32.s1 += 1;
                    MEM[(r + 4) as usize].b32.s0 = copy_node_list(MEM[(p + 4) as usize].b32.s0);
                    words = (5i32 - 1i32) as u8
                }
                8 => match MEM[p as usize].b16.s0 as i32 {
                    0 => {
                        r = get_node(3i32);
                        words = 3_u8
                    }
                    1 | 3 => {
                        r = get_node(2i32);
                        MEM[MEM[(p + 1) as usize].b32.s1 as usize].b32.s0 += 1;
                        words = 2_u8
                    }
                    2 | 4 => {
                        r = get_node(2i32);
                        words = 2_u8
                    }
                    40 | 41 => {
                        words = MEM[(p + 4) as usize].b16.s3 as u8;
                        r = get_node(words as i32);
                        while words as i32 > 0i32 {
                            words = words.wrapping_sub(1);
                            MEM[(r + words as i32) as usize] = MEM[(p + words as i32) as usize]
                        }
                        MEM[(r + 5) as usize].ptr = 0 as *mut libc::c_void;
                        MEM[(r + 4) as usize].b16.s0 = 0_u16;
                        copy_native_glyph_info(p, r);
                    }
                    42 => {
                        r = get_node(5i32);
                        words = 5_u8
                    }
                    43 | 44 => {
                        words = (9i32 as u64).wrapping_add(
                            (MEM[(p + 4) as usize].b16.s1 as u64)
                                .wrapping_add(::std::mem::size_of::<memory_word>() as u64)
                                .wrapping_sub(1i32 as u64)
                                .wrapping_div(::std::mem::size_of::<memory_word>() as u64),
                        ) as u8;
                        r = get_node(words as i32)
                    }
                    6 => r = get_node(2i32),
                    _ => confusion(b"ext2"),
                },
                10 => {
                    r = get_node(3i32);
                    MEM[MEM[(p + 1) as usize].b32.s0 as usize].b32.s1 += 1;
                    MEM[(r + 2) as usize].b32.s0 = MEM[(p + 2) as usize].b32.s0;
                    MEM[(r + 2) as usize].b32.s1 = MEM[(p + 2) as usize].b32.s1;
                    MEM[(r + 1) as usize].b32.s0 = MEM[(p + 1) as usize].b32.s0;
                    MEM[(r + 1) as usize].b32.s1 = copy_node_list(MEM[(p + 1) as usize].b32.s1)
                }
                11 | 9 | 12 => {
                    r = get_node(3i32);
                    words = 3_u8
                }
                40 => {
                    r = get_node(3i32);
                    words = 3_u8
                }
                6 => {
                    r = get_node(2i32);
                    MEM[(r + 1) as usize] = MEM[(p + 1) as usize];
                    MEM[(r + 1) as usize].b32.s1 = copy_node_list(MEM[(p + 1) as usize].b32.s1)
                }
                7 => {
                    r = get_node(2i32);
                    MEM[(r + 1) as usize].b32.s0 = copy_node_list(MEM[(p + 1) as usize].b32.s0);
                    MEM[(r + 1) as usize].b32.s1 = copy_node_list(MEM[(p + 1) as usize].b32.s1)
                }
                4 => {
                    r = get_node(2i32);
                    MEM[MEM[(p + 1) as usize].b32.s1 as usize].b32.s0 += 1;
                    words = 2_u8
                }
                5 => {
                    r = get_node(2i32);
                    MEM[(r + 1) as usize].b32.s1 = copy_node_list(MEM[(p + 1) as usize].b32.s1)
                }
                _ => confusion(b"copying"),
            }
        }
        while words as i32 > 0i32 {
            words = words.wrapping_sub(1);
            MEM[(r + words as i32) as usize] = MEM[(p + words as i32) as usize]
        }
        MEM[q as usize].b32.s1 = r;
        q = r;
        p = MEM[p as usize].b32.s1
    }
    MEM[q as usize].b32.s1 = TEX_NULL;
    q = MEM[h as usize].b32.s1;
    MEM[h as usize].b32.s1 = avail;
    avail = h;
    q
}
pub(crate) unsafe fn print_mode(mut m: i32) {
    if m > 0i32 {
        match m / (102i32 + 1i32) {
            0 => print_cstr(b"vertical mode"),
            1 => print_cstr(b"horizontal mode"),
            2 => print_cstr(b"display math mode"),
            _ => {}
        }
    } else if m == 0i32 {
        print_cstr(b"no mode");
    } else {
        match -m / (102i32 + 1i32) {
            0 => print_cstr(b"internal vertical mode"),
            1 => print_cstr(b"restricted horizontal mode"),
            2 => print_cstr(b"math mode"),
            _ => {}
        }
    };
}
pub(crate) unsafe fn print_in_mode(mut m: i32) {
    if m > 0i32 {
        match m / (102i32 + 1i32) {
            0 => print_cstr(b"\' in vertical mode"),
            1 => print_cstr(b"\' in horizontal mode"),
            2 => print_cstr(b"\' in display math mode"),
            _ => {}
        }
    } else if m == 0i32 {
        print_cstr(b"\' in no mode");
    } else {
        match -m / (102i32 + 1i32) {
            0 => print_cstr(b"\' in internal vertical mode"),
            1 => print_cstr(b"\' in restricted horizontal mode"),
            2 => print_cstr(b"\' in math mode"),
            _ => {}
        }
    };
}
pub(crate) unsafe fn push_nest() {
    if nest_ptr > max_nest_stack {
        max_nest_stack = nest_ptr;
        if nest_ptr == nest_size {
            overflow(b"semantic nest size", nest_size);
        }
    }
    *nest.offset(nest_ptr as isize) = cur_list;
    nest_ptr += 1;
    cur_list.head = get_avail();
    cur_list.tail = cur_list.head;
    cur_list.prev_graf = 0i32;
    cur_list.mode_line = line;
    cur_list.eTeX_aux = TEX_NULL;
}
pub(crate) unsafe fn pop_nest() {
    MEM[cur_list.head as usize].b32.s1 = avail;
    avail = cur_list.head;
    nest_ptr -= 1;
    cur_list = *nest.offset(nest_ptr as isize);
}
pub(crate) unsafe fn show_activities() {
    let mut p: i32 = 0;
    let mut m: i16 = 0;
    let mut a: memory_word = memory_word {
        b32: b32x2 { s0: 0, s1: 0 },
    };
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut t: i32 = 0;
    *nest.offset(nest_ptr as isize) = cur_list;
    print_nl_cstr(b"");
    print_ln();
    let mut for_end: i32 = 0;
    p = nest_ptr;
    for_end = 0i32;
    if p >= for_end {
        loop {
            m = (*nest.offset(p as isize)).mode;
            a = (*nest.offset(p as isize)).aux;
            print_nl_cstr(b"### ");
            print_mode(m as i32);
            print_cstr(b" entered at line ");
            print_int((*nest.offset(p as isize)).mode_line.abs());
            if m as i32 == 104i32 {
                if (*nest.offset(p as isize)).prev_graf != 0x830000i32 {
                    print_cstr(b" (language");
                    print_int(((*nest.offset(p as isize)).prev_graf as i64 % 65536) as i32);
                    print_cstr(b":hyphenmin");
                    print_int((*nest.offset(p as isize)).prev_graf / 0x400000i32);
                    print_char(',' as i32);
                    print_int(
                        ((*nest.offset(p as isize)).prev_graf as i64 / 65536 % 64i32 as i64) as i32,
                    );
                    print_char(')' as i32);
                }
            }
            if (*nest.offset(p as isize)).mode_line < 0i32 {
                print_cstr(b" (\\output routine)");
            }
            if p == 0i32 {
                if 4999999i32 - 2i32 != page_tail {
                    print_nl_cstr(b"### current page:");
                    if output_active {
                        print_cstr(b" (held over for next output)");
                    }
                    show_box(MEM[(4999999 - 2) as usize].b32.s1);
                    if page_contents as i32 > 0i32 {
                        print_nl_cstr(b"total height ");
                        print_totals();
                        print_nl_cstr(b" goal height ");
                        print_scaled(page_so_far[0]);
                        r = MEM[4999999].b32.s1;
                        while r != 4999999i32 {
                            print_ln();
                            print_esc_cstr(b"insert");
                            t = MEM[r as usize].b16.s0 as i32;
                            print_int(t);
                            print_cstr(b" adds ");
                            if EQTB[(COUNT_BASE + t) as usize].b32.s1 == 1000i32 {
                                t = MEM[(r + 3) as usize].b32.s1
                            } else {
                                t = x_over_n(MEM[(r + 3) as usize].b32.s1, 1000)
                                    * EQTB[(COUNT_BASE + t) as usize].b32.s1
                            }
                            print_scaled(t);
                            if MEM[r as usize].b16.s1 as i32 == 1 {
                                q = 4999999i32 - 2i32;
                                t = 0i32;
                                loop {
                                    q = MEM[q as usize].b32.s1;
                                    if MEM[q as usize].b16.s1 as i32 == 3
                                        && MEM[q as usize].b16.s0 as i32
                                            == MEM[r as usize].b16.s0 as i32
                                    {
                                        t += 1
                                    }
                                    if q == MEM[(r + 1) as usize].b32.s0 {
                                        break;
                                    }
                                }
                                print_cstr(b", #");
                                print_int(t);
                                print_cstr(b" might split");
                            }
                            r = MEM[r as usize].b32.s1
                        }
                    }
                }
                if MEM[(4999999 - 1) as usize].b32.s1 != TEX_NULL {
                    print_nl_cstr(b"### recent contributions:");
                }
            }
            show_box(MEM[(*nest.offset(p as isize)).head as usize].b32.s1);
            match (m as i32).abs() / (102i32 + 1i32) {
                0 => {
                    print_nl_cstr(b"prevdepth ");
                    if a.b32.s1 <= -65536000i32 {
                        print_cstr(b"ignored");
                    } else {
                        print_scaled(a.b32.s1);
                    }
                    if (*nest.offset(p as isize)).prev_graf != 0i32 {
                        print_cstr(b", prevgraf ");
                        print_int((*nest.offset(p as isize)).prev_graf);
                        if (*nest.offset(p as isize)).prev_graf != 1i32 {
                            print_cstr(b" lines");
                        } else {
                            print_cstr(b" line");
                        }
                    }
                }
                1 => {
                    print_nl_cstr(b"spacefactor ");
                    print_int(a.b32.s0);
                    if m as i32 > 0i32 {
                        if a.b32.s1 > 0i32 {
                            print_cstr(b", current language ");
                            print_int(a.b32.s1);
                        }
                    }
                }
                2 => {
                    if a.b32.s1 != TEX_NULL {
                        print_cstr(b"this will be denominator of:");
                        show_box(a.b32.s1);
                    }
                }
                _ => {}
            }
            let fresh13 = p;
            p = p - 1;
            if !(fresh13 > for_end) {
                break;
            }
        }
    };
}
pub(crate) unsafe fn print_param(mut n: i32) {
    match n {
        0 => print_esc_cstr(b"pretolerance"),
        1 => print_esc_cstr(b"tolerance"),
        2 => print_esc_cstr(b"linepenalty"),
        3 => print_esc_cstr(b"hyphenpenalty"),
        4 => print_esc_cstr(b"exhyphenpenalty"),
        5 => print_esc_cstr(b"clubpenalty"),
        6 => print_esc_cstr(b"widowpenalty"),
        7 => print_esc_cstr(b"displaywidowpenalty"),
        8 => print_esc_cstr(b"brokenpenalty"),
        9 => print_esc_cstr(b"binoppenalty"),
        10 => print_esc_cstr(b"relpenalty"),
        11 => print_esc_cstr(b"predisplaypenalty"),
        12 => print_esc_cstr(b"postdisplaypenalty"),
        13 => print_esc_cstr(b"interlinepenalty"),
        14 => print_esc_cstr(b"doublehyphendemerits"),
        15 => print_esc_cstr(b"finalhyphendemerits"),
        16 => print_esc_cstr(b"adjdemerits"),
        17 => print_esc_cstr(b"mag"),
        18 => print_esc_cstr(b"delimiterfactor"),
        19 => print_esc_cstr(b"looseness"),
        20 => print_esc_cstr(b"time"),
        21 => print_esc_cstr(b"day"),
        22 => print_esc_cstr(b"month"),
        23 => print_esc_cstr(b"year"),
        24 => print_esc_cstr(b"showboxbreadth"),
        25 => print_esc_cstr(b"showboxdepth"),
        26 => print_esc_cstr(b"hbadness"),
        27 => print_esc_cstr(b"vbadness"),
        28 => print_esc_cstr(b"pausing"),
        29 => print_esc_cstr(b"tracingonline"),
        30 => print_esc_cstr(b"tracingmacros"),
        31 => print_esc_cstr(b"tracingstats"),
        32 => print_esc_cstr(b"tracingparagraphs"),
        33 => print_esc_cstr(b"tracingpages"),
        34 => print_esc_cstr(b"tracingoutput"),
        35 => print_esc_cstr(b"tracinglostchars"),
        36 => print_esc_cstr(b"tracingcommands"),
        37 => print_esc_cstr(b"tracingrestores"),
        38 => print_esc_cstr(b"uchyph"),
        39 => print_esc_cstr(b"outputpenalty"),
        40 => print_esc_cstr(b"maxdeadcycles"),
        41 => print_esc_cstr(b"hangafter"),
        42 => print_esc_cstr(b"floatingpenalty"),
        43 => print_esc_cstr(b"globaldefs"),
        44 => print_esc_cstr(b"fam"),
        45 => print_esc_cstr(b"escapechar"),
        46 => print_esc_cstr(b"defaulthyphenchar"),
        47 => print_esc_cstr(b"defaultskewchar"),
        48 => print_esc_cstr(b"endlinechar"),
        49 => print_esc_cstr(b"newlinechar"),
        50 => print_esc_cstr(b"language"),
        51 => print_esc_cstr(b"lefthyphenmin"),
        52 => print_esc_cstr(b"righthyphenmin"),
        53 => print_esc_cstr(b"holdinginserts"),
        54 => print_esc_cstr(b"errorcontextlines"),
        55 => print_esc_cstr(b"charsubdefmin"),
        56 => print_esc_cstr(b"charsubdefmax"),
        57 => print_esc_cstr(b"tracingcharsubdef"),
        69 => print_esc_cstr(b"XeTeXlinebreakpenalty"),
        70 => print_esc_cstr(b"XeTeXprotrudechars"),
        83 => print_esc_cstr(b"synctex"),
        58 => print_esc_cstr(b"tracingassigns"),
        59 => print_esc_cstr(b"tracinggroups"),
        60 => print_esc_cstr(b"tracingifs"),
        61 => print_esc_cstr(b"tracingscantokens"),
        62 => print_esc_cstr(b"tracingnesting"),
        63 => print_esc_cstr(b"predisplaydirection"),
        64 => print_esc_cstr(b"lastlinefit"),
        65 => print_esc_cstr(b"savingvdiscards"),
        66 => print_esc_cstr(b"savinghyphcodes"),
        67 => print_esc_cstr(b"suppressfontnotfounderror"),
        71 => print_esc_cstr(b"TeXXeTstate"),
        73 => print_esc_cstr(b"XeTeXupwardsmode"),
        74 => print_esc_cstr(b"XeTeXuseglyphmetrics"),
        75 => print_esc_cstr(b"XeTeXinterchartokenstate"),
        72 => print_esc_cstr(b"XeTeXdashbreakstate"),
        76 => print_esc_cstr(b"XeTeXinputnormalization"),
        79 => print_esc_cstr(b"XeTeXtracingfonts"),
        80 => print_esc_cstr(b"XeTeXinterwordspaceshaping"),
        81 => print_esc_cstr(b"XeTeXgenerateactualtext"),
        82 => print_esc_cstr(b"XeTeXhyphenatablelength"),
        84 => print_esc_cstr(b"pdfoutput"),
        _ => print_cstr(b"[unknown i32 parameter!]"),
    };
}
pub(crate) unsafe fn begin_diagnostic() {
    old_setting = selector;
    if EQTB[(INT_BASE + 29i32) as usize].b32.s1 <= 0i32 && selector == Selector::TERM_AND_LOG {
        selector = (u8::from(selector) - 1).into();
        if history == TTHistory::SPOTLESS {
            history = TTHistory::WARNING_ISSUED
        }
    };
}
pub(crate) unsafe fn end_diagnostic(mut blank_line: bool) {
    print_nl_cstr(b"");
    if blank_line {
        print_ln();
    }
    selector = old_setting;
}
pub(crate) unsafe fn print_length_param(mut n: i32) {
    match n {
        0 => print_esc_cstr(b"parindent"),
        1 => print_esc_cstr(b"mathsurround"),
        2 => print_esc_cstr(b"lineskiplimit"),
        3 => print_esc_cstr(b"hsize"),
        4 => print_esc_cstr(b"vsize"),
        5 => print_esc_cstr(b"maxdepth"),
        6 => print_esc_cstr(b"splitmaxdepth"),
        7 => print_esc_cstr(b"boxmaxdepth"),
        8 => print_esc_cstr(b"hfuzz"),
        9 => print_esc_cstr(b"vfuzz"),
        10 => print_esc_cstr(b"delimitershortfall"),
        11 => print_esc_cstr(b"nulldelimiterspace"),
        12 => print_esc_cstr(b"scriptspace"),
        13 => print_esc_cstr(b"predisplaysize"),
        14 => print_esc_cstr(b"displaywidth"),
        15 => print_esc_cstr(b"displayindent"),
        16 => print_esc_cstr(b"overfullrule"),
        17 => print_esc_cstr(b"hangindent"),
        18 => print_esc_cstr(b"hoffset"),
        19 => print_esc_cstr(b"voffset"),
        20 => print_esc_cstr(b"emergencystretch"),
        21 => print_esc_cstr(b"pdfpagewidth"),
        22 => print_esc_cstr(b"pdfpageheight"),
        _ => print_cstr(b"[unknown dimen parameter!]"),
    };
}
pub(crate) unsafe fn print_cmd_chr(mut cmd: u16, mut chr_code: i32) {
    let mut n: i32 = 0;
    let mut font_name_str: str_number = 0;
    let mut quote_char: UTF16_code = 0;
    match cmd as i32 {
        1 => {
            print_cstr(b"begin-group character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        2 => {
            print_cstr(b"end-group character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        3 => {
            print_cstr(b"math shift character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        6 => {
            print_cstr(b"macro parameter character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        7 => {
            print_cstr(b"superscript character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        8 => {
            print_cstr(b"subscript character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        9 => print_cstr(b"end of alignment template"),
        10 => {
            print_cstr(b"blank space ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        11 => {
            print_cstr(b"the letter ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        12 => {
            print_cstr(b"the character ");
            if (chr_code as i64) < 65536 {
                print(chr_code);
            } else {
                print_char(chr_code);
            }
        }
        76 | 77 => {
            if chr_code
                < 1i32
                    + (0x10ffffi32 + 1i32)
                    + (0x10ffffi32 + 1i32)
                    + 1i32
                    + 15000i32
                    + 12i32
                    + 9000i32
                    + 1i32
                    + 1i32
                    + 19i32
            {
                print_skip_param(
                    chr_code
                        - (1i32
                            + (0x10ffffi32 + 1i32)
                            + (0x10ffffi32 + 1i32)
                            + 1i32
                            + 15000i32
                            + 12i32
                            + 9000i32
                            + 1i32
                            + 1i32),
                );
            } else if chr_code
                < 1i32
                    + (0x10ffffi32 + 1i32)
                    + (0x10ffffi32 + 1i32)
                    + 1i32
                    + 15000i32
                    + 12i32
                    + 9000i32
                    + 1i32
                    + 1i32
                    + 19i32
                    + 256i32
            {
                print_esc_cstr(b"skip");
                print_int(
                    chr_code
                        - (1i32
                            + (0x10ffffi32 + 1i32)
                            + (0x10ffffi32 + 1i32)
                            + 1i32
                            + 15000i32
                            + 12i32
                            + 9000i32
                            + 1i32
                            + 1i32
                            + 19i32),
                );
            } else {
                print_esc_cstr(b"muskip");
                print_int(
                    chr_code
                        - (1i32
                            + (0x10ffffi32 + 1i32)
                            + (0x10ffffi32 + 1i32)
                            + 1i32
                            + 15000i32
                            + 12i32
                            + 9000i32
                            + 1i32
                            + 1i32
                            + 19i32
                            + 256i32),
                );
            }
        }
        73 => {
            if chr_code >= LOCAL_BASE + 13i32 {
                print_esc_cstr(b"toks");
                print_int(chr_code - (LOCAL_BASE + 13i32));
            } else {
                match chr_code {
                    2252772 => print_esc_cstr(b"output"),
                    2252773 => print_esc_cstr(b"everypar"),
                    2252774 => print_esc_cstr(b"everymath"),
                    2252775 => print_esc_cstr(b"everydisplay"),
                    2252776 => print_esc_cstr(b"everyhbox"),
                    2252777 => print_esc_cstr(b"everyvbox"),
                    2252778 => print_esc_cstr(b"everyjob"),
                    2252779 => print_esc_cstr(b"everycr"),
                    2252781 => print_esc_cstr(b"everyeof"),
                    2252782 => print_esc_cstr(b"XeTeXinterchartoks"),
                    2252783 => print_esc_cstr(b"TectonicCodaTokens"),
                    _ => print_esc_cstr(b"errhelp"),
                }
            }
        }
        74 => {
            if chr_code < COUNT_BASE {
                print_param(chr_code - (INT_BASE));
            } else {
                print_esc_cstr(b"count");
                print_int(chr_code - (COUNT_BASE));
            }
        }
        75 => {
            if chr_code < DIMEN_BASE + 23i32 {
                print_length_param(chr_code - (DIMEN_BASE));
            } else {
                print_esc_cstr(b"dimen");
                print_int(chr_code - (DIMEN_BASE + 23i32));
            }
        }
        45 => print_esc_cstr(b"accent"),
        92 => print_esc_cstr(b"advance"),
        40 => print_esc_cstr(b"afterassignment"),
        41 => print_esc_cstr(b"aftergroup"),
        78 => print_esc_cstr(b"fontdimen"),
        61 => print_esc_cstr(b"begingroup"),
        42 => print_esc_cstr(b"penalty"),
        16 => print_esc_cstr(b"char"),
        109 => print_esc_cstr(b"csname"),
        90 => print_esc_cstr(b"font"),
        15 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"Udelimiter");
            } else {
                print_esc_cstr(b"delimiter");
            }
        }
        94 => print_esc_cstr(b"divide"),
        67 => print_esc_cstr(b"endcsname"),
        62 => print_esc_cstr(b"endgroup"),
        64 => print_esc(' ' as i32),
        104 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"expandafter");
            } else {
                print_esc_cstr(b"unless");
            }
        }
        32 => print_esc_cstr(b"halign"),
        36 => print_esc_cstr(b"hrule"),
        39 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"ignorespaces");
            } else {
                print_esc_cstr(b"primitive");
            }
        }
        37 => print_esc_cstr(b"insert"),
        44 => print_esc('/' as i32),
        18 => {
            print_esc_cstr(b"mark");
            if chr_code > 0i32 {
                print_char('s' as i32);
            }
        }
        46 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"Umathaccent");
            } else {
                print_esc_cstr(b"mathaccent");
            }
        }
        17 => {
            if chr_code == 2i32 {
                print_esc_cstr(b"Umathchar");
            } else if chr_code == 1i32 {
                print_esc_cstr(b"Umathcharnum");
            } else {
                print_esc_cstr(b"mathchar");
            }
        }
        54 => print_esc_cstr(b"mathchoice"),
        93 => print_esc_cstr(b"multiply"),
        34 => print_esc_cstr(b"noalign"),
        65 => print_esc_cstr(b"noboundary"),
        105 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"noexpand");
            } else {
                print_esc_cstr(b"primitive");
            }
        }
        55 => print_esc_cstr(b"nonscript"),
        63 => print_esc_cstr(b"omit"),
        66 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"Uradical");
            } else {
                print_esc_cstr(b"radical");
            }
        }
        98 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"read");
            } else {
                print_esc_cstr(b"readline");
            }
        }
        0 => print_esc_cstr(b"relax"),
        100 => print_esc_cstr(b"setbox"),
        81 => print_esc_cstr(b"prevgraf"),
        85 => match chr_code {
            2252771 => print_esc_cstr(b"parshape"),
            2253040 => print_esc_cstr(b"interlinepenalties"),
            2253041 => print_esc_cstr(b"clubpenalties"),
            2253042 => print_esc_cstr(b"widowpenalties"),
            2253043 => print_esc_cstr(b"displaywidowpenalties"),
            _ => {}
        },
        111 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"the");
            } else if chr_code == 1i32 {
                print_esc_cstr(b"unexpanded");
            } else {
                print_esc_cstr(b"detokenize");
            }
        }
        72 => {
            print_esc_cstr(b"toks");
            if chr_code != 0i32 {
                print_sa_num(chr_code);
            }
        }
        38 => print_esc_cstr(b"vadjust"),
        33 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"valign");
            } else {
                match chr_code {
                    6 => print_esc_cstr(b"beginL"),
                    7 => print_esc_cstr(b"endL"),
                    10 => print_esc_cstr(b"beginR"),
                    _ => print_esc_cstr(b"endR"),
                }
            }
        }
        56 => print_esc_cstr(b"vcenter"),
        35 => print_esc_cstr(b"vrule"),
        13 => print_esc_cstr(b"par"),
        106 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"input");
            } else if chr_code == 2i32 {
                print_esc_cstr(b"scantokens");
            } else {
                print_esc_cstr(b"endinput");
            }
        }
        112 => {
            match chr_code % 5i32 {
                1 => print_esc_cstr(b"firstmark"),
                2 => print_esc_cstr(b"botmark"),
                3 => print_esc_cstr(b"splitfirstmark"),
                4 => print_esc_cstr(b"splitbotmark"),
                _ => print_esc_cstr(b"topmark"),
            }
            if chr_code >= 5i32 {
                print_char('s' as i32);
            }
        }
        91 => {
            if chr_code < 0i32 || chr_code > 19i32 {
                /*lo_mem_stat_max*/
                cmd = (MEM[chr_code as usize].b16.s1 as i32 / 64) as u16
            } else {
                cmd = chr_code as u16;
                chr_code = TEX_NULL
            }
            if cmd as i32 == 0i32 {
                print_esc_cstr(b"count");
            } else if cmd as i32 == 1i32 {
                print_esc_cstr(b"dimen");
            } else if cmd as i32 == 2i32 {
                print_esc_cstr(b"skip");
            } else {
                print_esc_cstr(b"muskip");
            }
            if chr_code != TEX_NULL {
                print_sa_num(chr_code);
            }
        }
        80 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"prevdepth");
            } else {
                print_esc_cstr(b"spacefactor");
            }
        }
        83 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"deadcycles");
            } else if chr_code == 2i32 {
                print_esc_cstr(b"interactionmode");
            } else {
                print_esc_cstr(b"insertpenalties");
            }
        }
        84 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"wd");
            } else if chr_code == 3i32 {
                print_esc_cstr(b"ht");
            } else {
                print_esc_cstr(b"dp");
            }
        }
        71 => match chr_code {
            0 => print_esc_cstr(b"lastpenalty"),
            1 => print_esc_cstr(b"lastkern"),
            2 => print_esc_cstr(b"lastskip"),
            4 => print_esc_cstr(b"inputlineno"),
            45 => print_esc_cstr(b"shellescape"),
            3 => print_esc_cstr(b"lastnodetype"),
            6 => print_esc_cstr(b"eTeXversion"),
            14 => print_esc_cstr(b"XeTeXversion"),
            15 => print_esc_cstr(b"XeTeXcountglyphs"),
            16 => print_esc_cstr(b"XeTeXcountvariations"),
            17 => print_esc_cstr(b"XeTeXvariation"),
            18 => print_esc_cstr(b"XeTeXfindvariationbyname"),
            19 => print_esc_cstr(b"XeTeXvariationmin"),
            20 => print_esc_cstr(b"XeTeXvariationmax"),
            21 => print_esc_cstr(b"XeTeXvariationdefault"),
            22 => print_esc_cstr(b"XeTeXcountfeatures"),
            23 => print_esc_cstr(b"XeTeXfeaturecode"),
            24 => print_esc_cstr(b"XeTeXfindfeaturebyname"),
            25 => print_esc_cstr(b"XeTeXisexclusivefeature"),
            26 => print_esc_cstr(b"XeTeXcountselectors"),
            27 => print_esc_cstr(b"XeTeXselectorcode"),
            28 => print_esc_cstr(b"XeTeXfindselectorbyname"),
            29 => print_esc_cstr(b"XeTeXisdefaultselector"),
            30 => print_esc_cstr(b"XeTeXOTcountscripts"),
            31 => print_esc_cstr(b"XeTeXOTcountlanguages"),
            32 => print_esc_cstr(b"XeTeXOTcountfeatures"),
            33 => print_esc_cstr(b"XeTeXOTscripttag"),
            34 => print_esc_cstr(b"XeTeXOTlanguagetag"),
            35 => print_esc_cstr(b"XeTeXOTfeaturetag"),
            36 => print_esc_cstr(b"XeTeXcharglyph"),
            37 => print_esc_cstr(b"XeTeXglyphindex"),
            47 => print_esc_cstr(b"XeTeXglyphbounds"),
            38 => print_esc_cstr(b"XeTeXfonttype"),
            39 => print_esc_cstr(b"XeTeXfirstfontchar"),
            40 => print_esc_cstr(b"XeTeXlastfontchar"),
            41 => print_esc_cstr(b"pdflastxpos"),
            42 => print_esc_cstr(b"pdflastypos"),
            46 => print_esc_cstr(b"XeTeXpdfpagecount"),
            7 => print_esc_cstr(b"currentgrouplevel"),
            8 => print_esc_cstr(b"currentgrouptype"),
            9 => print_esc_cstr(b"currentiflevel"),
            10 => print_esc_cstr(b"currentiftype"),
            11 => print_esc_cstr(b"currentifbranch"),
            48 => print_esc_cstr(b"fontcharwd"),
            49 => print_esc_cstr(b"fontcharht"),
            50 => print_esc_cstr(b"fontchardp"),
            51 => print_esc_cstr(b"fontcharic"),
            52 => print_esc_cstr(b"parshapelength"),
            53 => print_esc_cstr(b"parshapeindent"),
            54 => print_esc_cstr(b"parshapedimen"),
            59 => print_esc_cstr(b"numexpr"),
            60 => print_esc_cstr(b"dimexpr"),
            61 => print_esc_cstr(b"glueexpr"),
            62 => print_esc_cstr(b"muexpr"),
            12 => print_esc_cstr(b"gluestretchorder"),
            13 => print_esc_cstr(b"glueshrinkorder"),
            55 => print_esc_cstr(b"gluestretch"),
            56 => print_esc_cstr(b"glueshrink"),
            57 => print_esc_cstr(b"mutoglue"),
            58 => print_esc_cstr(b"gluetomu"),
            _ => print_esc_cstr(b"badness"),
        },
        110 => match chr_code {
            0 => print_esc_cstr(b"number"),
            1 => print_esc_cstr(b"romannumeral"),
            2 => print_esc_cstr(b"string"),
            3 => print_esc_cstr(b"meaning"),
            4 => print_esc_cstr(b"fontname"),
            43 => print_esc_cstr(b"strcmp"),
            44 => print_esc_cstr(b"mdfivesum"),
            11 => print_esc_cstr(b"leftmarginkern"),
            12 => print_esc_cstr(b"rightmarginkern"),
            5 => print_esc_cstr(b"eTeXrevision"),
            6 => print_esc_cstr(b"XeTeXrevision"),
            7 => print_esc_cstr(b"XeTeXvariationname"),
            8 => print_esc_cstr(b"XeTeXfeaturename"),
            9 => print_esc_cstr(b"XeTeXselectorname"),
            10 => print_esc_cstr(b"XeTeXglyphname"),
            13 => print_esc_cstr(b"Uchar"),
            14 => print_esc_cstr(b"Ucharcat"),
            _ => print_esc_cstr(b"jobname"),
        },
        107 => {
            if chr_code >= 32i32 {
                print_esc_cstr(b"unless");
            }
            match chr_code % 32i32 {
                1 => print_esc_cstr(b"ifcat"),
                2 => print_esc_cstr(b"ifnum"),
                3 => print_esc_cstr(b"ifdim"),
                4 => print_esc_cstr(b"ifodd"),
                5 => print_esc_cstr(b"ifvmode"),
                6 => print_esc_cstr(b"ifhmode"),
                7 => print_esc_cstr(b"ifmmode"),
                8 => print_esc_cstr(b"ifinner"),
                9 => print_esc_cstr(b"ifvoid"),
                10 => print_esc_cstr(b"ifhbox"),
                11 => print_esc_cstr(b"ifvbox"),
                12 => print_esc_cstr(b"ifx"),
                13 => print_esc_cstr(b"ifeof"),
                14 => print_esc_cstr(b"iftrue"),
                15 => print_esc_cstr(b"iffalse"),
                16 => print_esc_cstr(b"ifcase"),
                21 => print_esc_cstr(b"ifprimitive"),
                17 => print_esc_cstr(b"ifdefined"),
                18 => print_esc_cstr(b"ifcsname"),
                19 => print_esc_cstr(b"iffontchar"),
                20 => print_esc_cstr(b"ifincsname"),
                _ => print_esc_cstr(b"if"),
            }
        }
        108 => {
            if chr_code == 2i32 {
                print_esc_cstr(b"fi");
            } else if chr_code == 4i32 {
                print_esc_cstr(b"or");
            } else {
                print_esc_cstr(b"else");
            }
        }
        4 => {
            if chr_code == 0x10ffffi32 + 2i32 {
                print_esc_cstr(b"span");
            } else {
                print_cstr(b"alignment tab character ");
                if (chr_code as i64) < 65536 {
                    print(chr_code);
                } else {
                    print_char(chr_code);
                }
            }
        }
        5 => {
            if chr_code == 0x10ffffi32 + 3i32 {
                print_esc_cstr(b"cr");
            } else {
                print_esc_cstr(b"crcr");
            }
        }
        82 => {
            match chr_code {
                0 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pagegoal");
                }
                1 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pagetotal");
                }
                2 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pagestretch");
                }
                3 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pagefilstretch");
                }
                4 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pagefillstretch");
                }
                5 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pagefilllstretch");
                }
                6 => {
                    /* genuine literal in WEB */
                    print_esc_cstr(b"pageshrink");
                }
                _ => print_esc_cstr(b"pagedepth"),
            }
        }
        14 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"dump");
            } else {
                print_esc_cstr(b"end");
            }
        }
        26 => match chr_code {
            4 => print_esc_cstr(b"hskip"),
            0 => print_esc_cstr(b"hfil"),
            1 => print_esc_cstr(b"hfill"),
            2 => print_esc_cstr(b"hss"),
            _ => print_esc_cstr(b"hfilneg"),
        },
        27 => match chr_code {
            4 => print_esc_cstr(b"vskip"),
            0 => print_esc_cstr(b"vfil"),
            1 => print_esc_cstr(b"vfill"),
            2 => print_esc_cstr(b"vss"),
            _ => print_esc_cstr(b"vfilneg"),
        },
        28 => print_esc_cstr(b"mskip"),
        29 => print_esc_cstr(b"kern"),
        30 => print_esc_cstr(b"mkern"),
        21 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"moveleft");
            } else {
                print_esc_cstr(b"moveright");
            }
        }
        22 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"raise");
            } else {
                print_esc_cstr(b"lower");
            }
        }
        20 => match chr_code {
            0 => print_esc_cstr(b"box"),
            1 => print_esc_cstr(b"copy"),
            2 => print_esc_cstr(b"lastbox"),
            3 => print_esc_cstr(b"vsplit"),
            4 => print_esc_cstr(b"vtop"),
            5 => print_esc_cstr(b"vbox"),
            _ => print_esc_cstr(b"hbox"),
        },
        31 => {
            if chr_code == 100i32 {
                print_esc_cstr(b"leaders");
            } else if chr_code == 101i32 {
                print_esc_cstr(b"cleaders");
            } else if chr_code == 102i32 {
                print_esc_cstr(b"xleaders");
            } else {
                print_esc_cstr(b"shipout");
            }
        }
        43 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"noindent");
            } else {
                print_esc_cstr(b"indent");
            }
        }
        25 => {
            if chr_code == 10i32 {
                print_esc_cstr(b"unskip");
            } else if chr_code == 11i32 {
                print_esc_cstr(b"unkern");
            } else {
                print_esc_cstr(b"unpenalty");
            }
        }
        23 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"unhcopy");
            } else {
                print_esc_cstr(b"unhbox");
            }
        }
        24 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"unvcopy");
            } else if chr_code == 2i32 {
                print_esc_cstr(b"pagediscards");
            } else if chr_code == 3i32 {
                print_esc_cstr(b"splitdiscards");
            } else {
                print_esc_cstr(b"unvbox");
            }
        }
        47 => {
            if chr_code == 1i32 {
                print_esc('-' as i32);
            } else {
                print_esc_cstr(b"discretionary");
            }
        }
        48 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"leqno");
            } else {
                print_esc_cstr(b"eqno");
            }
        }
        50 => match chr_code {
            16 => print_esc_cstr(b"mathord"),
            17 => print_esc_cstr(b"mathop"),
            18 => print_esc_cstr(b"mathbin"),
            19 => print_esc_cstr(b"mathrel"),
            20 => print_esc_cstr(b"mathopen"),
            21 => print_esc_cstr(b"mathclose"),
            22 => print_esc_cstr(b"mathpunct"),
            23 => print_esc_cstr(b"mathinner"),
            26 => print_esc_cstr(b"underline"),
            _ => print_esc_cstr(b"overline"),
        },
        51 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"limits");
            } else if chr_code == 2i32 {
                print_esc_cstr(b"nolimits");
            } else {
                print_esc_cstr(b"displaylimits");
            }
        }
        53 => print_style(chr_code),
        52 => match chr_code {
            1 => print_esc_cstr(b"over"),
            2 => print_esc_cstr(b"atop"),
            3 => print_esc_cstr(b"abovewithdelims"),
            4 => print_esc_cstr(b"overwithdelims"),
            5 => print_esc_cstr(b"atopwithdelims"),
            _ => print_esc_cstr(b"above"),
        },
        49 => {
            if chr_code == 30i32 {
                print_esc_cstr(b"left");
            } else if chr_code == 1i32 {
                print_esc_cstr(b"middle");
            } else {
                print_esc_cstr(b"right");
            }
        }
        95 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"long");
            } else if chr_code == 2i32 {
                print_esc_cstr(b"outer");
            } else if chr_code == 8i32 {
                print_esc_cstr(b"protected");
            } else {
                print_esc_cstr(b"global");
            }
        }
        99 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"def");
            } else if chr_code == 1i32 {
                print_esc_cstr(b"gdef");
            } else if chr_code == 2i32 {
                print_esc_cstr(b"edef");
            } else {
                print_esc_cstr(b"xdef");
            }
        }
        96 => {
            if chr_code != 0i32 {
                print_esc_cstr(b"futurelet");
            } else {
                print_esc_cstr(b"let");
            }
        }
        97 => match chr_code {
            0 => print_esc_cstr(b"chardef"),
            1 => print_esc_cstr(b"mathchardef"),
            9 => print_esc_cstr(b"Umathchardef"),
            8 => print_esc_cstr(b"Umathcharnumdef"),
            2 => print_esc_cstr(b"countdef"),
            3 => print_esc_cstr(b"dimendef"),
            4 => print_esc_cstr(b"skipdef"),
            5 => print_esc_cstr(b"muskipdef"),
            7 => print_esc_cstr(b"charsubdef"),
            _ => print_esc_cstr(b"toksdef"),
        },
        68 => {
            print_esc_cstr(b"char");
            print_hex(chr_code);
        }
        69 => {
            print_esc_cstr(b"mathchar");
            print_hex(chr_code);
        }
        70 => {
            print_esc_cstr(b"Umathchar");
            print_hex((chr_code as u32 >> 21i32 & 0x7_u32) as i32);
            print_hex((chr_code as u32 >> 24i32 & 0xff_u32) as i32);
            print_hex((chr_code as u32 & 0x1fffff_u32) as i32);
        }
        86 => {
            if chr_code == MATH_FONT_BASE + 3i32 * 256i32 {
                print_esc_cstr(b"catcode");
            } else if chr_code == MATH_CODE_BASE {
                print_esc_cstr(b"mathcode");
            } else if chr_code == MATH_FONT_BASE + 3i32 * 256i32 + (0x10ffffi32 + 1i32) {
                print_esc_cstr(b"lccode");
            } else if chr_code
                == MATH_FONT_BASE + 3i32 * 256i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32)
            {
                print_esc_cstr(b"uccode");
            } else if chr_code == SF_CODE_BASE {
                print_esc_cstr(b"sfcode");
            } else {
                print_esc_cstr(b"delcode");
            }
        }
        87 => {
            if chr_code == SF_CODE_BASE {
                print_esc_cstr(b"XeTeXcharclass");
            } else if chr_code == MATH_CODE_BASE {
                print_esc_cstr(b"Umathcodenum");
            } else if chr_code == MATH_CODE_BASE + 1i32 {
                print_esc_cstr(b"Umathcode");
            } else if chr_code == DEL_CODE_BASE {
                print_esc_cstr(b"Udelcodenum");
            } else {
                print_esc_cstr(b"Udelcode");
            }
        }
        88 => print_size(chr_code - (MATH_FONT_BASE)),
        101 => {
            if chr_code == 1i32 {
                print_esc_cstr(b"patterns");
            } else {
                print_esc_cstr(b"hyphenation");
            }
        }
        79 => match chr_code {
            0 => print_esc_cstr(b"hyphenchar"),
            1 => print_esc_cstr(b"skewchar"),
            2 => print_esc_cstr(b"lpcode"),
            3 => print_esc_cstr(b"rpcode"),
            _ => {}
        },
        89 => {
            print_cstr(b"select font ");
            font_name_str = FONT_NAME[chr_code as usize];
            if FONT_AREA[chr_code as usize] as u32 == 0xffffu32
                || FONT_AREA[chr_code as usize] as u32 == 0xfffeu32
            {
                let mut for_end: i32 = length(font_name_str) - 1i32;
                quote_char = '\"' as i32 as UTF16_code;
                n = 0i32;
                while n <= for_end {
                    if *str_pool.offset(
                        (*str_start.offset((font_name_str as i64 - 65536) as isize) + n) as isize,
                    ) as i32
                        == '\"' as i32
                    {
                        quote_char = '\'' as i32 as UTF16_code
                    }
                    n += 1
                }
                print_char(quote_char as i32);
                print(font_name_str);
                print_char(quote_char as i32);
            } else {
                print(font_name_str);
            }
            if FONT_SIZE[chr_code as usize] != FONT_DSIZE[chr_code as usize] {
                print_cstr(b" at ");
                print_scaled(FONT_SIZE[chr_code as usize]);
                print_cstr(b"pt");
            }
        }
        102 => match chr_code {
            0 => print_esc_cstr(b"batchmode"),
            1 => print_esc_cstr(b"nonstopmode"),
            2 => print_esc_cstr(b"scrollmode"),
            _ => print_esc_cstr(b"errorstopmode"),
        },
        60 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"closein");
            } else {
                print_esc_cstr(b"openin");
            }
        }
        58 => {
            if chr_code == 0i32 {
                print_esc_cstr(b"message");
            } else {
                print_esc_cstr(b"errmessage");
            }
        }
        57 => {
            if chr_code == MATH_FONT_BASE + 3i32 * 256i32 + (0x10ffffi32 + 1i32) {
                print_esc_cstr(b"lowercase");
            } else {
                print_esc_cstr(b"uppercase");
            }
        }
        19 => match chr_code {
            1 => print_esc_cstr(b"showbox"),
            2 => print_esc_cstr(b"showthe"),
            3 => print_esc_cstr(b"showlists"),
            4 => print_esc_cstr(b"showgroups"),
            5 => print_esc_cstr(b"showtokens"),
            6 => print_esc_cstr(b"showifs"),
            _ => print_esc_cstr(b"show"),
        },
        103 => print_cstr(b"undefined"),
        113 | 114 | 115 | 116 => {
            n = cmd as i32 - 113i32;
            if MEM[MEM[chr_code as usize].b32.s1 as usize].b32.s0 == 0x1c00000 + 1 {
                n = n + 4i32
            }
            if n / 4i32 & 1i32 != 0 {
                print_esc_cstr(b"protected");
            }
            if n & 1i32 != 0 {
                print_esc_cstr(b"long");
            }
            if n / 2i32 & 1i32 != 0 {
                print_esc_cstr(b"outer");
            }
            if n > 0i32 {
                print_char(' ' as i32);
            }
            print_cstr(b"macro");
        }
        117 => print_esc_cstr(b"outer endtemplate"),
        59 => match chr_code {
            0 => print_esc_cstr(b"openout"),
            1 => print_esc_cstr(b"write"),
            2 => print_esc_cstr(b"closeout"),
            3 => print_esc_cstr(b"special"),
            4 => print_esc_cstr(b"immediate"),
            5 => print_esc_cstr(b"setlanguage"),
            41 => print_esc_cstr(b"XeTeXpicfile"),
            42 => print_esc_cstr(b"XeTeXpdffile"),
            43 => print_esc_cstr(b"XeTeXglyph"),
            46 => print_esc_cstr(b"XeTeXlinebreaklocale"),
            44 => print_esc_cstr(b"XeTeXinputencoding"),
            45 => print_esc_cstr(b"XeTeXdefaultencoding"),
            6 => print_esc_cstr(b"pdfsavepos"),
            _ => print_cstr(b"[unknown extension!]"),
        },
        _ => print_cstr(b"[unknown command code!]"),
    };
}
pub(crate) unsafe fn not_aat_font_error(mut cmd: i32, mut c: i32, mut f: i32) {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Cannot use ");
    print_cmd_chr(cmd as u16, c);
    print_cstr(b" with ");
    print(FONT_NAME[f as usize]);
    print_cstr(b"; not an AAT font");
    error();
}
pub(crate) unsafe fn not_aat_gr_font_error(mut cmd: i32, mut c: i32, mut f: i32) {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Cannot use ");
    print_cmd_chr(cmd as u16, c);
    print_cstr(b" with ");
    print(FONT_NAME[f as usize]);
    print_cstr(b"; not an AAT or Graphite font");
    error();
}
pub(crate) unsafe fn not_ot_font_error(mut cmd: i32, mut c: i32, mut f: i32) {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Cannot use ");
    print_cmd_chr(cmd as u16, c);
    print_cstr(b" with ");
    print(FONT_NAME[f as usize]);
    print_cstr(b"; not an OpenType Layout font");
    error();
}
pub(crate) unsafe fn not_native_font_error(mut cmd: i32, mut c: i32, mut f: i32) {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Cannot use ");
    print_cmd_chr(cmd as u16, c);
    print_cstr(b" with ");
    print(FONT_NAME[f as usize]);
    print_cstr(b"; not a native platform font");
    error();
}
/*:1434*/
pub(crate) unsafe fn id_lookup(mut j: i32, mut l: i32) -> i32 {
    let mut h: i32 = 0; /*269:*/
    let mut d: i32 = 0;
    let mut p: i32 = 0;
    let mut k: i32 = 0;
    let mut ll: i32 = 0;
    h = 0i32;
    k = j;
    while k <= j + l - 1i32 {
        h = h + h + *buffer.offset(k as isize);
        while h >= 8501i32 {
            h = h - 8501i32
        }
        k += 1
    }
    p = h + (1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) + 1i32);
    ll = l;
    d = 0i32;
    while d <= l - 1i32 {
        if *buffer.offset((j + d) as isize) as i64 >= 65536 {
            ll += 1
        }
        d += 1
    }
    loop {
        if (*hash.offset(p as isize)).s1 > 0i32 {
            if length((*hash.offset(p as isize)).s1) == ll {
                if str_eq_buf((*hash.offset(p as isize)).s1, j) {
                    break;
                }
            }
        }
        if (*hash.offset(p as isize)).s0 == 0i32 {
            if no_new_control_sequence {
                p = 1i32
                    + (0x10ffffi32 + 1i32)
                    + (0x10ffffi32 + 1i32)
                    + 1i32
                    + 15000i32
                    + 12i32
                    + 9000i32
                    + 1i32
            } else {
                if (*hash.offset(p as isize)).s1 > 0i32 {
                    if hash_high < hash_extra {
                        hash_high += 1;
                        (*hash.offset(p as isize)).s0 =
                            hash_high + (DIMEN_BASE + 23i32 + 256i32 - 1i32);
                        p = hash_high + (DIMEN_BASE + 23i32 + 256i32 - 1i32)
                    } else {
                        loop {
                            if hash_used
                                == 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) + 1i32
                            {
                                overflow(b"hash size", 15000i32 + hash_extra);
                            }
                            hash_used -= 1;
                            if !((*hash.offset(hash_used as isize)).s1 != 0i32) {
                                break;
                            }
                        }
                        (*hash.offset(p as isize)).s0 = hash_used;
                        p = hash_used
                    }
                }
                if pool_ptr + ll > pool_size {
                    overflow(b"pool size", pool_size - init_pool_ptr);
                }
                d = cur_length();
                while pool_ptr > *str_start.offset((str_ptr - 65536i32) as isize) {
                    pool_ptr -= 1;
                    *str_pool.offset((pool_ptr + l) as isize) = *str_pool.offset(pool_ptr as isize)
                }
                k = j;
                while k <= j + l - 1i32 {
                    if (*buffer.offset(k as isize) as i64) < 65536 {
                        *str_pool.offset(pool_ptr as isize) =
                            *buffer.offset(k as isize) as packed_UTF16_code;
                        pool_ptr += 1
                    } else {
                        *str_pool.offset(pool_ptr as isize) = (0xd800i32 as i64
                            + (*buffer.offset(k as isize) as i64 - 65536) / 1024i32 as i64)
                            as packed_UTF16_code;
                        pool_ptr += 1;
                        *str_pool.offset(pool_ptr as isize) = (0xdc00i32 as i64
                            + (*buffer.offset(k as isize) as i64 - 65536) % 1024i32 as i64)
                            as packed_UTF16_code;
                        pool_ptr += 1
                    }
                    k += 1
                }
                (*hash.offset(p as isize)).s1 = make_string();
                pool_ptr += d
            }
            break;
        } else {
            p = (*hash.offset(p as isize)).s0
        }
    }
    p
}
pub(crate) unsafe fn prim_lookup(mut s: str_number) -> i32 {
    let mut current_block: u64;
    let mut h: i32 = 0;
    let mut p: i32 = 0;
    let mut k: i32 = 0;
    let mut j: i32 = 0;
    let mut l: i32 = 0i32;
    if s <= 0xffffi32 {
        if s < 0i32 {
            p = 0i32;
            current_block = 12583739755984661121;
        } else {
            p = s % 431i32 + 1i32;
            current_block = 11307063007268554308;
        }
    } else {
        j = *str_start.offset((s as i64 - 65536) as isize);
        if s == str_ptr {
            l = cur_length()
        } else {
            l = length(s)
        }
        h = *str_pool.offset(j as isize) as i32;
        let mut for_end: i32 = 0;
        k = j + 1i32;
        for_end = j + l - 1i32;
        if k <= for_end {
            loop {
                h = h + h + *str_pool.offset(k as isize) as i32;
                while h >= 431i32 {
                    h = h - 431i32
                }
                let fresh14 = k;
                k = k + 1;
                if !(fresh14 < for_end) {
                    break;
                }
            }
        }
        p = h + 1i32;
        current_block = 11307063007268554308;
    }
    loop {
        match current_block {
            12583739755984661121 => return p,
            _ => {
                if prim[p as usize].s1 as i64 > 65536 {
                    if length(prim[p as usize].s1) - 1i32 == l {
                        if str_eq_str(prim[p as usize].s1 - 1i32, s) {
                            current_block = 12583739755984661121;
                            continue;
                        }
                    }
                } else if prim[p as usize].s1 == 1i32 + s {
                    current_block = 12583739755984661121;
                    continue;
                }
                if prim[p as usize].s0 == 0i32 {
                    if no_new_control_sequence {
                        p = 0i32
                    } else {
                        /*272:*/
                        if prim[p as usize].s1 > 0i32 {
                            loop {
                                if prim_used == 1i32 {
                                    overflow(b"primitive size", 500i32);
                                }
                                prim_used -= 1;
                                if prim[prim_used as usize].s1 == 0i32 {
                                    break;
                                }
                            }
                            prim[p as usize].s0 = prim_used;
                            p = prim_used
                        }
                        prim[p as usize].s1 = s + 1i32
                    }
                    current_block = 12583739755984661121;
                } else {
                    p = prim[p as usize].s0;
                    current_block = 11307063007268554308;
                }
            }
        }
    }
}
/*:276*/
/*280: *//*296: */
pub(crate) unsafe fn print_group(mut e: bool) {
    match cur_group as i32 {
        0 => {
            print_cstr(b"bottom level");
            return;
        }
        1 | 14 => {
            if cur_group as i32 == 14i32 {
                print_cstr(b"semi ");
            }
            print_cstr(b"simple");
        }
        2 | 3 => {
            if cur_group as i32 == 3i32 {
                print_cstr(b"adjusted ");
            }
            print_cstr(b"hbox");
        }
        4 => print_cstr(b"vbox"),
        5 => print_cstr(b"vtop"),
        6 | 7 => {
            if cur_group as i32 == 7i32 {
                print_cstr(b"no ");
            }
            print_cstr(b"align");
        }
        8 => print_cstr(b"output"),
        10 => print_cstr(b"disc"),
        11 => print_cstr(b"insert"),
        12 => print_cstr(b"vcenter"),
        9 | 13 | 15 | 16 => {
            print_cstr(b"math");
            if cur_group as i32 == 13i32 {
                print_cstr(b" choice");
            } else if cur_group as i32 == 15i32 {
                print_cstr(b" shift");
            } else if cur_group as i32 == 16i32 {
                print_cstr(b" left");
            }
        }
        _ => {}
    }
    print_cstr(b" group (level ");
    print_int(cur_level as i32);
    print_char(')' as i32);
    if SAVE_STACK[SAVE_PTR - 1].b32.s1 != 0i32 {
        if e {
            print_cstr(b" entered at line ");
        } else {
            print_cstr(b" at line ");
        }
        print_int(SAVE_STACK[SAVE_PTR - 1].b32.s1);
    };
}
/*:1448*/
/*1449: */
pub(crate) unsafe fn pseudo_input() -> bool {
    let mut p: i32 = 0;
    let mut sz: i32 = 0;
    let mut w: b16x4 = b16x4 {
        s0: 0,
        s1: 0,
        s2: 0,
        s3: 0,
    };
    let mut r: i32 = 0;
    last = first;
    p = MEM[pseudo_files as usize].b32.s0;
    if p == TEX_NULL {
        false
    } else {
        MEM[pseudo_files as usize].b32.s0 = MEM[p as usize].b32.s1;
        sz = MEM[p as usize].b32.s0;
        if 4i32 * sz - 3i32 >= buf_size - last {
            /*35: */
            cur_input.loc = first;
            cur_input.limit = last - 1i32;
            overflow(b"buffer size", buf_size);
        }
        last = first;
        let mut for_end: i32 = 0;
        r = p + 1i32;
        for_end = p + sz - 1i32;
        if r <= for_end {
            loop {
                w = MEM[r as usize].b16;
                *buffer.offset(last as isize) = w.s3 as UnicodeScalar;
                *buffer.offset((last + 1i32) as isize) = w.s2 as UnicodeScalar;
                *buffer.offset((last + 2i32) as isize) = w.s1 as UnicodeScalar;
                *buffer.offset((last + 3i32) as isize) = w.s0 as UnicodeScalar;
                last = last + 4i32;
                let fresh15 = r;
                r = r + 1;
                if !(fresh15 < for_end) {
                    break;
                }
            }
        }
        if last >= max_buf_stack {
            max_buf_stack = last + 1i32
        }
        while last > first && *buffer.offset((last - 1i32) as isize) == ' ' as i32 {
            last -= 1
        }
        free_node(p, sz);
        true
    }
}
pub(crate) unsafe fn pseudo_close() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    p = MEM[pseudo_files as usize].b32.s1;
    q = MEM[pseudo_files as usize].b32.s0;
    MEM[pseudo_files as usize].b32.s1 = avail;
    avail = pseudo_files;
    pseudo_files = p;
    while q != TEX_NULL {
        p = q;
        q = MEM[p as usize].b32.s1;
        free_node(p, MEM[p as usize].b32.s0);
    }
}
pub(crate) unsafe fn group_warning() {
    let mut w: bool = false;
    BASE_PTR = INPUT_PTR;
    INPUT_STACK[BASE_PTR] = cur_input;
    let mut i = IN_OPEN;
    w = false;
    while GRP_STACK[i] == cur_boundary && i > 0 {
        if EQTB[(INT_BASE + 62i32) as usize].b32.s1 > 0i32 {
            while INPUT_STACK[BASE_PTR].state as i32 == 0i32
                || INPUT_STACK[BASE_PTR].index as usize > i
            {
                BASE_PTR -= 1;
            }
            if INPUT_STACK[BASE_PTR].name > 17i32 {
                w = true
            }
        }
        GRP_STACK[i] = SAVE_STACK[SAVE_PTR].b32.s1;
        i -= 1;
    }
    if w {
        print_nl_cstr(b"Warning: end of ");
        print_group(1i32 != 0);
        print_cstr(b" of a different file");
        print_ln();
        if EQTB[(INT_BASE + 62i32) as usize].b32.s1 > 1i32 {
            show_context();
        }
        if history == TTHistory::SPOTLESS {
            history = TTHistory::WARNING_ISSUED
        }
    };
}
pub(crate) unsafe fn if_warning() {
    let mut w: bool = false;
    BASE_PTR = INPUT_PTR;
    INPUT_STACK[BASE_PTR] = cur_input;
    let mut i = IN_OPEN;
    w = false;
    while IF_STACK[i] == cond_ptr {
        if EQTB[(INT_BASE + 62i32) as usize].b32.s1 > 0i32 {
            while INPUT_STACK[BASE_PTR].state as i32 == 0i32
                || INPUT_STACK[BASE_PTR].index as usize > i
            {
                BASE_PTR -= 1
            }
            if INPUT_STACK[BASE_PTR].name > 17i32 {
                w = true
            }
        }
        IF_STACK[i] = MEM[cond_ptr as usize].b32.s1;
        i -= 1;
    }
    if w {
        print_nl_cstr(b"Warning: end of ");
        print_cmd_chr(107_u16, cur_if as i32);
        if if_line != 0i32 {
            print_cstr(b" entered on line ");
            print_int(if_line);
        }
        print_cstr(b" of a different file");
        print_ln();
        if EQTB[(INT_BASE + 62i32) as usize].b32.s1 > 1i32 {
            show_context();
        }
        if history == TTHistory::SPOTLESS {
            history = TTHistory::WARNING_ISSUED
        }
    };
}
pub(crate) unsafe fn file_warning() {
    let mut p: i32 = 0;
    let mut l: u16 = 0;
    let mut c: u16 = 0;
    let mut i: i32 = 0;
    p = SAVE_PTR as i32;
    l = cur_level;
    c = cur_group as u16;
    SAVE_PTR = cur_boundary as usize;
    while GRP_STACK[IN_OPEN] != SAVE_PTR as i32 {
        cur_level = cur_level.wrapping_sub(1);
        print_nl_cstr(b"Warning: end of file when ");
        print_group(1i32 != 0);
        print_cstr(b" is incomplete");
        cur_group = SAVE_STACK[SAVE_PTR].b16.s0 as group_code;
        SAVE_PTR = SAVE_STACK[SAVE_PTR].b32.s1 as usize
    }
    SAVE_PTR = p as usize;
    cur_level = l;
    cur_group = c as group_code;
    p = cond_ptr;
    l = if_limit as u16;
    c = cur_if as u16;
    i = if_line;
    while IF_STACK[IN_OPEN] != cond_ptr {
        print_nl_cstr(b"Warning: end of file when ");
        print_cmd_chr(107_u16, cur_if as i32);
        if if_limit as i32 == 2i32 {
            print_esc_cstr(b"else");
        }
        if if_line != 0i32 {
            print_cstr(b" entered on line ");
            print_int(if_line);
        }
        print_cstr(b" is incomplete");
        if_line = MEM[(cond_ptr + 1) as usize].b32.s1;
        cur_if = MEM[cond_ptr as usize].b16.s0 as small_number;
        if_limit = MEM[cond_ptr as usize].b16.s1 as u8;
        cond_ptr = MEM[cond_ptr as usize].b32.s1
    }
    cond_ptr = p;
    if_limit = l as u8;
    cur_if = c as small_number;
    if_line = i;
    print_ln();
    if EQTB[(INT_BASE + 62i32) as usize].b32.s1 > 1i32 {
        show_context();
    }
    if history == TTHistory::SPOTLESS {
        history = TTHistory::WARNING_ISSUED
    };
}
pub(crate) unsafe fn delete_sa_ref(mut q: i32) {
    let mut p: i32 = 0;
    let mut i: small_number = 0;
    let mut s: small_number = 0;
    MEM[(q + 1) as usize].b32.s0 -= 1;
    if MEM[(q + 1) as usize].b32.s0 != TEX_NULL {
        return;
    }
    if (MEM[q as usize].b16.s1 as i32) < 128 {
        if MEM[(q + 2) as usize].b32.s1 == 0 {
            s = 3i32 as small_number
        } else {
            return;
        }
    } else {
        if (MEM[q as usize].b16.s1 as i32) < 256 {
            if MEM[(q + 1) as usize].b32.s1 == 0 {
                delete_glue_ref(0i32);
            } else {
                return;
            }
        } else if MEM[(q + 1) as usize].b32.s1 != TEX_NULL {
            return;
        }
        s = 2i32 as small_number
    }
    loop {
        i = (MEM[q as usize].b16.s1 as i32 % 64) as small_number;
        p = q;
        q = MEM[p as usize].b32.s1;
        free_node(p, s as i32);
        if q == TEX_NULL {
            sa_root[i as usize] = TEX_NULL;
            return;
        }
        if i as i32 & 1i32 != 0 {
            MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = TEX_NULL
        } else {
            MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = TEX_NULL
        }
        MEM[q as usize].b16.s0 -= 1;
        s = 33i32 as small_number;
        if MEM[q as usize].b16.s0 as i32 > 0 {
            break;
        }
    }
}
/*:1609*/
/*1611: */
pub(crate) unsafe fn sa_save(mut p: i32) {
    let mut q: i32 = 0;
    let mut i: u16 = 0;
    if cur_level as i32 != sa_level as i32 {
        if SAVE_PTR > MAX_SAVE_STACK {
            MAX_SAVE_STACK = SAVE_PTR;
            if MAX_SAVE_STACK > SAVE_SIZE - 7 {
                overflow(b"save size", SAVE_SIZE as i32);
            }
        }
        SAVE_STACK[SAVE_PTR].b16.s1 = 4_u16;
        SAVE_STACK[SAVE_PTR].b16.s0 = sa_level;
        SAVE_STACK[SAVE_PTR].b32.s1 = sa_chain;
        SAVE_PTR += 1;
        sa_chain = TEX_NULL;
        sa_level = cur_level
    }
    i = MEM[p as usize].b16.s1;
    if (i as i32) < 128i32 {
        if MEM[(p + 2) as usize].b32.s1 == 0 {
            q = get_node(2i32);
            i = 384_u16
        } else {
            q = get_node(3i32);
            MEM[(q + 2) as usize].b32.s1 = MEM[(p + 2) as usize].b32.s1
        }
        MEM[(q + 1) as usize].b32.s1 = TEX_NULL
    } else {
        q = get_node(2i32);
        MEM[(q + 1) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1
    }
    MEM[(q + 1) as usize].b32.s0 = p;
    MEM[q as usize].b16.s1 = i;
    MEM[q as usize].b16.s0 = MEM[p as usize].b16.s0;
    MEM[q as usize].b32.s1 = sa_chain;
    sa_chain = q;
    MEM[(p + 1) as usize].b32.s0 += 1;
}
pub(crate) unsafe fn sa_destroy(mut p: i32) {
    if (MEM[p as usize].b16.s1 as i32) < 256 {
        delete_glue_ref(MEM[(p + 1) as usize].b32.s1);
    } else if MEM[(p + 1) as usize].b32.s1 != TEX_NULL {
        if (MEM[p as usize].b16.s1 as i32) < 320 {
            flush_node_list(MEM[(p + 1) as usize].b32.s1);
        } else {
            delete_token_ref(MEM[(p + 1) as usize].b32.s1);
        }
    };
}
pub(crate) unsafe fn sa_def(mut p: i32, mut e: i32) {
    MEM[(p + 1) as usize].b32.s0 += 1;
    if MEM[(p + 1) as usize].b32.s1 == e {
        sa_destroy(p);
    } else {
        if MEM[p as usize].b16.s0 as i32 == cur_level as i32 {
            sa_destroy(p);
        } else {
            sa_save(p);
        }
        MEM[p as usize].b16.s0 = cur_level;
        MEM[(p + 1) as usize].b32.s1 = e
    }
    delete_sa_ref(p);
}
pub(crate) unsafe fn sa_w_def(mut p: i32, mut w: i32) {
    MEM[(p + 1) as usize].b32.s0 += 1;
    if !(MEM[(p + 2) as usize].b32.s1 == w) {
        if MEM[p as usize].b16.s0 as i32 != cur_level as i32 {
            sa_save(p);
        }
        MEM[p as usize].b16.s0 = cur_level;
        MEM[(p + 2) as usize].b32.s1 = w
    }
    delete_sa_ref(p);
}
pub(crate) unsafe fn gsa_def(mut p: i32, mut e: i32) {
    MEM[(p + 1) as usize].b32.s0 += 1;
    sa_destroy(p);
    MEM[p as usize].b16.s0 = 1_u16;
    MEM[(p + 1) as usize].b32.s1 = e;
    delete_sa_ref(p);
}
pub(crate) unsafe fn gsa_w_def(mut p: i32, mut w: i32) {
    MEM[(p + 1) as usize].b32.s0 += 1;
    MEM[p as usize].b16.s0 = 1_u16;
    MEM[(p + 2) as usize].b32.s1 = w;
    delete_sa_ref(p);
}
pub(crate) unsafe fn sa_restore() {
    let mut p: i32 = 0;
    loop {
        p = MEM[(sa_chain + 1) as usize].b32.s0;
        if MEM[p as usize].b16.s0 as i32 == 1 {
            if MEM[p as usize].b16.s1 as i32 >= 128 {
                sa_destroy(sa_chain);
            }
        } else {
            if (MEM[p as usize].b16.s1 as i32) < 128 {
                if (MEM[sa_chain as usize].b16.s1 as i32) < 128 {
                    MEM[(p + 2) as usize].b32.s1 = MEM[(sa_chain + 2) as usize].b32.s1
                } else {
                    MEM[(p + 2) as usize].b32.s1 = 0
                }
            } else {
                sa_destroy(p);
                MEM[(p + 1) as usize].b32.s1 = MEM[(sa_chain + 1) as usize].b32.s1
            }
            MEM[p as usize].b16.s0 = MEM[sa_chain as usize].b16.s0
        }
        delete_sa_ref(p);
        p = sa_chain;
        sa_chain = MEM[p as usize].b32.s1;
        if (MEM[p as usize].b16.s1 as i32) < 128 {
            free_node(p, 3i32);
        } else {
            free_node(p, 2i32);
        }
        if sa_chain == TEX_NULL {
            break;
        }
    }
}
pub(crate) unsafe fn new_save_level(mut c: group_code) {
    if SAVE_PTR > MAX_SAVE_STACK {
        MAX_SAVE_STACK = SAVE_PTR;
        if MAX_SAVE_STACK > SAVE_SIZE - 7 {
            overflow(b"save size", SAVE_SIZE as i32);
        }
    }
    SAVE_STACK[SAVE_PTR + 0].b32.s1 = line;
    SAVE_PTR += 1;
    SAVE_STACK[SAVE_PTR].b16.s1 = 3_u16;
    SAVE_STACK[SAVE_PTR].b16.s0 = cur_group as u16;
    SAVE_STACK[SAVE_PTR].b32.s1 = cur_boundary;
    if cur_level as i32 == 65535i32 {
        overflow(b"grouping levels", 65535i32);
    }
    cur_boundary = SAVE_PTR as i32;
    cur_group = c;
    cur_level = cur_level.wrapping_add(1);
    SAVE_PTR += 1;
}
pub(crate) unsafe fn eq_destroy(mut w: memory_word) {
    let mut q: i32 = 0;
    match w.b16.s1 as i32 {
        113 | 114 | 115 | 116 => delete_token_ref(w.b32.s1),
        119 => delete_glue_ref(w.b32.s1),
        120 => {
            q = w.b32.s1;
            if q != TEX_NULL {
                free_node(q, MEM[q as usize].b32.s0 + MEM[q as usize].b32.s0 + 1);
            }
        }
        121 => flush_node_list(w.b32.s1),
        72 | 91 => {
            if w.b32.s1 < 0i32 || w.b32.s1 > 19i32 {
                delete_sa_ref(w.b32.s1);
            }
        }
        _ => {}
    };
}
pub(crate) unsafe fn eq_save(mut p: i32, mut l: u16) {
    if SAVE_PTR > MAX_SAVE_STACK {
        MAX_SAVE_STACK = SAVE_PTR;
        if MAX_SAVE_STACK > SAVE_SIZE - 7 {
            overflow(b"save size", SAVE_SIZE as i32);
        }
    }
    if l as i32 == 0i32 {
        SAVE_STACK[SAVE_PTR].b16.s1 = 1_u16
    } else {
        SAVE_STACK[SAVE_PTR] = EQTB[p as usize];
        SAVE_PTR += 1;
        SAVE_STACK[SAVE_PTR].b16.s1 = 0_u16
    }
    SAVE_STACK[SAVE_PTR].b16.s0 = l;
    SAVE_STACK[SAVE_PTR].b32.s1 = p;
    SAVE_PTR += 1;
}
pub(crate) unsafe fn eq_define(mut p: i32, mut t: u16, mut e: i32) {
    if EQTB[p as usize].b16.s1 as i32 == t as i32 && EQTB[p as usize].b32.s1 == e {
        eq_destroy(EQTB[p as usize]);
        return;
    }
    if EQTB[p as usize].b16.s0 as i32 == cur_level as i32 {
        eq_destroy(EQTB[p as usize]);
    } else if cur_level as i32 > 1i32 {
        eq_save(p, EQTB[p as usize].b16.s0);
    }
    EQTB[p as usize].b16.s0 = cur_level;
    EQTB[p as usize].b16.s1 = t;
    EQTB[p as usize].b32.s1 = e;
}
pub(crate) unsafe fn eq_word_define(mut p: i32, mut w: i32) {
    if EQTB[p as usize].b32.s1 == w {
        return;
    }
    if _xeq_level_array[(p - (INT_BASE)) as usize] as i32 != cur_level as i32 {
        eq_save(p, _xeq_level_array[(p - (INT_BASE)) as usize]);
        _xeq_level_array[(p - (INT_BASE)) as usize] = cur_level
    }
    EQTB[p as usize].b32.s1 = w;
}
pub(crate) unsafe fn geq_define(mut p: i32, mut t: u16, mut e: i32) {
    eq_destroy(EQTB[p as usize]);
    EQTB[p as usize].b16.s0 = 1_u16;
    EQTB[p as usize].b16.s1 = t;
    EQTB[p as usize].b32.s1 = e;
}
pub(crate) unsafe fn geq_word_define(mut p: i32, mut w: i32) {
    EQTB[p as usize].b32.s1 = w;
    _xeq_level_array[(p - (INT_BASE)) as usize] = 1_u16;
}
pub(crate) unsafe fn save_for_after(mut t: i32) {
    if cur_level as i32 > 1i32 {
        if SAVE_PTR > MAX_SAVE_STACK {
            MAX_SAVE_STACK = SAVE_PTR;
            if MAX_SAVE_STACK > SAVE_SIZE - 7 {
                overflow(b"save size", SAVE_SIZE as i32);
            }
        }
        SAVE_STACK[SAVE_PTR].b16.s1 = 2_u16;
        SAVE_STACK[SAVE_PTR].b16.s0 = 0_u16;
        SAVE_STACK[SAVE_PTR].b32.s1 = t;
        SAVE_PTR += 1;
    };
}
pub(crate) unsafe fn unsave() {
    let mut p: i32 = 0;
    let mut l: u16 = 0_u16;
    let mut t: i32 = 0;
    let mut a: bool = false;
    a = false;
    if cur_level as i32 > 1i32 {
        cur_level = cur_level.wrapping_sub(1);
        loop {
            SAVE_PTR -= 1;
            if SAVE_STACK[SAVE_PTR].b16.s1 as i32 == 3i32 {
                break;
            }
            p = SAVE_STACK[SAVE_PTR].b32.s1;
            if SAVE_STACK[SAVE_PTR].b16.s1 as i32 == 2i32 {
                /*338: */
                t = cur_tok;
                cur_tok = p;
                if a {
                    p = get_avail();
                    MEM[p as usize].b32.s0 = cur_tok;
                    MEM[p as usize].b32.s1 = cur_input.loc;
                    cur_input.loc = p;
                    cur_input.start = p;
                    if cur_tok < 0x600000i32 {
                        if cur_tok < 0x400000i32 {
                            align_state -= 1
                        } else {
                            align_state += 1
                        }
                    }
                } else {
                    back_input();
                    a = true
                }
                cur_tok = t
            } else if SAVE_STACK[SAVE_PTR].b16.s1 as i32 == 4i32 {
                sa_restore();
                sa_chain = p;
                sa_level = SAVE_STACK[SAVE_PTR].b16.s0
            } else {
                if SAVE_STACK[SAVE_PTR].b16.s1 as i32 == 0i32 {
                    l = SAVE_STACK[SAVE_PTR].b16.s0;
                    SAVE_PTR -= 1;
                } else {
                    SAVE_STACK[SAVE_PTR] = EQTB[(1i32
                        + (0x10ffffi32 + 1i32)
                        + (0x10ffffi32 + 1i32)
                        + 1i32
                        + 15000i32
                        + 12i32
                        + 9000i32
                        + 1i32) as usize];
                }
                if p < INT_BASE || p > DIMEN_BASE + 23i32 + 256i32 - 1i32 {
                    if EQTB[p as usize].b16.s0 as i32 == 1i32 {
                        eq_destroy(SAVE_STACK[SAVE_PTR]);
                    } else {
                        eq_destroy(EQTB[p as usize]);
                        EQTB[p as usize] = SAVE_STACK[SAVE_PTR]
                    }
                } else if _xeq_level_array[(p - (INT_BASE)) as usize] as i32 != 1i32 {
                    EQTB[p as usize] = SAVE_STACK[SAVE_PTR];
                    _xeq_level_array[(p - (INT_BASE)) as usize] = l
                }
            }
        }
        if GRP_STACK[IN_OPEN] == cur_boundary {
            group_warning();
        }
        cur_group = SAVE_STACK[SAVE_PTR].b16.s0 as group_code;
        cur_boundary = SAVE_STACK[SAVE_PTR].b32.s1;
        SAVE_PTR -= 1;
    } else {
        confusion(b"curlevel");
    };
}
pub(crate) unsafe fn prepare_mag() {
    if mag_set > 0i32 && EQTB[(INT_BASE + 17i32) as usize].b32.s1 != mag_set {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Incompatible magnification (");
        print_int(EQTB[(INT_BASE + 17i32) as usize].b32.s1);
        print_cstr(b");");
        print_nl_cstr(b" the previous value will be retained");
        help_ptr = 2_u8;
        help_line[1] = b"I can handle only one magnification ratio per job. So I\'ve";
        help_line[0] = b"reverted to the magnification you used earlier on this run.";
        int_error(mag_set);
        geq_word_define(INT_BASE + 17i32, mag_set);
    }
    if EQTB[(INT_BASE + 17i32) as usize].b32.s1 <= 0i32
        || EQTB[(INT_BASE + 17i32) as usize].b32.s1 as i64 > 32768
    {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Illegal magnification has been changed to 1000");
        help_ptr = 1_u8;
        help_line[0] = b"The magnification ratio must be between 1 and 32768.";
        int_error(EQTB[(INT_BASE + 17i32) as usize].b32.s1);
        geq_word_define(INT_BASE + 17i32, 1000i32);
    }
    mag_set = EQTB[(INT_BASE + 17i32) as usize].b32.s1;
}
pub(crate) unsafe fn token_show(mut p: i32) {
    if p != TEX_NULL {
        show_token_list(MEM[p as usize].b32.s1, TEX_NULL, 10000000i64 as i32);
    };
}
pub(crate) unsafe fn print_meaning() {
    print_cmd_chr(cur_cmd as u16, cur_chr);
    if cur_cmd as i32 >= 113i32 {
        print_char(':' as i32);
        print_ln();
        token_show(cur_chr);
    } else if cur_cmd as i32 == 112i32 && cur_chr < 5i32 {
        print_char(':' as i32);
        print_ln();
        token_show(cur_mark[cur_chr as usize]);
    };
}
pub(crate) unsafe fn show_cur_cmd_chr() {
    let mut n: i32 = 0;
    let mut l: i32 = 0;
    let mut p: i32 = 0;
    begin_diagnostic();
    print_nl('{' as i32);
    if cur_list.mode as i32 != shown_mode as i32 {
        print_mode(cur_list.mode as i32);
        print_cstr(b": ");
        shown_mode = cur_list.mode
    }
    print_cmd_chr(cur_cmd as u16, cur_chr);
    if EQTB[(INT_BASE + 60i32) as usize].b32.s1 > 0i32 {
        if cur_cmd as i32 >= 107i32 {
            if cur_cmd as i32 <= 108i32 {
                print_cstr(b": ");
                if cur_cmd as i32 == 108i32 {
                    print_cmd_chr(107_u16, cur_if as i32);
                    print_char(' ' as i32);
                    n = 0i32;
                    l = if_line
                } else {
                    n = 1i32;
                    l = line
                }
                p = cond_ptr;
                while p != TEX_NULL {
                    n += 1;
                    p = MEM[p as usize].b32.s1
                }
                print_cstr(b"(level ");
                print_int(n);
                print_char(')' as i32);
                if l != 0i32 {
                    print_cstr(b" entered on line ");
                    print_int(l);
                }
            }
        }
    }
    print_char('}' as i32);
    end_diagnostic(false);
}
pub(crate) unsafe fn show_context() {
    let mut nn: i32 = 0;
    let mut bottom_line: bool = false;
    let mut i: i32 = 0;
    let mut j: i32 = 0;
    let mut l: i32 = 0;
    let mut m: i32 = 0;
    let mut n: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    BASE_PTR = INPUT_PTR;
    INPUT_STACK[BASE_PTR] = cur_input;
    nn = -1i32;
    bottom_line = false;
    loop {
        cur_input = INPUT_STACK[BASE_PTR];
        if cur_input.state as i32 != 0i32 {
            if cur_input.name > 19i32 || BASE_PTR == 0 {
                bottom_line = true
            }
        }
        if BASE_PTR == INPUT_PTR
            || bottom_line as i32 != 0
            || nn < EQTB[(INT_BASE + 54i32) as usize].b32.s1
        {
            /*324: */
            if BASE_PTR == INPUT_PTR
                || cur_input.state as i32 != 0i32
                || cur_input.index as i32 != 3i32
                || cur_input.loc != TEX_NULL
            {
                tally = 0i32;
                let old_setting_0 = selector;
                if cur_input.state as i32 != 0i32 {
                    if cur_input.name <= 17i32 {
                        if cur_input.name == 0i32 {
                            if BASE_PTR == 0 {
                                print_nl_cstr(b"<*>");
                            } else {
                                print_nl_cstr(b"<insert> ");
                            }
                        } else {
                            print_nl_cstr(b"<read ");
                            if cur_input.name == 17i32 {
                                print_char('*' as i32);
                            } else {
                                print_int(cur_input.name - 1i32);
                            }
                            print_char('>' as i32);
                        }
                    } else {
                        print_nl_cstr(b"l.");
                        if cur_input.index as usize == IN_OPEN {
                            print_int(line);
                        } else {
                            print_int(LINE_STACK[(cur_input.index as i32 + 1i32) as usize]);
                        }
                    }
                    print_char(' ' as i32);
                    l = tally;
                    tally = 0i32;
                    selector = Selector::PSEUDO;
                    trick_count = 1000000i64 as i32;
                    if *buffer.offset(cur_input.limit as isize)
                        == EQTB[(INT_BASE + 48i32) as usize].b32.s1
                    {
                        j = cur_input.limit
                    } else {
                        j = cur_input.limit + 1i32
                    }
                    if j > 0i32 {
                        let mut for_end: i32 = 0;
                        i = cur_input.start;
                        for_end = j - 1i32;
                        if i <= for_end {
                            loop {
                                if i == cur_input.loc {
                                    first_count = tally;
                                    trick_count = tally + 1i32 + error_line - half_error_line;
                                    if trick_count < error_line {
                                        trick_count = error_line
                                    }
                                }
                                print_char(*buffer.offset(i as isize));
                                let fresh23 = i;
                                i = i + 1;
                                if !(fresh23 < for_end) {
                                    break;
                                }
                            }
                        }
                    }
                } else {
                    match cur_input.index as i32 {
                        0 => print_nl_cstr(b"<argument> "),
                        1 | 2 => print_nl_cstr(b"<template> "),
                        3 | 4 => {
                            if cur_input.loc == TEX_NULL {
                                print_nl_cstr(b"<recently read> ");
                            } else {
                                print_nl_cstr(b"<to be read again> ");
                            }
                        }
                        5 => print_nl_cstr(b"<inserted text> "),
                        6 => {
                            print_ln();
                            print_cs(cur_input.name);
                        }
                        7 => print_nl_cstr(b"<output> "),
                        8 => print_nl_cstr(b"<everypar> "),
                        9 => print_nl_cstr(b"<everymath> "),
                        10 => print_nl_cstr(b"<everydisplay> "),
                        11 => print_nl_cstr(b"<everyhbox> "),
                        12 => print_nl_cstr(b"<everyvbox> "),
                        13 => print_nl_cstr(b"<everyjob> "),
                        14 => print_nl_cstr(b"<everycr> "),
                        15 => print_nl_cstr(b"<mark> "),
                        16 => print_nl_cstr(b"<everyeof> "),
                        17 => print_nl_cstr(b"<XeTeXinterchartoks> "),
                        18 => print_nl_cstr(b"<write> "),
                        19 => print_nl_cstr(b"<TectonicCodaTokens> "),
                        _ => print_nl('?' as i32),
                    }
                    l = tally;
                    tally = 0i32;
                    selector = Selector::PSEUDO;
                    trick_count = 1000000i64 as i32;
                    if (cur_input.index as i32) < 6i32 {
                        show_token_list(cur_input.start, cur_input.loc, 100000i64 as i32);
                    } else {
                        show_token_list(
                            MEM[cur_input.start as usize].b32.s1,
                            cur_input.loc,
                            100000i64 as i32,
                        );
                    }
                }
                selector = old_setting_0;
                if trick_count as i64 == 1000000 {
                    first_count = tally;
                    trick_count = tally + 1i32 + error_line - half_error_line;
                    if trick_count < error_line {
                        trick_count = error_line
                    }
                }
                if tally < trick_count {
                    m = tally - first_count
                } else {
                    m = trick_count - first_count
                }
                if l + first_count <= half_error_line {
                    p = 0i32;
                    n = l + first_count
                } else {
                    print_cstr(b"...");
                    p = l + first_count - half_error_line + 3i32;
                    n = half_error_line
                }
                let mut for_end_0: i32 = 0;
                q = p;
                for_end_0 = first_count - 1i32;
                if q <= for_end_0 {
                    loop {
                        print_raw_char(trick_buf[(q % error_line) as usize], true);
                        let fresh24 = q;
                        q = q + 1;
                        if !(fresh24 < for_end_0) {
                            break;
                        }
                    }
                }
                print_ln();
                let mut for_end_1: i32 = 0;
                q = 1i32;
                for_end_1 = n;
                if q <= for_end_1 {
                    loop {
                        print_raw_char(' ' as i32 as UTF16_code, true);
                        let fresh25 = q;
                        q = q + 1;
                        if !(fresh25 < for_end_1) {
                            break;
                        }
                    }
                }
                if m + n <= error_line {
                    p = first_count + m
                } else {
                    p = first_count + (error_line - n - 3i32)
                }
                let mut for_end_2: i32 = 0;
                q = first_count;
                for_end_2 = p - 1i32;
                if q <= for_end_2 {
                    loop {
                        print_raw_char(trick_buf[(q % error_line) as usize], true);
                        let fresh26 = q;
                        q = q + 1;
                        if !(fresh26 < for_end_2) {
                            break;
                        }
                    }
                }
                if m + n > error_line {
                    print_cstr(b"...");
                }
                nn += 1
            }
        } else if nn == EQTB[(INT_BASE + 54i32) as usize].b32.s1 {
            print_nl_cstr(b"...");
            nn += 1
        }
        if bottom_line {
            break;
        }
        BASE_PTR -= 1
    }
    cur_input = INPUT_STACK[INPUT_PTR];
}
pub(crate) unsafe fn begin_token_list(mut p: i32, mut t: u16) {
    if INPUT_PTR > MAX_IN_STACK {
        MAX_IN_STACK = INPUT_PTR;
        if INPUT_PTR == STACK_SIZE {
            overflow(b"input stack size", STACK_SIZE as i32);
        }
    }
    INPUT_STACK[INPUT_PTR] = cur_input;
    INPUT_PTR += 1;
    cur_input.state = 0_u16;
    cur_input.start = p;
    cur_input.index = t;
    if t as i32 >= 6i32 {
        MEM[p as usize].b32.s0 += 1;
        if t as i32 == 6i32 {
            cur_input.limit = PARAM_PTR as i32
        } else {
            cur_input.loc = MEM[p as usize].b32.s1;
            if EQTB[(INT_BASE + 30i32) as usize].b32.s1 > 1i32 {
                begin_diagnostic();
                print_nl_cstr(b"");
                match t as i32 {
                    15 => print_esc_cstr(b"mark"),
                    18 => print_esc_cstr(b"write"),
                    _ => {
                        print_cmd_chr(
                            73_u16,
                            t as i32
                                + (1i32
                                    + (0x10ffffi32 + 1i32)
                                    + (0x10ffffi32 + 1i32)
                                    + 1i32
                                    + 15000i32
                                    + 12i32
                                    + 9000i32
                                    + 1i32
                                    + 1i32
                                    + 19i32
                                    + 256i32
                                    + 256i32)
                                + 1i32
                                - 7i32,
                        );
                    }
                }
                print_cstr(b"->");
                token_show(p);
                end_diagnostic(false);
            }
        }
    } else {
        cur_input.loc = p
    };
}
pub(crate) unsafe fn end_token_list() {
    if cur_input.index as i32 >= 3i32 {
        if cur_input.index as i32 <= 5i32 {
            flush_list(cur_input.start);
        } else {
            delete_token_ref(cur_input.start);
            if cur_input.index as i32 == 6i32 {
                while PARAM_PTR as i32 > cur_input.limit {
                    PARAM_PTR -= 1;
                    flush_list(PARAM_STACK[PARAM_PTR]);
                }
            }
        }
    } else if cur_input.index as i32 == 1i32 {
        if align_state as i64 > 500000 {
            align_state = 0i32
        } else {
            fatal_error(b"(interwoven alignment preambles are not allowed)");
        }
    }
    INPUT_PTR -= 1;
    cur_input = INPUT_STACK[INPUT_PTR];
}
pub(crate) unsafe fn back_input() {
    let mut p: i32 = 0;
    while cur_input.state as i32 == 0i32
        && cur_input.loc == TEX_NULL
        && cur_input.index as i32 != 2i32
    {
        end_token_list();
    }
    p = get_avail();
    MEM[p as usize].b32.s0 = cur_tok;
    if cur_tok < 0x600000i32 {
        if cur_tok < 0x400000i32 {
            align_state -= 1
        } else {
            align_state += 1
        }
    }
    if INPUT_PTR > MAX_IN_STACK {
        MAX_IN_STACK = INPUT_PTR;
        if INPUT_PTR == STACK_SIZE {
            overflow(b"input stack size", STACK_SIZE as i32);
        }
    }
    INPUT_STACK[INPUT_PTR] = cur_input;
    INPUT_PTR += 1;
    cur_input.state = 0_u16;
    cur_input.start = p;
    cur_input.index = 3_u16;
    cur_input.loc = p;
}
pub(crate) unsafe fn back_error() {
    back_input();
    error();
}
pub(crate) unsafe fn ins_error() {
    back_input();
    cur_input.index = 5_u16;
    error();
}
pub(crate) unsafe fn begin_file_reading() {
    if IN_OPEN == MAX_IN_OPEN {
        overflow(b"text input levels", MAX_IN_OPEN as i32);
    }
    if first == buf_size {
        overflow(b"buffer size", buf_size);
    }
    IN_OPEN += 1;
    if INPUT_PTR > MAX_IN_STACK {
        MAX_IN_STACK = INPUT_PTR;
        if INPUT_PTR == STACK_SIZE {
            overflow(b"input stack size", STACK_SIZE as i32);
        }
    }
    INPUT_STACK[INPUT_PTR] = cur_input;
    INPUT_PTR += 1;
    cur_input.index = IN_OPEN as u16;
    SOURCE_FILENAME_STACK[cur_input.index as usize] = 0;
    FULL_SOURCE_FILENAME_STACK[cur_input.index as usize] = 0;
    EOF_SEEN[cur_input.index as usize] = false;
    GRP_STACK[cur_input.index as usize] = cur_boundary;
    IF_STACK[cur_input.index as usize] = cond_ptr;
    LINE_STACK[cur_input.index as usize] = line;
    cur_input.start = first;
    cur_input.state = 1_u16;
    cur_input.name = 0i32;
    cur_input.synctex_tag = 0i32;
}
pub(crate) unsafe fn end_file_reading() {
    first = cur_input.start;
    line = LINE_STACK[cur_input.index as usize];
    if cur_input.name == 18i32 || cur_input.name == 19i32 {
        pseudo_close();
    } else if cur_input.name > 17i32 {
        u_close(INPUT_FILE[cur_input.index as usize]);
    }
    INPUT_PTR -= 1;
    cur_input = INPUT_STACK[INPUT_PTR];
    IN_OPEN -= 1;
}
pub(crate) unsafe fn check_outer_validity() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    if scanner_status as i32 != 0i32 {
        deletions_allowed = false;
        if cur_cs != 0i32 {
            if cur_input.state as i32 == 0i32 || cur_input.name < 1i32 || cur_input.name > 17i32 {
                p = get_avail();
                MEM[p as usize].b32.s0 = 0x1ffffff + cur_cs;
                begin_token_list(p, 3_u16);
            }
            cur_cmd = 10i32 as eight_bits;
            cur_chr = ' ' as i32
        }
        if scanner_status as i32 > 1i32 {
            /*350:*/
            runaway();
            if cur_cs == 0i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"File ended");
            } else {
                cur_cs = 0i32;
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Forbidden control sequence found");
            }
            p = get_avail();
            match scanner_status as i32 {
                2 => {
                    print_cstr(b" while scanning definition");
                    MEM[p as usize].b32.s0 = 0x400000 + '}' as i32
                }
                3 => {
                    print_cstr(b" while scanning use");
                    MEM[p as usize].b32.s0 = par_token;
                    long_state = 115_u8
                }
                4 => {
                    print_cstr(b" while scanning preamble");
                    MEM[p as usize].b32.s0 = 0x400000 + '}' as i32;
                    q = p;
                    p = get_avail();
                    MEM[p as usize].b32.s1 = q;
                    MEM[p as usize].b32.s0 = 0x1ffffff
                        + (1i32
                            + (0x10ffffi32 + 1i32)
                            + (0x10ffffi32 + 1i32)
                            + 1i32
                            + 15000i32
                            + 1i32);
                    align_state = -1000000i64 as i32
                }
                5 => {
                    print_cstr(b" while scanning text");
                    MEM[p as usize].b32.s0 = 0x400000 + '}' as i32
                }
                _ => {}
            }
            begin_token_list(p, 5_u16);
            print_cstr(b" of ");
            sprint_cs(warning_index);
            help_ptr = 4_u8;
            help_line[3] = b"I suspect you have forgotten a `}\', causing me";
            help_line[2] = b"to read past where you wanted me to stop.";
            help_line[1] = b"I\'ll try to recover; but if the error is serious,";
            help_line[0] = b"you\'d better type `E\' or `X\' now and fix your file.";
            error();
        } else {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Incomplete ");
            print_cmd_chr(107_u16, cur_if as i32);
            print_cstr(b"; all text was ignored after line ");
            print_int(skip_line);
            help_ptr = 3_u8;
            help_line[2] = b"A forbidden control sequence occurred in skipped text.";
            help_line[1] = b"This kind of error happens when you say `\\if...\' and forget";
            help_line[0] = b"the matching `\\fi\'. I\'ve inserted a `\\fi\'; this might work.";
            if cur_cs != 0i32 {
                cur_cs = 0i32
            } else {
                help_line[2] = b"The file ended while I was skipping conditional text."
            }
            cur_tok = 0x1ffffffi32 + (FROZEN_CONTROL_SEQUENCE + 4i32);
            ins_error();
        }
        deletions_allowed = true
    };
}
/* These macros are kinda scary, but convenient */
pub(crate) unsafe fn get_next() {
    let mut current_block: u64;
    let mut k: i32 = 0;
    let mut t: i32 = 0;
    let mut cat: u8 = 0;
    let mut c: UnicodeScalar = 0;
    let mut lower: UTF16_code = 0;
    let mut d: small_number = 0;
    let mut sup_count: small_number = 0;
    'c_63502: loop {
        cur_cs = 0i32;
        if cur_input.state as i32 != 0i32 {
            /*355:*/
            'c_63807: loop
            /*357:*/
            {
                if cur_input.loc <= cur_input.limit {
                    cur_chr = *buffer.offset(cur_input.loc as isize);
                    cur_input.loc += 1;
                    if cur_chr >= 0xd800i32
                        && cur_chr < 0xdc00i32
                        && cur_input.loc <= cur_input.limit
                        && *buffer.offset(cur_input.loc as isize) >= 0xdc00i32
                        && *buffer.offset(cur_input.loc as isize) < 0xe000i32
                    {
                        lower = (*buffer.offset(cur_input.loc as isize) - 0xdc00i32) as UTF16_code;
                        cur_input.loc += 1;
                        cur_chr =
                            (65536 + ((cur_chr - 0xd800i32) * 1024i32) as i64 + lower as i64) as i32
                    }
                    'c_65186: loop {
                        cur_cmd = EQTB[(MATH_FONT_BASE + 3i32 * 256i32 + cur_chr) as usize]
                            .b32
                            .s1 as eight_bits;
                        match cur_input.state as i32 + cur_cmd as i32 {
                            10 | 26 | 42 | 27 | 43 => break,
                            1 | 17 | 33 => {
                                if cur_input.loc > cur_input.limit {
                                    current_block = 17833034027772472439;
                                    break 'c_63807;
                                } else {
                                    current_block = 7720778817628725688;
                                    break 'c_63807;
                                }
                            }
                            14 | 30 | 46 => {
                                cur_cs = cur_chr + 1i32;
                                cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits;
                                cur_chr = EQTB[cur_cs as usize].b32.s1;
                                cur_input.state = 1_u16;
                                if cur_cmd as i32 >= 115i32 {
                                    check_outer_validity();
                                }
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            8 | 24 | 40 => {
                                if !(cur_chr == *buffer.offset(cur_input.loc as isize)) {
                                    current_block = 8567661057257693057;
                                    break 'c_63807;
                                }
                                if !(cur_input.loc < cur_input.limit) {
                                    current_block = 8567661057257693057;
                                    break 'c_63807;
                                }
                                sup_count = 2i32 as small_number;
                                while (sup_count as i32) < 6i32
                                    && cur_input.loc + 2i32 * sup_count as i32 - 2i32
                                        <= cur_input.limit
                                    && cur_chr
                                        == *buffer.offset(
                                            (cur_input.loc + sup_count as i32 - 1i32) as isize,
                                        )
                                {
                                    sup_count += 1
                                }
                                d = 1i32 as small_number;
                                while d as i32 <= sup_count as i32 {
                                    if !(*buffer.offset(
                                        (cur_input.loc + sup_count as i32 - 2i32 + d as i32)
                                            as isize,
                                    ) >= '0' as i32
                                        && *buffer.offset(
                                            (cur_input.loc + sup_count as i32 - 2i32 + d as i32)
                                                as isize,
                                        ) <= '9' as i32
                                        || *buffer.offset(
                                            (cur_input.loc + sup_count as i32 - 2i32 + d as i32)
                                                as isize,
                                        ) >= 'a' as i32
                                            && *buffer.offset(
                                                (cur_input.loc + sup_count as i32 - 2i32 + d as i32)
                                                    as isize,
                                            ) <= 'f' as i32)
                                    {
                                        c = *buffer.offset((cur_input.loc + 1i32) as isize);
                                        if !(c < 128i32) {
                                            current_block = 8567661057257693057;
                                            break 'c_63807;
                                        }
                                        cur_input.loc = cur_input.loc + 2i32;
                                        if c < 64i32 {
                                            cur_chr = c + 64i32
                                        } else {
                                            cur_chr = c - 64i32
                                        }
                                        continue 'c_65186;
                                    } else {
                                        d += 1
                                    }
                                }
                                cur_chr = 0i32;
                                d = 1i32 as small_number;
                                while d as i32 <= sup_count as i32 {
                                    c = *buffer.offset(
                                        (cur_input.loc + sup_count as i32 - 2i32 + d as i32)
                                            as isize,
                                    );
                                    if c <= '9' as i32 {
                                        cur_chr = 16i32 * cur_chr + c - '0' as i32
                                    } else {
                                        cur_chr = 16i32 * cur_chr + c - 'a' as i32 + 10i32
                                    }
                                    d += 1
                                }
                                if cur_chr > 0x10ffffi32 {
                                    cur_chr = *buffer.offset(cur_input.loc as isize);
                                    current_block = 8567661057257693057;
                                    break 'c_63807;
                                } else {
                                    cur_input.loc = cur_input.loc + 2i32 * sup_count as i32 - 1i32
                                }
                            }
                            16 | 32 | 48 => {
                                if file_line_error_style_p != 0 {
                                    print_file_line();
                                } else {
                                    print_nl_cstr(b"! ");
                                }
                                print_cstr(b"Text line contains an invalid character");
                                help_ptr = 2_u8;
                                help_line[1] =
                                    b"A funny symbol that I can\'t read has just been input.";
                                help_line[0] = b"Continue, and I\'ll forget that it ever happened.";
                                deletions_allowed = false;
                                error();
                                deletions_allowed = true;
                                continue 'c_63502;
                            }
                            11 => {
                                cur_input.state = 17_u16;
                                cur_chr = ' ' as i32;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            6 => {
                                cur_input.loc = cur_input.limit + 1i32;
                                cur_cmd = 10i32 as eight_bits;
                                cur_chr = ' ' as i32;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            15 | 31 | 47 | 22 => {
                                cur_input.loc = cur_input.limit + 1i32;
                                break;
                            }
                            38 => {
                                cur_input.loc = cur_input.limit + 1i32;
                                cur_cs = par_loc;
                                cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits;
                                cur_chr = EQTB[cur_cs as usize].b32.s1;
                                if cur_cmd as i32 >= 115i32 {
                                    check_outer_validity();
                                }
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            2 => {
                                align_state += 1;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            18 | 34 => {
                                cur_input.state = 1_u16;
                                align_state += 1;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            3 => {
                                align_state -= 1;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            19 | 35 => {
                                cur_input.state = 1_u16;
                                align_state -= 1;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            20 | 21 | 23 | 25 | 28 | 29 | 36 | 37 | 39 | 41 | 44 | 45 => {
                                cur_input.state = 1_u16;
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                            _ => {
                                current_block = 14956172121224201915;
                                break 'c_63807;
                            }
                        }
                    }
                } else {
                    cur_input.state = 33_u16;
                    if cur_input.name > 17i32 {
                        /*374:*/
                        line += 1; /*367:*/
                        first = cur_input.start;
                        if !force_eof {
                            if cur_input.name <= 19i32 {
                                if pseudo_input() {
                                    cur_input.limit = last
                                } else if EQTB[(LOCAL_BASE + 10i32) as usize].b32.s1 != TEX_NULL
                                    && !EOF_SEEN[cur_input.index as usize]
                                {
                                    cur_input.limit = first - 1i32;
                                    EOF_SEEN[cur_input.index as usize] = true;
                                    begin_token_list(
                                        EQTB[(1i32
                                            + (0x10ffffi32 + 1i32)
                                            + (0x10ffffi32 + 1i32)
                                            + 1i32
                                            + 15000i32
                                            + 12i32
                                            + 9000i32
                                            + 1i32
                                            + 1i32
                                            + 19i32
                                            + 256i32
                                            + 256i32
                                            + 10i32)
                                            as usize]
                                            .b32
                                            .s1,
                                        16_u16,
                                    );
                                    continue 'c_63502;
                                } else {
                                    force_eof = true
                                }
                            } else if input_line(INPUT_FILE[cur_input.index as usize]) != 0 {
                                cur_input.limit = last
                            } else if EQTB[(LOCAL_BASE + 10i32) as usize].b32.s1 != TEX_NULL
                                && !EOF_SEEN[cur_input.index as usize]
                            {
                                cur_input.limit = first - 1i32;
                                EOF_SEEN[cur_input.index as usize] = true;
                                begin_token_list(
                                    EQTB[(LOCAL_BASE + 10i32) as usize].b32.s1,
                                    16_u16,
                                );
                                continue 'c_63502;
                            } else {
                                force_eof = true
                            }
                        }
                        if force_eof {
                            if EQTB[(INT_BASE + 62i32) as usize].b32.s1 > 0i32 {
                                if GRP_STACK[IN_OPEN] != cur_boundary
                                    || IF_STACK[IN_OPEN] != cond_ptr
                                {
                                    file_warning();
                                }
                            }
                            if cur_input.name >= 19i32 {
                                print_char(')' as i32);
                                open_parens -= 1;
                                rust_stdout.as_mut().unwrap().flush().unwrap();
                            }
                            force_eof = false;
                            end_file_reading();
                            check_outer_validity();
                            continue 'c_63502;
                        } else {
                            if EQTB[(INT_BASE + 48i32) as usize].b32.s1 < 0i32
                                || EQTB[(INT_BASE + 48i32) as usize].b32.s1 > 255i32
                            {
                                cur_input.limit -= 1
                            } else {
                                *buffer.offset(cur_input.limit as isize) =
                                    EQTB[(INT_BASE + 48i32) as usize].b32.s1
                            }
                            first = cur_input.limit + 1i32;
                            cur_input.loc = cur_input.start
                        }
                    } else {
                        if cur_input.name != 0i32 {
                            cur_cmd = 0i32 as eight_bits;
                            cur_chr = 0i32;
                            return;
                        }
                        if INPUT_PTR > 0 {
                            current_block = 4001239642700071046;
                            break;
                        } else {
                            current_block = 15055213890147597004;
                            break;
                        }
                    }
                }
            }
            match current_block {
                14956172121224201915 => {}
                _ => {
                    match current_block {
                        8567661057257693057 => {
                            cur_input.state = 1_u16;
                            current_block = 14956172121224201915;
                        }
                        7720778817628725688 => {
                            'c_65963: loop {
                                k = cur_input.loc;
                                cur_chr = *buffer.offset(k as isize);
                                cat = EQTB[(CUR_FONT_LOC + 1i32 + 3i32 * 256i32 + cur_chr) as usize]
                                    .b32
                                    .s1 as u8;
                                k += 1;
                                if cat as i32 == 11i32 {
                                    cur_input.state = 17_u16
                                } else if cat as i32 == 10i32 {
                                    cur_input.state = 17_u16
                                } else {
                                    cur_input.state = 1_u16
                                }
                                if cat as i32 == 11i32 && k <= cur_input.limit {
                                    loop
                                    /*368:*/
                                    {
                                        cur_chr = *buffer.offset(k as isize);
                                        cat = EQTB
                                            [(MATH_FONT_BASE + 3i32 * 256i32 + cur_chr) as usize]
                                            .b32
                                            .s1 as u8;
                                        k += 1;
                                        if !(cat as i32 == 11i32 && k <= cur_input.limit) {
                                            break;
                                        }
                                    }
                                    if !(cat as i32 == 7i32
                                        && *buffer.offset(k as isize) == cur_chr
                                        && k < cur_input.limit)
                                    {
                                        current_block = 5873035170358615968;
                                        break;
                                    }
                                    /* Special characters: either ^^X, or up to six
                                     * ^'s followed by one hex character for each
                                     * ^. */
                                    let mut sup_count_save: i32 = 0;
                                    /* How many ^'s are there? */
                                    sup_count = 2i32 as small_number;
                                    while (sup_count as i32) < 6i32
                                        && k + 2i32 * sup_count as i32 - 2i32 <= cur_input.limit
                                        && *buffer.offset((k + sup_count as i32 - 1i32) as isize)
                                            == cur_chr
                                    {
                                        sup_count += 1
                                    }
                                    /* If they are followed by a sufficient number of
                                     * hex characters, treat it as an extended ^^^
                                     * sequence. If not, treat it as original-style
                                     * ^^X. */
                                    sup_count_save = sup_count as i32;
                                    d = 1i32 as small_number;
                                    while d as i32 <= sup_count_save {
                                        if !(*buffer.offset(
                                            (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                        ) >= '0' as i32
                                            && *buffer.offset(
                                                (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                            ) <= '9' as i32
                                            || *buffer.offset(
                                                (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                            ) >= 'a' as i32
                                                && *buffer.offset(
                                                    (k + sup_count as i32 - 2i32 + d as i32)
                                                        as isize,
                                                ) <= 'f' as i32)
                                        {
                                            /* Non-hex: do it old style */
                                            c = *buffer.offset((k + 1i32) as isize);
                                            if c < 128i32 {
                                                if c < 64i32 {
                                                    *buffer.offset((k - 1i32) as isize) = c + 64i32
                                                } else {
                                                    *buffer.offset((k - 1i32) as isize) = c - 64i32
                                                }
                                                d = 2i32 as small_number;
                                                cur_input.limit = cur_input.limit - d as i32;
                                                while k <= cur_input.limit {
                                                    *buffer.offset(k as isize) =
                                                        *buffer.offset((k + d as i32) as isize);
                                                    k += 1
                                                }
                                                continue 'c_65963;
                                            } else {
                                                sup_count = 0i32 as small_number
                                            }
                                        }
                                        d += 1
                                    }
                                    if !(sup_count as i32 > 0i32) {
                                        current_block = 5873035170358615968;
                                        break;
                                    }
                                    cur_chr = 0i32;
                                    d = 1i32 as small_number;
                                    while d as i32 <= sup_count as i32 {
                                        c = *buffer.offset(
                                            (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                        );
                                        if c <= '9' as i32 {
                                            cur_chr = 16i32 * cur_chr + c - '0' as i32
                                        } else {
                                            cur_chr = 16i32 * cur_chr + c - 'a' as i32 + 10i32
                                        }
                                        d += 1
                                    }
                                    if cur_chr > 0x10ffffi32 {
                                        cur_chr = *buffer.offset(k as isize);
                                        current_block = 5873035170358615968;
                                        break;
                                    } else {
                                        *buffer.offset((k - 1i32) as isize) = cur_chr;
                                        d = (2i32 * sup_count as i32 - 1i32) as small_number;
                                        cur_input.limit = cur_input.limit - d as i32;
                                        while k <= cur_input.limit {
                                            *buffer.offset(k as isize) =
                                                *buffer.offset((k + d as i32) as isize);
                                            k += 1
                                        }
                                    }
                                } else {
                                    if !(cat as i32 == 7i32
                                        && *buffer.offset(k as isize) == cur_chr
                                        && k < cur_input.limit)
                                    {
                                        current_block = 1604201581803946138;
                                        break;
                                    }
                                    let mut sup_count_save_0: i32 = 0;
                                    sup_count = 2i32 as small_number;
                                    while (sup_count as i32) < 6i32
                                        && k + 2i32 * sup_count as i32 - 2i32 <= cur_input.limit
                                        && *buffer.offset((k + sup_count as i32 - 1i32) as isize)
                                            == cur_chr
                                    {
                                        sup_count += 1
                                    }
                                    sup_count_save_0 = sup_count as i32;
                                    d = 1i32 as small_number;
                                    while d as i32 <= sup_count_save_0 {
                                        if !(*buffer.offset(
                                            (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                        ) >= '0' as i32
                                            && *buffer.offset(
                                                (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                            ) <= '9' as i32
                                            || *buffer.offset(
                                                (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                            ) >= 'a' as i32
                                                && *buffer.offset(
                                                    (k + sup_count as i32 - 2i32 + d as i32)
                                                        as isize,
                                                ) <= 'f' as i32)
                                        {
                                            c = *buffer.offset((k + 1i32) as isize);
                                            if c < 128i32 {
                                                if c < 64i32 {
                                                    *buffer.offset((k - 1i32) as isize) = c + 64i32
                                                } else {
                                                    *buffer.offset((k - 1i32) as isize) = c - 64i32
                                                }
                                                d = 2i32 as small_number;
                                                cur_input.limit = cur_input.limit - d as i32;
                                                while k <= cur_input.limit {
                                                    *buffer.offset(k as isize) =
                                                        *buffer.offset((k + d as i32) as isize);
                                                    k += 1
                                                }
                                                continue 'c_65963;
                                            } else {
                                                sup_count = 0i32 as small_number
                                            }
                                        }
                                        d += 1
                                    }
                                    if !(sup_count as i32 > 0i32) {
                                        current_block = 1604201581803946138;
                                        break;
                                    }
                                    cur_chr = 0i32;
                                    d = 1i32 as small_number;
                                    while d as i32 <= sup_count as i32 {
                                        c = *buffer.offset(
                                            (k + sup_count as i32 - 2i32 + d as i32) as isize,
                                        );
                                        if c <= '9' as i32 {
                                            cur_chr = 16i32 * cur_chr + c - '0' as i32
                                        } else {
                                            cur_chr = 16i32 * cur_chr + c - 'a' as i32 + 10i32
                                        }
                                        d += 1
                                    }
                                    if cur_chr > 0x10ffffi32 {
                                        cur_chr = *buffer.offset(k as isize);
                                        current_block = 1604201581803946138;
                                        break;
                                    } else {
                                        *buffer.offset((k - 1i32) as isize) = cur_chr;
                                        d = (2i32 * sup_count as i32 - 1i32) as small_number;
                                        cur_input.limit = cur_input.limit - d as i32;
                                        while k <= cur_input.limit {
                                            *buffer.offset(k as isize) =
                                                *buffer.offset((k + d as i32) as isize);
                                            k += 1
                                        }
                                    }
                                }
                            }
                            match current_block {
                                5873035170358615968 => {
                                    if cat as i32 != 11i32 {
                                        k -= 1
                                    }
                                    if k > cur_input.loc + 1i32 {
                                        cur_cs = id_lookup(cur_input.loc, k - cur_input.loc);
                                        cur_input.loc = k;
                                        current_block = 10802200937357087535;
                                    } else {
                                        current_block = 1604201581803946138;
                                    }
                                }
                                _ => {}
                            }
                            match current_block {
                                10802200937357087535 => {}
                                _ => {
                                    if *buffer.offset(cur_input.loc as isize) as i64 > 65535 {
                                        cur_cs = id_lookup(cur_input.loc, 1i32);
                                        cur_input.loc += 1
                                    } else {
                                        cur_cs = 1i32
                                            + (0x10ffffi32 + 1i32)
                                            + *buffer.offset(cur_input.loc as isize);
                                        cur_input.loc += 1
                                    }
                                    current_block = 10802200937357087535;
                                }
                            }
                        }
                        17833034027772472439 => {
                            cur_cs = 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32);
                            current_block = 10802200937357087535;
                        }
                        4001239642700071046 => {
                            end_file_reading();
                            continue;
                        }
                        _ =>
                        /* Tectonic extension: we add a \TectonicCodaTokens toklist
                         * that gets inserted at the very very end of processing if no
                         * \end or \dump has been seen. We just use a global state
                         * variable to make sure it only gets inserted once. */
                        {
                            if !used_tectonic_coda_tokens
                                && EQTB[(LOCAL_BASE + 12i32) as usize].b32.s1 != TEX_NULL
                            {
                                used_tectonic_coda_tokens = true; /* token list but no tokens left */
                                begin_token_list(
                                    EQTB[(LOCAL_BASE + 12i32) as usize].b32.s1,
                                    19_u16,
                                );
                                continue;
                            } else {
                                if u8::from(selector) < u8::from(Selector::LOG_ONLY) {
                                    open_log_file();
                                }
                                fatal_error(b"*** (job aborted, no legal \\end found)");
                            }
                        }
                    }
                    match current_block {
                        14956172121224201915 => {}
                        _ => {
                            cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits;
                            cur_chr = EQTB[cur_cs as usize].b32.s1;
                            if cur_cmd as i32 >= 115i32 {
                                check_outer_validity();
                            }
                        }
                    }
                }
            }
        } else if cur_input.loc != TEX_NULL {
            /* if we're inputting from a non-null token list: */
            t = MEM[cur_input.loc as usize].b32.s0;
            cur_input.loc = MEM[cur_input.loc as usize].b32.s1;
            if t >= 0x1ffffffi32 {
                cur_cs = t - 0x1ffffffi32;
                cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits;
                cur_chr = EQTB[cur_cs as usize].b32.s1;
                if cur_cmd as i32 >= 115i32 {
                    if cur_cmd as i32 == 118i32 {
                        /*370:*/
                        cur_cs = MEM[cur_input.loc as usize].b32.s0 - 0x1ffffff;
                        cur_input.loc = TEX_NULL;
                        cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits;
                        cur_chr = EQTB[cur_cs as usize].b32.s1;
                        if cur_cmd as i32 > 102i32 {
                            cur_cmd = 0i32 as eight_bits;
                            cur_chr = 0x10ffffi32 + 2i32
                        }
                    } else {
                        check_outer_validity();
                    }
                }
            } else {
                cur_cmd = (t / 0x200000i32) as eight_bits;
                cur_chr = t % 0x200000i32;
                match cur_cmd as i32 {
                    1 => {
                        current_block = 17818108259648334471;
                        align_state += 1;
                    }
                    2 => {
                        current_block = 1336783539463924428;
                        align_state -= 1;
                    }
                    5 => {
                        current_block = 1132450443677887731;
                        begin_token_list(
                            PARAM_STACK[(cur_input.limit + cur_chr - 1) as usize],
                            0_u16,
                        );
                        continue;
                    }
                    _ => {}
                }
            }
        } else {
            end_token_list();
            continue;
        }
        if cur_cmd as i32 <= 5i32 && cur_cmd as i32 >= 4i32 && align_state == 0i32 {
            /*818:*/
            if scanner_status as i32 == 4i32 || cur_align == TEX_NULL {
                fatal_error(b"(interwoven alignment preambles are not allowed)");
            }
            cur_cmd = MEM[(cur_align + 5) as usize].b32.s0 as eight_bits;
            MEM[(cur_align + 5) as usize].b32.s0 = cur_chr;
            if cur_cmd as i32 == 63i32 {
                begin_token_list(4999999i32 - 10i32, 2_u16);
            } else {
                begin_token_list(MEM[(cur_align + 2) as usize].b32.s1, 2_u16);
            }
            align_state = 1000000i64 as i32
        } else {
            return;
        }
    }
}
pub(crate) unsafe fn get_token() {
    no_new_control_sequence = false;
    get_next();
    no_new_control_sequence = true;
    if cur_cs == 0i32 {
        cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr
    } else {
        cur_tok = 0x1ffffffi32 + cur_cs
    };
}
pub(crate) unsafe fn macro_call() {
    let mut current_block: u64;
    let mut r: i32 = 0;
    let mut p: i32 = TEX_NULL;
    let mut q: i32 = 0;
    let mut s: i32 = 0;
    let mut t: i32 = 0;
    let mut u: i32 = 0;
    let mut v: i32 = 0;
    let mut rbrace_ptr: i32 = TEX_NULL;
    let mut n: small_number = 0;
    let mut unbalance: i32 = 0;
    let mut m: i32 = 0i32;
    let mut ref_count: i32 = 0;
    let mut save_scanner_status: small_number = 0;
    let mut save_warning_index: i32 = 0;
    let mut match_chr: UTF16_code = 0;
    save_scanner_status = scanner_status as small_number;
    save_warning_index = warning_index;
    warning_index = cur_cs;
    ref_count = cur_chr;
    r = MEM[ref_count as usize].b32.s1;
    n = 0i32 as small_number;
    if EQTB[(INT_BASE + 30i32) as usize].b32.s1 > 0i32 {
        /*419:*/
        begin_diagnostic();
        print_ln();
        print_cs(warning_index);
        token_show(ref_count);
        end_diagnostic(false);
    }
    if MEM[r as usize].b32.s0 == 0x1c00000 + 1 {
        r = MEM[r as usize].b32.s1
    }
    if MEM[r as usize].b32.s0 != 0x1c00000 {
        /*409:*/
        scanner_status = 3_u8;
        unbalance = 0i32;
        long_state = EQTB[cur_cs as usize].b16.s1 as u8;
        if long_state as i32 >= 115i32 {
            long_state = (long_state as i32 - 2i32) as u8
        }
        's_135: loop {
            MEM[(4999999 - 3) as usize].b32.s1 = TEX_NULL;
            if MEM[r as usize].b32.s0 >= 0x1c00000 || MEM[r as usize].b32.s0 < 0x1a00000 {
                s = TEX_NULL
            } else {
                match_chr = (MEM[r as usize].b32.s0 - 0x1a00000) as UTF16_code;
                s = MEM[r as usize].b32.s1;
                r = s;
                p = 4999999i32 - 3i32;
                m = 0i32
            }
            'c_67378: loop {
                get_token();
                if cur_tok == MEM[r as usize].b32.s0 {
                    /*412:*/
                    r = MEM[r as usize].b32.s1;
                    if !(MEM[r as usize].b32.s0 >= 0x1a00000 && MEM[r as usize].b32.s0 <= 0x1c00000)
                    {
                        continue;
                    }
                    if cur_tok < 0x400000i32 {
                        align_state -= 1
                    }
                    break;
                } else {
                    if s != r {
                        if s == TEX_NULL {
                            /*416:*/
                            if file_line_error_style_p != 0 {
                                print_file_line();
                            } else {
                                print_nl_cstr(b"! ");
                            }
                            print_cstr(b"Use of ");
                            sprint_cs(warning_index);
                            print_cstr(b" doesn\'t match its definition");
                            help_ptr = 4_u8;
                            help_line[3] =
                                b"If you say, e.g., `\\def\\a1{...}\', then you must always";
                            help_line[2] =
                                b"put `1\' after `\\a\', since control sequence names are";
                            help_line[1] = b"made up of letters only. The macro here has not been";
                            help_line[0] = b"followed by the required stuff, so I\'m ignoring it.";
                            error();
                            current_block = 16670727159935121194;
                            break 's_135;
                        } else {
                            t = s;
                            loop {
                                q = get_avail();
                                MEM[p as usize].b32.s1 = q;
                                MEM[q as usize].b32.s0 = MEM[t as usize].b32.s0;
                                p = q;
                                m += 1;
                                u = MEM[t as usize].b32.s1;
                                v = s;
                                loop {
                                    if u == r {
                                        if cur_tok != MEM[v as usize].b32.s0 {
                                            break;
                                        }
                                        r = MEM[v as usize].b32.s1;
                                        continue 'c_67378;
                                    } else {
                                        if MEM[u as usize].b32.s0 != MEM[v as usize].b32.s0 {
                                            break;
                                        }
                                        u = MEM[u as usize].b32.s1;
                                        v = MEM[v as usize].b32.s1
                                    }
                                }
                                t = MEM[t as usize].b32.s1;
                                if !(t != r) {
                                    break;
                                }
                            }
                            r = s
                        }
                    }
                    if cur_tok == par_token {
                        if long_state as i32 != 114i32 {
                            /*414:*/
                            if long_state as i32 == 113i32 {
                                runaway(); /*411:*/
                                if file_line_error_style_p != 0 {
                                    print_file_line(); /*413:*/
                                } else {
                                    print_nl_cstr(b"! ");
                                }
                                print_cstr(b"Paragraph ended before ");
                                sprint_cs(warning_index);
                                print_cstr(b" was complete");
                                help_ptr = 3_u8;
                                help_line[2] =
                                    b"I suspect you\'ve forgotten a `}\', causing me to apply this";
                                help_line[1] =
                                    b"control sequence to too much text. How can we recover?";
                                help_line[0] =
                                    b"My plan is to forget the whole thing and hope for the best.";
                                back_error();
                            }
                            pstack[n as usize] = MEM[(4999999 - 3) as usize].b32.s1;
                            align_state = align_state - unbalance;
                            m = 0i32;
                            while m <= n as i32 {
                                flush_list(pstack[m as usize]);
                                m += 1
                            }
                            current_block = 16670727159935121194;
                            break 's_135;
                        }
                    }
                    if cur_tok < 0x600000i32 {
                        if cur_tok < 0x400000i32 {
                            /*417:*/
                            unbalance = 1i32;
                            loop {
                                q = avail;
                                if q == TEX_NULL {
                                    q = get_avail()
                                } else {
                                    avail = MEM[q as usize].b32.s1;
                                    MEM[q as usize].b32.s1 = TEX_NULL
                                }
                                MEM[p as usize].b32.s1 = q;
                                MEM[q as usize].b32.s0 = cur_tok;
                                p = q;
                                get_token();
                                if cur_tok == par_token {
                                    if long_state as i32 != 114i32 {
                                        /*414:*/
                                        if long_state as i32 == 113i32 {
                                            runaway();
                                            if file_line_error_style_p != 0 {
                                                print_file_line();
                                            } else {
                                                print_nl_cstr(b"! ");
                                            }
                                            print_cstr(b"Paragraph ended before ");
                                            sprint_cs(warning_index);
                                            print_cstr(b" was complete");
                                            help_ptr = 3_u8;
                                            help_line[2] =
                                                        b"I suspect you\'ve forgotten a `}\', causing me to apply this";
                                            help_line[1] =
                                                        b"control sequence to too much text. How can we recover?";
                                            help_line[0] =
                                                        b"My plan is to forget the whole thing and hope for the best.";
                                            back_error();
                                        }
                                        pstack[n as usize] = MEM[(4999999 - 3) as usize].b32.s1;
                                        align_state = align_state - unbalance;
                                        m = 0i32;
                                        while m <= n as i32 {
                                            flush_list(pstack[m as usize]);
                                            m += 1
                                        }
                                        current_block = 16670727159935121194;
                                        break 's_135;
                                    }
                                }
                                if !(cur_tok < 0x600000i32) {
                                    continue;
                                }
                                if cur_tok < 0x400000i32 {
                                    unbalance += 1
                                } else {
                                    unbalance -= 1;
                                    if unbalance == 0i32 {
                                        break;
                                    }
                                }
                            }
                            rbrace_ptr = p;
                            q = get_avail();
                            MEM[p as usize].b32.s1 = q;
                            MEM[q as usize].b32.s0 = cur_tok;
                            p = q
                        } else {
                            back_input();
                            if file_line_error_style_p != 0 {
                                print_file_line();
                            } else {
                                print_nl_cstr(b"! ");
                            }
                            print_cstr(b"Argument of ");
                            sprint_cs(warning_index);
                            print_cstr(b" has an extra }");
                            help_ptr = 6_u8;
                            help_line[5] =
                                b"I\'ve run across a `}\' that doesn\'t seem to match anything.";
                            help_line[4] =
                                b"For example, `\\def\\a#1{...}\' and `\\a}\' would produce";
                            help_line[3] =
                                b"this error. If you simply proceed now, the `\\par\' that";
                            help_line[2] = b"I\'ve just inserted will cause me to report a runaway";
                            help_line[1] =
                                b"argument that might be the root of the problem. But if";
                            help_line[0] =
                                b"your `}\' was spurious, just type `2\' and it will go away.";
                            align_state += 1;
                            long_state = 113_u8;
                            cur_tok = par_token;
                            ins_error();
                            continue;
                        }
                    } else {
                        if cur_tok == 0x1400020i32 {
                            if MEM[r as usize].b32.s0 <= 0x1c00000 {
                                if MEM[r as usize].b32.s0 >= 0x1a00000 {
                                    continue;
                                }
                            }
                        }
                        q = get_avail();
                        MEM[p as usize].b32.s1 = q;
                        MEM[q as usize].b32.s0 = cur_tok;
                        p = q
                    }
                    m += 1;
                    if MEM[r as usize].b32.s0 > 0x1c00000 {
                        continue;
                    }
                    if !(MEM[r as usize].b32.s0 < 0x1a00000) {
                        break;
                    }
                }
            }
            if s != TEX_NULL {
                /*418:*/
                if m == 1i32 && MEM[p as usize].b32.s0 < 0x600000 && p != 4999999 - 3 {
                    MEM[rbrace_ptr as usize].b32.s1 = TEX_NULL;
                    MEM[p as usize].b32.s1 = avail;
                    avail = p;
                    p = MEM[(4999999 - 3) as usize].b32.s1;
                    pstack[n as usize] = MEM[p as usize].b32.s1;
                    MEM[p as usize].b32.s1 = avail;
                    avail = p
                } else {
                    pstack[n as usize] = MEM[(4999999 - 3) as usize].b32.s1
                }
                n += 1;
                if EQTB[(INT_BASE + 30i32) as usize].b32.s1 > 0i32 {
                    begin_diagnostic();
                    print_nl(match_chr as str_number);
                    print_int(n as i32);
                    print_cstr(b"<-");
                    show_token_list(pstack[(n as i32 - 1i32) as usize], TEX_NULL, 1000i32);
                    end_diagnostic(false);
                }
            }
            if !(MEM[r as usize].b32.s0 != 0x1c00000) {
                current_block = 12717620301112128284;
                break;
            }
        }
    } else {
        current_block = 12717620301112128284;
    }
    match current_block {
        12717620301112128284 => {
            while cur_input.state as i32 == 0i32
                && cur_input.loc == TEX_NULL
                && cur_input.index as i32 != 2i32
            {
                end_token_list();
            }
            begin_token_list(ref_count, 6_u16);
            cur_input.name = warning_index;
            cur_input.loc = MEM[r as usize].b32.s1;
            if n as i32 > 0i32 {
                if PARAM_PTR + n as usize > MAX_PARAM_STACK {
                    MAX_PARAM_STACK = PARAM_PTR + n as usize;
                    if MAX_PARAM_STACK > PARAM_SIZE {
                        overflow(b"parameter stack size", PARAM_SIZE as i32);
                    }
                }
                m = 0i32;
                while m <= n as i32 - 1i32 {
                    PARAM_STACK[PARAM_PTR + m as usize] = pstack[m as usize];
                    m += 1
                }
                PARAM_PTR += n as usize;
            }
        }
        _ => {}
    }
    scanner_status = save_scanner_status as u8;
    warning_index = save_warning_index;
}
pub(crate) unsafe fn insert_relax() {
    cur_tok = 0x1ffffffi32 + cur_cs;
    back_input();
    cur_tok = 0x1ffffffi32 + (FROZEN_CONTROL_SEQUENCE + 7i32);
    back_input();
    cur_input.index = 5_u16;
}
pub(crate) unsafe fn new_index(mut i: u16, mut q: i32) {
    let mut k: small_number = 0;
    cur_ptr = get_node(33i32);
    MEM[cur_ptr as usize].b16.s1 = i;
    MEM[cur_ptr as usize].b16.s0 = 0_u16;
    MEM[cur_ptr as usize].b32.s1 = q;
    let mut for_end: i32 = 0;
    k = 1i32 as small_number;
    for_end = 33i32 - 1i32;
    if k as i32 <= for_end {
        loop {
            MEM[(cur_ptr + k as i32) as usize] = sa_null;
            let fresh28 = k;
            k = k + 1;
            if !((fresh28 as i32) < for_end) {
                break;
            }
        }
    };
}
pub(crate) unsafe fn find_sa_element(mut t: small_number, mut n: i32, mut w: bool) {
    let mut current_block: u64;
    let mut q: i32 = 0;
    let mut i: small_number = 0;
    cur_ptr = sa_root[t as usize];
    if cur_ptr == TEX_NULL {
        if w {
            new_index(t as u16, TEX_NULL);
            sa_root[t as usize] = cur_ptr;
            q = cur_ptr;
            i = (n / 0x40000i32) as small_number
        } else {
            return;
        }
        current_block = 15806769474000922024;
    } else {
        q = cur_ptr;
        i = (n / 0x40000i32) as small_number;
        if i as i32 & 1i32 != 0 {
            cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s1
        } else {
            cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s0
        }
        if cur_ptr == TEX_NULL {
            if w {
                current_block = 15806769474000922024;
            } else {
                return;
            }
        } else {
            q = cur_ptr;
            i = (n / 4096i32 % 64i32) as small_number;
            if i as i32 & 1i32 != 0 {
                cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s1
            } else {
                cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s0
            }
            if cur_ptr == TEX_NULL {
                if w {
                    current_block = 14787586673191526541;
                } else {
                    return;
                }
            } else {
                q = cur_ptr;
                i = (n / 64i32 % 64i32) as small_number;
                if i as i32 & 1i32 != 0 {
                    cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s1
                } else {
                    cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s0
                }
                if cur_ptr == TEX_NULL {
                    if w {
                        current_block = 9497429165911859091;
                    } else {
                        return;
                    }
                } else {
                    q = cur_ptr;
                    i = (n % 64i32) as small_number;
                    if i as i32 & 1i32 != 0 {
                        cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s1
                    } else {
                        cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s0
                    }
                    if cur_ptr == TEX_NULL && w as i32 != 0 {
                        current_block = 10182473981606373355;
                    } else {
                        return;
                    }
                }
            }
        }
    }
    match current_block {
        15806769474000922024 => {
            /*not_found1 */
            new_index(i as u16, q);
            if i as i32 & 1i32 != 0 {
                MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = cur_ptr
            } else {
                MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = cur_ptr
            }
            MEM[q as usize].b16.s0 += 1;
            q = cur_ptr;
            i = (n / 4096i32 % 64i32) as small_number;
            current_block = 14787586673191526541;
        }
        _ => {}
    }
    match current_block {
        14787586673191526541 => {
            /*not_found2 */
            new_index(i as u16, q);
            if i as i32 & 1i32 != 0 {
                MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = cur_ptr
            } else {
                MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = cur_ptr
            }
            MEM[q as usize].b16.s0 += 1;
            q = cur_ptr;
            i = (n / 64i32 % 64i32) as small_number;
            current_block = 9497429165911859091;
        }
        _ => {}
    }
    match current_block {
        9497429165911859091 => {
            /*not_found3 */
            new_index(i as u16, q);
            if i as i32 & 1i32 != 0 {
                MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = cur_ptr
            } else {
                MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = cur_ptr
            }
            MEM[q as usize].b16.s0 += 1;
            q = cur_ptr;
            i = (n % 64i32) as small_number
        }
        _ => {}
    }
    /*not_found4 *//*1608: */
    if t as i32 == 7i32 {
        cur_ptr = get_node(4i32); /*level_one *//*:1608 */
        MEM[(cur_ptr + 1) as usize] = sa_null;
        MEM[(cur_ptr + 2) as usize] = sa_null;
        MEM[(cur_ptr + 3) as usize] = sa_null
    } else {
        if t as i32 <= 1i32 {
            cur_ptr = get_node(3i32);
            MEM[(cur_ptr + 2) as usize].b32.s1 = 0;
            MEM[(cur_ptr + 1) as usize].b32.s1 = n
        } else {
            cur_ptr = get_node(2i32);
            if t as i32 <= 3i32 {
                MEM[(cur_ptr + 1) as usize].b32.s1 = 0;
                MEM[0].b32.s1 += 1;
            } else {
                MEM[(cur_ptr + 1) as usize].b32.s1 = TEX_NULL
            }
        }
        MEM[(cur_ptr + 1) as usize].b32.s0 = TEX_NULL
    }
    MEM[cur_ptr as usize].b16.s1 = (64 * t as i32 + i as i32) as u16;
    MEM[cur_ptr as usize].b16.s0 = 1_u16;
    MEM[cur_ptr as usize].b32.s1 = q;
    if i as i32 & 1i32 != 0 {
        MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = cur_ptr
    } else {
        MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = cur_ptr
    }
    MEM[q as usize].b16.s0 += 1;
}
pub(crate) unsafe fn expand() {
    let mut t: i32 = 0;
    let mut b: bool = false;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut j: i32 = 0;
    let mut cv_backup: i32 = 0;
    let mut cvl_backup: small_number = 0;
    let mut radix_backup: small_number = 0;
    let mut co_backup: small_number = 0;
    let mut backup_backup: i32 = 0;
    let mut save_scanner_status: small_number = 0;
    expand_depth_count += 1;
    if expand_depth_count >= expand_depth {
        overflow(b"expansion depth", expand_depth);
    }
    cv_backup = cur_val;
    cvl_backup = cur_val_level as small_number;
    radix_backup = radix;
    co_backup = cur_order as small_number;
    backup_backup = MEM[(4999999 - 13) as usize].b32.s1;
    loop {
        if (cur_cmd as i32) < 113i32 {
            /*384:*/
            if EQTB[(INT_BASE + 36i32) as usize].b32.s1 > 1i32 {
                show_cur_cmd_chr(); /*1612:*/
            }
            match cur_cmd as i32 {
                112 => {
                    t = cur_chr % 5i32;
                    if cur_chr >= 5i32 {
                        scan_register_num();
                    } else {
                        cur_val = 0i32
                    }
                    if cur_val == 0i32 {
                        cur_ptr = cur_mark[t as usize]
                    } else {
                        find_sa_element(7i32 as small_number, cur_val, false);
                        if cur_ptr != TEX_NULL {
                            if t & 1i32 != 0 {
                                cur_ptr = MEM[(cur_ptr + t / 2 + 1) as usize].b32.s1
                            } else {
                                cur_ptr = MEM[(cur_ptr + t / 2 + 1) as usize].b32.s0
                            }
                        }
                    }
                    if cur_ptr != TEX_NULL {
                        begin_token_list(cur_ptr, 15_u16);
                    }
                    break;
                }
                104 => {
                    /*385:*/
                    if cur_chr == 0i32 {
                        get_token(); /*1553: "\unless" implementation */
                        t = cur_tok;
                        get_token();
                        if cur_cmd as i32 > 102i32 {
                            expand();
                        } else {
                            back_input();
                        }
                        cur_tok = t;
                        back_input();
                        break;
                    } else {
                        get_token();
                        if cur_cmd as i32 == 107i32 && cur_chr != 16i32 {
                            cur_chr = cur_chr + 32i32
                        } else {
                            if file_line_error_style_p != 0 {
                                print_file_line();
                            } else {
                                print_nl_cstr(b"! ");
                            }
                            print_cstr(b"You can\'t use `");
                            print_esc_cstr(b"unless");
                            print_cstr(b"\' before `");
                            print_cmd_chr(cur_cmd as u16, cur_chr);
                            print_char('\'' as i32);
                            help_ptr = 1_u8;
                            help_line[0] = b"Continue, and I\'ll forget that it ever happened.";
                            back_error();
                            break;
                        }
                    }
                }
                105 => {
                    /*386:*/
                    if cur_chr == 0i32 {
                        save_scanner_status = scanner_status as small_number; /*387: \primitive implementation */
                        scanner_status = 0_u8;
                        get_token();
                        scanner_status = save_scanner_status as u8;
                        t = cur_tok;
                        back_input();
                        if t >= 0x1ffffffi32 {
                            p = get_avail();
                            MEM[p as usize].b32.s0 = 0x1ffffff
                                + (1i32
                                    + (0x10ffffi32 + 1i32)
                                    + (0x10ffffi32 + 1i32)
                                    + 1i32
                                    + 15000i32
                                    + 9i32);
                            MEM[p as usize].b32.s1 = cur_input.loc;
                            cur_input.start = p;
                            cur_input.loc = p
                        }
                        break;
                    } else {
                        save_scanner_status = scanner_status as small_number;
                        scanner_status = 0_u8;
                        get_token();
                        scanner_status = save_scanner_status as u8;
                        if cur_cs < 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) + 1i32 {
                            cur_cs = prim_lookup(cur_cs - (1i32 + (0x10ffffi32 + 1i32)))
                        } else {
                            cur_cs = prim_lookup((*hash.offset(cur_cs as isize)).s1)
                        }
                        if !(cur_cs != 0i32) {
                            break;
                        }
                        t = prim_eqtb[cur_cs as usize].b16.s1 as i32;
                        if t > 102i32 {
                            cur_cmd = t as eight_bits;
                            cur_chr = prim_eqtb[cur_cs as usize].b32.s1;
                            cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr;
                            cur_cs = 0i32
                        } else {
                            back_input();
                            p = get_avail();
                            MEM[p as usize].b32.s0 = 0x1ffffff
                                + (1i32
                                    + (0x10ffffi32 + 1i32)
                                    + (0x10ffffi32 + 1i32)
                                    + 1i32
                                    + 15000i32
                                    + 11i32);
                            MEM[p as usize].b32.s1 = cur_input.loc;
                            cur_input.loc = p;
                            cur_input.start = p;
                            break;
                        }
                    }
                }
                109 => {
                    r = get_avail();
                    p = r;
                    b = is_in_csname;
                    is_in_csname = true;
                    loop {
                        get_x_token();
                        if cur_cs == 0i32 {
                            q = get_avail();
                            MEM[p as usize].b32.s1 = q;
                            MEM[q as usize].b32.s0 = cur_tok;
                            p = q
                        }
                        if !(cur_cs == 0i32) {
                            break;
                        }
                    }
                    if cur_cmd as i32 != 67i32 {
                        /*391:*/
                        if file_line_error_style_p != 0 {
                            print_file_line();
                        } else {
                            print_nl_cstr(b"! ");
                        }
                        print_cstr(b"Missing ");
                        print_esc_cstr(b"endcsname");
                        print_cstr(b" inserted");
                        help_ptr = 2_u8;
                        help_line[1] = b"The control sequence marked <to be read again> should";
                        help_line[0] = b"not appear between \\csname and \\endcsname.";
                        back_error();
                    }
                    is_in_csname = b;
                    j = first;
                    p = MEM[r as usize].b32.s1;
                    while p != TEX_NULL {
                        if j >= max_buf_stack {
                            max_buf_stack = j + 1i32;
                            if max_buf_stack == buf_size {
                                overflow(b"buffer size", buf_size);
                            }
                        }
                        *buffer.offset(j as isize) = MEM[p as usize].b32.s0 % 0x200000;
                        j += 1;
                        p = MEM[p as usize].b32.s1
                    }
                    if j > first + 1i32 || *buffer.offset(first as isize) as i64 > 65535 {
                        no_new_control_sequence = false;
                        cur_cs = id_lookup(first, j - first);
                        no_new_control_sequence = true
                    } else if j == first {
                        cur_cs = 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32)
                    } else {
                        cur_cs = 1i32 + (0x10ffffi32 + 1i32) + *buffer.offset(first as isize)
                        /*:392*/
                    }
                    flush_list(r);
                    if EQTB[cur_cs as usize].b16.s1 as i32 == 103i32 {
                        eq_define(cur_cs, 0_u16, 0x10ffffi32 + 1i32);
                    }
                    cur_tok = cur_cs + 0x1ffffffi32;
                    back_input();
                    break;
                }
                110 => {
                    conv_toks();
                    break;
                }
                111 => {
                    ins_the_toks();
                    break;
                }
                107 => {
                    conditional();
                    break;
                }
                108 => {
                    if EQTB[(INT_BASE + 60i32) as usize].b32.s1 > 0i32 {
                        if EQTB[(INT_BASE + 36i32) as usize].b32.s1 <= 1i32 {
                            show_cur_cmd_chr();
                        }
                    }
                    if cur_chr > if_limit as i32 {
                        if if_limit as i32 == 1i32 {
                            insert_relax();
                        } else {
                            if file_line_error_style_p != 0 {
                                print_file_line();
                            } else {
                                print_nl_cstr(b"! ");
                            }
                            print_cstr(b"Extra ");
                            print_cmd_chr(108_u16, cur_chr);
                            help_ptr = 1_u8;
                            help_line[0] = b"I\'m ignoring this; it doesn\'t match any \\if.";
                            error();
                        }
                    } else {
                        while cur_chr != 2i32 {
                            pass_text();
                        }
                        if IF_STACK[IN_OPEN] == cond_ptr {
                            if_warning();
                        }
                        p = cond_ptr;
                        if_line = MEM[(p + 1) as usize].b32.s1;
                        cur_if = MEM[p as usize].b16.s0 as small_number;
                        if_limit = MEM[p as usize].b16.s1 as u8;
                        cond_ptr = MEM[p as usize].b32.s1;
                        free_node(p, 2i32);
                    }
                    break;
                }
                106 => {
                    if cur_chr == 1i32 {
                        /* \endinput */
                        force_eof = true
                    } else if cur_chr == 2i32 {
                        /*1537:*/
                        /* \scantokens */
                        pseudo_start();
                    } else if name_in_progress {
                        insert_relax();
                    } else {
                        /* \input */
                        start_input(ptr::null()); /*393:*/
                    }
                    break;
                }
                _ => {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Undefined control sequence");
                    help_ptr = 5_u8;
                    help_line[4] = b"The control sequence at the end of the top line";
                    help_line[3] = b"of your error message was never \\def\'ed. If you have";
                    help_line[2] = b"misspelled it (e.g., `\\hobx\'), type `I\' and the correct";
                    help_line[1] = b"spelling (e.g., `I\\hbox\'). Otherwise just continue,";
                    help_line[0] = b"and I\'ll forget about whatever was undefined.";
                    error();
                    break;
                }
            }
        } else {
            if (cur_cmd as i32) < 117i32 {
                macro_call();
            } else {
                cur_tok = 0x1ffffffi32 + (FROZEN_CONTROL_SEQUENCE + 6i32);
                back_input();
            }
            break;
        }
    }
    cur_val = cv_backup;
    cur_val_level = cvl_backup as u8;
    radix = radix_backup;
    cur_order = co_backup as glue_ord;
    MEM[(4999999 - 13) as usize].b32.s1 = backup_backup;
    expand_depth_count -= 1;
}
pub(crate) unsafe fn get_x_token() {
    loop {
        get_next();
        if cur_cmd as i32 <= 102i32 {
            break;
        }
        if cur_cmd as i32 >= 113i32 {
            if (cur_cmd as i32) < 117i32 {
                macro_call();
            } else {
                cur_cs = FROZEN_CONTROL_SEQUENCE + 6i32;
                cur_cmd = 9i32 as eight_bits;
                break;
            }
        } else {
            expand();
        }
    }
    if cur_cs == 0i32 {
        cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr
    } else {
        cur_tok = 0x1ffffffi32 + cur_cs
    };
}
pub(crate) unsafe fn x_token() {
    while cur_cmd as i32 > 102i32 {
        expand();
        get_next();
    }
    if cur_cs == 0i32 {
        cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr
    } else {
        cur_tok = 0x1ffffffi32 + cur_cs
    };
}
pub(crate) unsafe fn scan_left_brace() {
    loop {
        get_x_token();
        if !(cur_cmd as i32 == 10i32 || cur_cmd as i32 == 0i32) {
            break;
        }
    }
    if cur_cmd as i32 != 1i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Missing { inserted");
        help_ptr = 4_u8;
        help_line[3] = b"A left brace was mandatory here, so I\'ve put one in.";
        help_line[2] = b"You might want to delete and/or insert some corrections";
        help_line[1] = b"so that I will find a matching right brace soon.";
        help_line[0] = b"(If you\'re confused by all this, try typing `I}\' now.)";
        back_error();
        cur_tok = 0x200000i32 + '{' as i32;
        cur_cmd = 1i32 as eight_bits;
        cur_chr = '{' as i32;
        align_state += 1
    };
}
pub(crate) unsafe fn scan_optional_equals() {
    loop {
        get_x_token();
        if !(cur_cmd as i32 == 10i32) {
            break;
        }
    }
    if cur_tok != 0x1800000i32 + 61i32 {
        /*"="*/
        back_input();
    };
}

pub(crate) unsafe fn scan_keyword(s: &[u8]) -> bool {
    let mut p: i32 = BACKUP_HEAD;
    let mut q: i32 = 0;
    MEM[p as usize].b32.s1 = TEX_NULL;
    if s.len() == 1 {
        let mut c: i8 = s[0] as i8;
        loop {
            get_x_token();
            if cur_cs == 0i32 && (cur_chr == c as i32 || cur_chr == c as i32 - 32i32) {
                q = get_avail();
                MEM[p as usize].b32.s1 = q;
                MEM[q as usize].b32.s0 = cur_tok;
                p = q;
                flush_list(MEM[BACKUP_HEAD as usize].b32.s1);
                return true;
            } else {
                if cur_cmd as i32 != SPACER as _ || p != BACKUP_HEAD {
                    back_input();
                    if p != BACKUP_HEAD {
                        begin_token_list(MEM[BACKUP_HEAD as usize].b32.s1, BACKED_UP);
                    }
                    return false;
                }
            }
        }
    }
    let slen = s.len();
    let mut i = 0;
    while i < slen {
        get_x_token();
        if cur_cs == 0i32
            && (cur_chr == s[i as usize] as i8 as i32
                || cur_chr == s[i as usize] as i8 as i32 - 32i32)
        {
            q = get_avail();
            MEM[p as usize].b32.s1 = q;
            MEM[q as usize].b32.s0 = cur_tok;
            p = q;
            i = i.wrapping_add(1)
        } else if cur_cmd as i32 != SPACER as _ || p != BACKUP_HEAD {
            back_input();
            if p != BACKUP_HEAD {
                begin_token_list(MEM[BACKUP_HEAD as usize].b32.s1, BACKED_UP);
            }
            return false;
        }
    }
    flush_list(MEM[BACKUP_HEAD as usize].b32.s1);
    true
}

pub(crate) unsafe fn mu_error() {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Incompatible glue units");
    help_ptr = 1_u8;
    help_line[0] = b"I\'m going to assume that 1mu=1pt when they\'re mixed.";
    error();
}
pub(crate) unsafe fn scan_glyph_number(mut f: internal_font_number) {
    if scan_keyword(b"/") {
        scan_and_pack_name();
        cur_val = map_glyph_to_index(f);
        cur_val_level = 0_u8
    } else if scan_keyword(b"u") {
        scan_char_num();
        cur_val = map_char_to_glyph(f, cur_val);
        cur_val_level = 0_u8
    } else {
        scan_int();
    };
}
pub(crate) unsafe fn scan_char_class() {
    scan_int();
    if cur_val < 0i32 || cur_val > 4096i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad character class");
        help_ptr = 2_u8;
        help_line[1] = b"A character class must be between 0 and 4096.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_char_class_not_ignored() {
    scan_int();
    if cur_val < 0i32 || cur_val > 4096i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad character class");
        help_ptr = 2_u8;
        help_line[1] = b"A class for inter-character transitions must be between 0 and 4095.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_eight_bit_int() {
    scan_int();
    if cur_val < 0i32 || cur_val > 255i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad register code");
        help_ptr = 2_u8;
        help_line[1] = b"A register code or char class must be between 0 and 255.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_usv_num() {
    scan_int();
    if cur_val < 0i32 || cur_val > 0x10ffffi32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad character code");
        help_ptr = 2_u8;
        help_line[1] = b"A Unicode scalar value must be between 0 and \"10FFFF.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_char_num() {
    scan_int();
    if cur_val < 0i32 || cur_val > 0xffffi32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad character code");
        help_ptr = 2_u8;
        help_line[1] = b"A character number must be between 0 and 65535.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_xetex_math_char_int() {
    scan_int();
    if cur_val as u32 & 0x1fffff_u32 == 0x1fffff_u32 {
        if cur_val != 0x1fffffi32 {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Bad active XeTeX math code");
            help_ptr = 2_u8;
            help_line[1] = b"Since I ignore class and family for active math chars,";
            help_line[0] = b"I changed this one to \"1FFFFF.";
            int_error(cur_val);
            cur_val = 0x1fffffi32
        }
    } else if cur_val as u32 & 0x1fffff_u32 > 0x10ffff_u32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad XeTeX math character code");
        help_ptr = 2_u8;
        help_line[1] = b"Since I expected a character number between 0 and \"10FFFF,";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_math(mut p: i32) {
    let mut c: i32 = 0;
    'c_118470: loop {
        loop
        /*422:*/
        {
            get_x_token();
            if !(cur_cmd as i32 == 10i32 || cur_cmd as i32 == 0i32) {
                break;
            }
        }
        loop {
            match cur_cmd as i32 {
                11 | 12 | 68 => {
                    c = EQTB[(MATH_CODE_BASE + cur_chr) as usize].b32.s1;
                    if !(c as u32 & 0x1fffff_u32 == 0x1fffff_u32) {
                        break 'c_118470;
                    }
                    cur_cs = cur_chr + 1i32;
                    cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits;
                    cur_chr = EQTB[cur_cs as usize].b32.s1;
                    x_token();
                    back_input();
                    break;
                }
                16 => {
                    scan_char_num();
                    cur_chr = cur_val;
                    cur_cmd = 68i32 as eight_bits
                }
                17 => {
                    if cur_chr == 2i32 {
                        scan_math_class_int();
                        c = ((cur_val as u32 & 0x7_u32) << 21i32) as i32;
                        scan_math_fam_int();
                        c = (c as u32).wrapping_add((cur_val as u32 & 0xff_u32) << 24i32) as i32;
                        scan_usv_num();
                        c = c + cur_val
                    } else if cur_chr == 1i32 {
                        scan_xetex_math_char_int();
                        c = cur_val
                    } else {
                        scan_fifteen_bit_int();
                        c = (((cur_val / 4096i32) as u32 & 0x7_u32) << 21i32)
                            .wrapping_add(((cur_val % 4096i32 / 256i32) as u32 & 0xff_u32) << 24i32)
                            .wrapping_add((cur_val % 256i32) as u32)
                            as i32
                    }
                    break 'c_118470;
                }
                69 => {
                    c = (((cur_chr / 4096i32) as u32 & 0x7_u32) << 21i32)
                        .wrapping_add(((cur_chr % 4096i32 / 256i32) as u32 & 0xff_u32) << 24i32)
                        .wrapping_add((cur_chr % 256i32) as u32) as i32;
                    break 'c_118470;
                }
                70 => {
                    c = cur_chr;
                    break 'c_118470;
                }
                15 => {
                    if cur_chr == 1i32 {
                        scan_math_class_int();
                        c = ((cur_val as u32 & 0x7_u32) << 21i32) as i32;
                        scan_math_fam_int();
                        c = (c as u32).wrapping_add((cur_val as u32 & 0xff_u32) << 24i32) as i32;
                        scan_usv_num();
                        c = c + cur_val
                    } else {
                        scan_delimiter_int();
                        c = cur_val / 4096i32;
                        c = (((c / 4096i32) as u32 & 0x7_u32) << 21i32)
                            .wrapping_add(((c % 4096i32 / 256i32) as u32 & 0xff_u32) << 24i32)
                            .wrapping_add((c % 256i32) as u32) as i32
                    }
                    break 'c_118470;
                }
                _ => {
                    back_input();
                    scan_left_brace();
                    SAVE_STACK[SAVE_PTR + 0].b32.s1 = p;
                    SAVE_PTR += 1;
                    push_math(9i32 as group_code);
                    return;
                }
            }
        }
    }
    MEM[p as usize].b32.s1 = 1;
    MEM[p as usize].b16.s0 = (c as i64 % 65536) as u16;
    if c as u32 >> 21i32 & 0x7_u32 == 7_u32
        && (EQTB[(INT_BASE + 44i32) as usize].b32.s1 >= 0i32
            && EQTB[(INT_BASE + 44i32) as usize].b32.s1 < 256i32)
    {
        MEM[p as usize].b16.s1 = EQTB[(INT_BASE + 44i32) as usize].b32.s1 as u16
    } else {
        MEM[p as usize].b16.s1 = (c as u32 >> 24 & 0xff_u32) as u16
    }
    MEM[p as usize].b16.s1 = (MEM[p as usize].b16.s1 as i64
        + (c as u32 & 0x1fffff_u32) as i64 / 65536 * 256i32 as i64)
        as u16;
}
pub(crate) unsafe fn set_math_char(mut c: i32) {
    let mut p: i32 = 0;
    let mut ch: UnicodeScalar = 0;
    if c as u32 & 0x1fffff_u32 == 0x1fffff_u32 {
        /*1187: */
        cur_cs = cur_chr + 1i32; /* ... "between 0 and 15" */
        cur_cmd = EQTB[cur_cs as usize].b16.s1 as eight_bits; /* ... "between 0 and 15" */
        cur_chr = EQTB[cur_cs as usize].b32.s1;
        x_token();
        back_input();
    } else {
        p = new_noad();
        MEM[(p + 1) as usize].b32.s1 = 1;
        ch = (c as u32 & 0x1fffff_u32) as UnicodeScalar;
        MEM[(p + 1) as usize].b16.s0 = (ch as i64 % 65536) as u16;
        MEM[(p + 1) as usize].b16.s1 = (c as u32 >> 24 & 0xff_u32) as u16;
        if c as u32 >> 21i32 & 0x7_u32 == 7_u32 {
            if EQTB[(INT_BASE + 44i32) as usize].b32.s1 >= 0i32
                && EQTB[(INT_BASE + 44i32) as usize].b32.s1 < 256i32
            {
                MEM[(p + 1) as usize].b16.s1 = EQTB[(INT_BASE + 44i32) as usize].b32.s1 as u16
            }
            MEM[p as usize].b16.s1 = 16_u16
        } else {
            MEM[p as usize].b16.s1 = (16_u32).wrapping_add(c as u32 >> 21 & 0x7_u32) as u16
        }
        MEM[(p + 1) as usize].b16.s1 =
            (MEM[(p + 1) as usize].b16.s1 as i64 + ch as i64 / 65536 * 256 as i64) as u16;
        MEM[cur_list.tail as usize].b32.s1 = p;
        cur_list.tail = p
    };
}
pub(crate) unsafe fn scan_math_class_int() {
    scan_int();
    if cur_val < 0i32 || cur_val > 7i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad math class");
        help_ptr = 2_u8;
        help_line[1] = b"Since I expected to read a number between 0 and 7,";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_math_fam_int() {
    scan_int();
    if cur_val < 0i32 || cur_val > 256i32 - 1i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad math family");
        help_ptr = 2_u8;
        help_line[1] = b"Since I expected to read a number between 0 and 255,";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_four_bit_int() {
    scan_int();
    if cur_val < 0i32 || cur_val > 15i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad number");
        help_ptr = 2_u8;
        help_line[1] = b"Since I expected to read a number between 0 and 15,";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_fifteen_bit_int() {
    scan_int();
    if cur_val < 0i32 || cur_val > 32767i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad mathchar");
        help_ptr = 2_u8;
        help_line[1] = b"A mathchar number must be between 0 and 32767.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_delimiter_int() {
    scan_int();
    if cur_val < 0i32 || cur_val > 0x7ffffffi32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad delimiter code");
        help_ptr = 2_u8;
        help_line[1] = b"A numeric delimiter code must be between 0 and 2^{27}-1.";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_register_num() {
    scan_int();
    if cur_val < 0i32 || cur_val > max_reg_num {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad register code");
        help_ptr = 2_u8;
        help_line[1] = max_reg_help_line;
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn scan_four_bit_int_or_18() {
    scan_int();
    if cur_val < 0i32 || cur_val > 15i32 && cur_val != 18i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad number");
        help_ptr = 2_u8;
        help_line[1] = b"Since I expected to read a number between 0 and 15,";
        help_line[0] = b"I changed this one to zero.";
        int_error(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn get_x_or_protected() {
    loop {
        get_token();
        if cur_cmd as i32 <= 102i32 {
            return;
        }
        if cur_cmd as i32 >= 113i32 && (cur_cmd as i32) < 117i32 {
            if MEM[MEM[cur_chr as usize].b32.s1 as usize].b32.s0 == 0x1c00000 + 1 {
                return;
            }
        }
        expand();
    }
}
pub(crate) unsafe fn effective_char(
    mut _err_p: bool,
    mut f: internal_font_number,
    mut c: u16,
) -> i32 {
    if !xtx_ligature_present && !(FONT_MAPPING[f as usize]).is_null() {
        c = apply_tfm_font_mapping(FONT_MAPPING[f as usize], c as i32) as u16
    }
    xtx_ligature_present = false;
    c as i32
}
pub(crate) unsafe fn scan_font_ident() {
    let mut f: internal_font_number = 0;
    let mut m: i32 = 0;
    loop {
        get_x_token();
        if !(cur_cmd as i32 == 10i32) {
            break;
        }
    }
    if cur_cmd as i32 == 90i32 {
        f = EQTB[(CUR_FONT_LOC) as usize].b32.s1
    } else if cur_cmd as i32 == 89i32 {
        f = cur_chr
    } else if cur_cmd as i32 == 88i32 {
        m = cur_chr;
        scan_math_fam_int();
        f = EQTB[(m + cur_val) as usize].b32.s1
    } else {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Missing font identifier");
        help_ptr = 2_u8;
        help_line[1] = b"I was looking for a control sequence whose";
        help_line[0] = b"current meaning has been defined by \\font.";
        back_error();
        f = 0i32
    }
    cur_val = f;
}
pub(crate) unsafe fn find_font_dimen(mut writing: bool) {
    let mut f: internal_font_number = 0;
    let mut n: i32 = 0;
    scan_int();
    n = cur_val;
    scan_font_ident();
    f = cur_val;
    if n <= 0i32 {
        cur_val = fmem_ptr
    } else {
        if writing as i32 != 0 && n <= 4i32 && n >= 2i32 && FONT_GLUE[f as usize] != TEX_NULL {
            delete_glue_ref(FONT_GLUE[f as usize]);
            FONT_GLUE[f as usize] = TEX_NULL
        }
        if n > FONT_PARAMS[f as usize] {
            if f < font_ptr {
                cur_val = fmem_ptr
            } else {
                loop
                /*599: */
                {
                    if fmem_ptr == FONT_MEM_SIZE as i32 {
                        overflow(b"font memory", FONT_MEM_SIZE as i32);
                    }
                    FONT_INFO[fmem_ptr as usize].b32.s1 = 0;
                    fmem_ptr += 1;
                    FONT_PARAMS[f as usize] += 1;
                    if n == FONT_PARAMS[f as usize] {
                        break;
                    }
                }
                cur_val = fmem_ptr - 1i32
            }
        } else {
            cur_val = n + PARAM_BASE[f as usize]
        }
    }
    if cur_val == fmem_ptr {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Font ");
        print_esc((*hash.offset((FROZEN_CONTROL_SEQUENCE + 12i32 + f) as isize)).s1);
        print_cstr(b" has only ");
        print_int(FONT_PARAMS[f as usize]);
        print_cstr(b" fontdimen parameters");
        help_ptr = 2_u8;
        help_line[1] = b"To increase the number of font parameters, you must";
        help_line[0] = b"use \\fontdimen immediately after the \\font is loaded.";
        error();
    };
}
pub(crate) unsafe fn scan_something_internal(mut level: small_number, mut negative: bool) {
    let mut m: i32 = 0;
    let mut n: i32 = 0;
    let mut k: i32 = 0;
    let mut kk: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut tx: i32 = 0;
    let mut i: b16x4 = b16x4 {
        s0: 0,
        s1: 0,
        s2: 0,
        s3: 0,
    };
    let mut p: i32 = 0;
    m = cur_chr;
    match cur_cmd as i32 {
        86 => {
            scan_usv_num();
            if m == MATH_CODE_BASE {
                cur_val1 = EQTB[(MATH_CODE_BASE + cur_val) as usize].b32.s1;
                if cur_val1 as u32 & 0x1fffff_u32 == 0x1fffff_u32 {
                    cur_val1 = 0x8000i32
                } else if cur_val1 as u32 >> 21i32 & 0x7_u32 > 7_u32
                    || cur_val1 as u32 >> 24i32 & 0xff_u32 > 15_u32
                    || cur_val1 as u32 & 0x1fffff_u32 > 255_u32
                {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Extended mathchar used as mathchar");
                    help_ptr = 2_u8;
                    help_line[1] = b"A mathchar number must be between 0 and \"7FFF.";
                    help_line[0] = b"I changed this one to zero.";
                    int_error(cur_val1);
                    cur_val1 = 0i32
                }
                cur_val1 = (cur_val1 as u32 >> 21i32 & 0x7_u32)
                    .wrapping_mul(0x1000_u32)
                    .wrapping_add((cur_val1 as u32 >> 24i32 & 0xff_u32).wrapping_mul(0x100_u32))
                    .wrapping_add(cur_val1 as u32 & 0x1fffff_u32) as i32;
                cur_val = cur_val1;
                cur_val_level = 0_u8
            } else if m == DEL_CODE_BASE {
                cur_val1 = EQTB[(DEL_CODE_BASE + cur_val) as usize].b32.s1;
                if cur_val1 >= 0x40000000i32 {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Extended delcode used as delcode");
                    help_ptr = 2_u8;
                    help_line[1] = b"I can only go up to 2147483647=\'17777777777=\"7FFFFFFF,";
                    help_line[0] = b"I changed this one to zero.";
                    error();
                    cur_val = 0i32;
                    cur_val_level = 0_u8
                } else {
                    cur_val = cur_val1;
                    cur_val_level = 0_u8
                }
            } else if m < SF_CODE_BASE {
                cur_val = EQTB[(m + cur_val) as usize].b32.s1;
                cur_val_level = 0_u8
            } else if m < MATH_CODE_BASE {
                cur_val = (EQTB[(m + cur_val) as usize].b32.s1 as i64 % 65536) as i32;
                cur_val_level = 0_u8
            } else {
                cur_val = EQTB[(m + cur_val) as usize].b32.s1;
                cur_val_level = 0_u8
            }
        }
        87 => {
            scan_usv_num();
            if m == SF_CODE_BASE {
                cur_val = (EQTB[(SF_CODE_BASE + cur_val) as usize].b32.s1 as i64 / 65536) as i32;
                cur_val_level = 0_u8
            } else if m == MATH_CODE_BASE {
                cur_val = EQTB[(MATH_CODE_BASE + cur_val) as usize].b32.s1;
                cur_val_level = 0_u8
            } else if m == MATH_CODE_BASE + 1i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Can\'t use \\Umathcode as a number (try \\Umathcodenum)");
                help_ptr = 2_u8;
                help_line[1] = b"\\Umathcode is for setting a mathcode from separate values;";
                help_line[0] = b"use \\Umathcodenum to access them as single values.";
                error();
                cur_val = 0i32;
                cur_val_level = 0_u8
            } else if m == DEL_CODE_BASE {
                cur_val = EQTB[(DEL_CODE_BASE + cur_val) as usize].b32.s1;
                cur_val_level = 0_u8
            } else {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Can\'t use \\Udelcode as a number (try \\Udelcodenum)");
                help_ptr = 2_u8;
                help_line[1] = b"\\Udelcode is for setting a delcode from separate values;";
                help_line[0] = b"use \\Udelcodenum to access them as single values.";
                error();
                cur_val = 0i32;
                cur_val_level = 0_u8
            }
        }
        72 | 73 | 88 | 89 | 90 => {
            if level as i32 != 5i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Missing number, treated as zero");
                help_ptr = 3_u8;
                help_line[2] = b"A number should have been here; I inserted `0\'.";
                help_line[1] = b"(If you can\'t figure out why I needed to see a number,";
                help_line[0] = b"look up `weird error\' in the index to The TeXbook.)";
                back_error();
                cur_val = 0i32;
                cur_val_level = 1_u8
            } else if cur_cmd as i32 <= 73i32 {
                if (cur_cmd as i32) < 73i32 {
                    if m == 0i32 {
                        scan_register_num();
                        if cur_val < 256i32 {
                            cur_val = EQTB[(LOCAL_BASE + 13i32 + cur_val) as usize].b32.s1
                        } else {
                            find_sa_element(5i32 as small_number, cur_val, false);
                            if cur_ptr == TEX_NULL {
                                cur_val = TEX_NULL
                            } else {
                                cur_val = MEM[(cur_ptr + 1) as usize].b32.s1
                            }
                        }
                    } else {
                        cur_val = MEM[(m + 1) as usize].b32.s1
                    }
                } else if cur_chr == LOCAL_BASE + 11i32 {
                    scan_char_class_not_ignored();
                    cur_ptr = cur_val;
                    scan_char_class_not_ignored();
                    find_sa_element(6i32 as small_number, cur_ptr * 4096i32 + cur_val, false);
                    if cur_ptr == TEX_NULL {
                        cur_val = TEX_NULL
                    } else {
                        cur_val = MEM[(cur_ptr + 1) as usize].b32.s1
                    }
                } else {
                    cur_val = EQTB[m as usize].b32.s1
                }
                cur_val_level = 5_u8
            } else {
                back_input();
                scan_font_ident();
                cur_val = FONT_ID_BASE + cur_val;
                cur_val_level = 4_u8
            }
        }
        74 => {
            cur_val = EQTB[m as usize].b32.s1;
            cur_val_level = 0_u8
        }
        75 => {
            cur_val = EQTB[m as usize].b32.s1;
            cur_val_level = 1_u8
        }
        76 => {
            cur_val = EQTB[m as usize].b32.s1;
            cur_val_level = 2_u8
        }
        77 => {
            cur_val = EQTB[m as usize].b32.s1;
            cur_val_level = 3_u8
        }
        80 => {
            if (cur_list.mode as i32).abs() != m {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Improper ");
                print_cmd_chr(80_u16, m);
                help_ptr = 4_u8;
                help_line[3] = b"You can refer to \\spacefactor only in horizontal mode;";
                help_line[2] = b"you can refer to \\prevdepth only in vertical mode; and";
                help_line[1] = b"neither of these is meaningful inside \\write. So";
                help_line[0] = b"I\'m forgetting what you said and using zero instead.";
                error();
                if level as i32 != 5i32 {
                    cur_val = 0i32;
                    cur_val_level = 1_u8
                } else {
                    cur_val = 0i32;
                    cur_val_level = 0_u8
                }
            } else if m == 1i32 {
                cur_val = cur_list.aux.b32.s1;
                cur_val_level = 1_u8
            } else {
                cur_val = cur_list.aux.b32.s0;
                cur_val_level = 0_u8
            }
        }
        81 => {
            if cur_list.mode as i32 == 0i32 {
                cur_val = 0i32;
                cur_val_level = 0_u8
            } else {
                *nest.offset(nest_ptr as isize) = cur_list;
                p = nest_ptr;
                while ((*nest.offset(p as isize)).mode as i32).abs() != 1i32 {
                    p -= 1
                }
                cur_val = (*nest.offset(p as isize)).prev_graf;
                cur_val_level = 0_u8
            }
        }
        83 => {
            if m == 0i32 {
                cur_val = dead_cycles
            } else if m == 2i32 {
                cur_val = interaction as i32
            } else {
                cur_val = insert_penalties
            }
            cur_val_level = 0_u8
        }
        82 => {
            if page_contents as i32 == 0i32 && !output_active {
                if m == 0i32 {
                    cur_val = 0x3fffffffi32
                } else {
                    cur_val = 0i32
                }
            } else {
                cur_val = page_so_far[m as usize]
            }
            cur_val_level = 1_u8
        }
        85 => {
            if m > LOCAL_BASE + 0i32 {
                /*1654:*/
                scan_int();
                if EQTB[m as usize].b32.s1 == TEX_NULL || cur_val < 0i32 {
                    cur_val = 0i32
                } else {
                    if cur_val > MEM[(EQTB[m as usize].b32.s1 + 1) as usize].b32.s1 {
                        cur_val = MEM[(EQTB[m as usize].b32.s1 + 1) as usize].b32.s1
                    }
                    cur_val = MEM[(EQTB[m as usize].b32.s1 + cur_val + 1) as usize].b32.s1
                }
            } else if EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1 == TEX_NULL {
                cur_val = 0i32
            } else {
                cur_val = MEM[EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1 as usize]
                    .b32
                    .s0
            }
            cur_val_level = 0_u8
        }
        84 => {
            scan_register_num();
            if cur_val < 256i32 {
                q = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr == TEX_NULL {
                    q = TEX_NULL
                } else {
                    q = MEM[(cur_ptr + 1) as usize].b32.s1
                }
            }
            if q == TEX_NULL {
                cur_val = 0i32
            } else {
                cur_val = MEM[(q + m) as usize].b32.s1
            }
            cur_val_level = 1_u8
        }
        68 | 69 => {
            cur_val = cur_chr;
            cur_val_level = 0_u8
        }
        78 => {
            find_font_dimen(false);
            FONT_INFO[fmem_ptr as usize].b32.s1 = 0;
            cur_val = FONT_INFO[cur_val as usize].b32.s1;
            cur_val_level = 1_u8
        }
        79 => {
            scan_font_ident();
            if m == 0i32 {
                cur_val = HYPHEN_CHAR[cur_val as usize];
                cur_val_level = 0_u8
            } else if m == 1i32 {
                cur_val = SKEW_CHAR[cur_val as usize];
                cur_val_level = 0_u8
            } else {
                n = cur_val;
                if FONT_AREA[n as usize] as u32 == 0xffffu32
                    || FONT_AREA[n as usize] as u32 == 0xfffeu32
                {
                    scan_glyph_number(n);
                } else {
                    scan_char_num();
                }
                k = cur_val;
                match m {
                    2 => {
                        cur_val = get_cp_code(n, k as u32, 0i32);
                        cur_val_level = 0_u8
                    }
                    3 => {
                        cur_val = get_cp_code(n, k as u32, 1i32);
                        cur_val_level = 0_u8
                    }
                    _ => {}
                }
            }
        }
        91 => {
            if m < 0i32 || m > 19i32 {
                /* 19 = "lo_mem_stat_max" */
                cur_val_level = (MEM[m as usize].b16.s1 as i32 / 64) as u8;
                if (cur_val_level as i32) < 2i32 {
                    cur_val = MEM[(m + 2) as usize].b32.s1
                } else {
                    cur_val = MEM[(m + 1) as usize].b32.s1
                }
            } else {
                scan_register_num();
                cur_val_level = m as u8;
                if cur_val > 255i32 {
                    find_sa_element(cur_val_level as small_number, cur_val, false);
                    if cur_ptr == TEX_NULL {
                        cur_val = 0i32
                    } else if (cur_val_level as i32) < 2i32 {
                        cur_val = MEM[(cur_ptr + 2) as usize].b32.s1
                    } else {
                        cur_val = MEM[(cur_ptr + 1) as usize].b32.s1
                    }
                } else {
                    match cur_val_level as i32 {
                        0 => cur_val = EQTB[(COUNT_BASE + cur_val) as usize].b32.s1,
                        1 => {
                            cur_val = EQTB[(INT_BASE
                                + 85i32
                                + 256i32
                                + (0x10ffffi32 + 1i32)
                                + 23i32
                                + cur_val) as usize]
                                .b32
                                .s1
                        }
                        2 => {
                            cur_val = EQTB[(1i32
                                + (0x10ffffi32 + 1i32)
                                + (0x10ffffi32 + 1i32)
                                + 1i32
                                + 15000i32
                                + 12i32
                                + 9000i32
                                + 1i32
                                + 1i32
                                + 19i32
                                + cur_val) as usize]
                                .b32
                                .s1
                        }
                        3 => {
                            cur_val = EQTB[(1i32
                                + (0x10ffffi32 + 1i32)
                                + (0x10ffffi32 + 1i32)
                                + 1i32
                                + 15000i32
                                + 12i32
                                + 9000i32
                                + 1i32
                                + 1i32
                                + 19i32
                                + 256i32
                                + cur_val) as usize]
                                .b32
                                .s1
                        }
                        _ => {}
                    }
                }
            }
        }
        71 => {
            if m >= 4i32 {
                if m >= 57i32 {
                    /*1568:*/
                    if m < 58i32 {
                        match m {
                            57 => {
                                /*1595:*/
                                scan_mu_glue();
                            }
                            _ => {}
                        }
                        cur_val_level = 2_u8
                    } else if m < 59i32 {
                        match m {
                            58 => {
                                /*1596:*/
                                scan_normal_glue(); /* if(m >= XETEX_DIM) */
                            }
                            _ => {}
                        }
                        cur_val_level = 3_u8
                    } else {
                        cur_val_level = (m - 59i32) as u8;
                        scan_expr();
                    }
                    while cur_val_level as i32 > level as i32 {
                        if cur_val_level as i32 == 2i32 {
                            m = cur_val;
                            cur_val = MEM[(m + 1) as usize].b32.s1;
                            delete_glue_ref(m);
                        } else if cur_val_level as i32 == 3i32 {
                            mu_error();
                        }
                        cur_val_level = cur_val_level.wrapping_sub(1)
                    }
                    if negative {
                        if cur_val_level as i32 >= 2i32 {
                            m = cur_val;
                            cur_val = new_spec(m);
                            delete_glue_ref(m);
                            MEM[(cur_val + 1) as usize].b32.s1 =
                                -MEM[(cur_val + 1) as usize].b32.s1;
                            MEM[(cur_val + 2) as usize].b32.s1 =
                                -MEM[(cur_val + 2) as usize].b32.s1;
                            MEM[(cur_val + 3) as usize].b32.s1 = -MEM[(cur_val + 3) as usize].b32.s1
                        } else {
                            cur_val = -cur_val
                        }
                    }
                    return;
                }
                if m >= 47i32 {
                    match m {
                        47 => {
                            /*1435:*/
                            if FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32
                                == 0xffffu32
                                || FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32
                                    == 0xfffeu32
                            {
                                scan_int(); /* shellenabledp */
                                n = cur_val;
                                if n < 1i32 || n > 4i32 {
                                    if file_line_error_style_p != 0 {
                                        print_file_line();
                                    } else {
                                        print_nl_cstr(b"! ");
                                    }
                                    print_cstr(
                                        b"\\\\XeTeXglyphbounds requires an edge index from 1 to 4;",
                                    );
                                    print_nl_cstr(b"I don\'t know anything about edge ");
                                    print_int(n);
                                    error();
                                    cur_val = 0i32
                                } else {
                                    scan_int();
                                    cur_val = get_glyph_bounds(
                                        EQTB[(CUR_FONT_LOC) as usize].b32.s1,
                                        n,
                                        cur_val,
                                    )
                                }
                            } else {
                                not_native_font_error(
                                    71i32,
                                    m,
                                    EQTB[(CUR_FONT_LOC) as usize].b32.s1,
                                );
                                cur_val = 0i32
                            }
                        }
                        48 | 49 | 50 | 51 => {
                            scan_font_ident();
                            q = cur_val;
                            scan_usv_num();
                            if FONT_AREA[q as usize] as u32 == 0xffffu32
                                || FONT_AREA[q as usize] as u32 == 0xfffeu32
                            {
                                match m {
                                    48 => cur_val = getnativecharwd(q, cur_val),
                                    49 => cur_val = getnativecharht(q, cur_val),
                                    50 => cur_val = getnativechardp(q, cur_val),
                                    51 => cur_val = getnativecharic(q, cur_val),
                                    _ => {}
                                }
                            } else if FONT_BC[q as usize] as i32 <= cur_val
                                && FONT_EC[q as usize] as i32 >= cur_val
                            {
                                i = FONT_INFO[(CHAR_BASE[q as usize]
                                    + effective_char(1i32 != 0, q, cur_val as u16))
                                    as usize]
                                    .b16;
                                match m {
                                    48 => {
                                        cur_val = FONT_INFO
                                            [(WIDTH_BASE[q as usize] + i.s3 as i32) as usize]
                                            .b32
                                            .s1
                                    }
                                    49 => {
                                        cur_val = FONT_INFO[(HEIGHT_BASE[q as usize]
                                            + i.s2 as i32 / 16i32)
                                            as usize]
                                            .b32
                                            .s1
                                    }
                                    50 => {
                                        cur_val = FONT_INFO[(DEPTH_BASE[q as usize]
                                            + i.s2 as i32 % 16i32)
                                            as usize]
                                            .b32
                                            .s1
                                    }
                                    51 => {
                                        cur_val = FONT_INFO[(ITALIC_BASE[q as usize]
                                            + i.s1 as i32 / 4i32)
                                            as usize]
                                            .b32
                                            .s1
                                    }
                                    _ => {}
                                }
                            } else {
                                cur_val = 0i32
                            }
                        }
                        52 | 53 | 54 => {
                            q = cur_chr - 52i32;
                            scan_int();
                            if EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1 == TEX_NULL
                                || cur_val <= 0i32
                            {
                                cur_val = 0i32
                            } else {
                                if q == 2i32 {
                                    q = cur_val % 2i32;
                                    cur_val = (cur_val + q) / 2i32
                                }
                                if cur_val
                                    > MEM[EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1 as usize]
                                        .b32
                                        .s0
                                {
                                    cur_val = MEM
                                        [EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1 as usize]
                                        .b32
                                        .s0
                                }
                                cur_val = MEM[(EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1
                                    + 2i32 * cur_val
                                    - q) as usize]
                                    .b32
                                    .s1
                            }
                            cur_val_level = 1_u8
                        }
                        55 | 56 => {
                            scan_normal_glue();
                            q = cur_val;
                            if m == 55i32 {
                                cur_val = MEM[(q + 2) as usize].b32.s1
                            } else {
                                cur_val = MEM[(q + 3) as usize].b32.s1
                            }
                            delete_glue_ref(q);
                        }
                        _ => {}
                    }
                    cur_val_level = 1_u8
                } else {
                    match m {
                        4 => cur_val = line,
                        5 => cur_val = last_badness,
                        45 => cur_val = 0i32,
                        6 => cur_val = 2i32,
                        14 => cur_val = 0i32,
                        15 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    cur_val = aat::aat_font_get(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                    )
                                }
                                0xfffeu32 => {
                                    cur_val = ot_font_get(m - 14i32, FONT_LAYOUT_ENGINE[n as usize])
                                }
                                _ => cur_val = 0i32,
                            }
                        }
                        22 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    cur_val = aat::aat_font_get(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                    )
                                }
                                #[cfg(not(target_os = "macos"))]
                                0xffffu32 => cur_val = -1,
                                0xfffeu32 => {
                                    if usingGraphite(
                                        FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                    ) as i32
                                        != 0
                                    {
                                        cur_val =
                                            ot_font_get(m - 14i32, FONT_LAYOUT_ENGINE[n as usize]);
                                    } else {
                                        cur_val = 0;
                                    }
                                }
                                _ => cur_val = 0,
                            }
                        }
                        17 | 19 | 20 | 21 | 16 => {
                            scan_font_ident();
                            n = cur_val;
                            cur_val = 0i32
                        }
                        23 | 25 | 26 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    scan_int();
                                    k = cur_val;
                                    cur_val = aat::aat_font_get_1(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                        k,
                                    )
                                }
                                #[cfg(not(target_os = "macos"))]
                                0xffffu32 => {
                                    scan_int();
                                    k = cur_val;
                                    cur_val = -1;
                                }
                                0xfffeu32 => {
                                    if usingGraphite(
                                        FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                    ) as i32
                                        != 0
                                    {
                                        scan_int();
                                        k = cur_val;
                                        cur_val = ot_font_get_1(
                                            m - 14i32,
                                            FONT_LAYOUT_ENGINE[n as usize],
                                            k,
                                        )
                                    } else {
                                        not_aat_gr_font_error(71i32, m, n);
                                        cur_val = -1i32
                                    }
                                }
                                _ => {
                                    not_aat_gr_font_error(71i32, m, n);
                                    cur_val = -1i32
                                }
                            }
                        }
                        27 | 29 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    scan_int();
                                    k = cur_val;
                                    scan_int();
                                    cur_val = aat::aat_font_get_2(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                        k,
                                        cur_val,
                                    )
                                }
                                #[cfg(not(target_os = "macos"))]
                                0xffffu32 => {
                                    scan_int();
                                    k = cur_val;
                                    scan_int();
                                    cur_val = -1;
                                }
                                0xfffeu32 => {
                                    if usingGraphite(
                                        FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                    ) as i32
                                        != 0
                                    {
                                        scan_int();
                                        k = cur_val;
                                        scan_int();
                                        cur_val = ot_font_get_2(
                                            m - 14i32,
                                            FONT_LAYOUT_ENGINE[n as usize],
                                            k,
                                            cur_val,
                                        )
                                    } else {
                                        not_aat_gr_font_error(71i32, m, n);
                                        cur_val = -1i32
                                    }
                                }
                                _ => {
                                    not_aat_gr_font_error(71i32, m, n);
                                    cur_val = -1i32
                                }
                            }
                        }
                        18 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    scan_and_pack_name();
                                    cur_val = aat::aat_font_get_named(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                    );
                                }
                                #[cfg(not(target_os = "macos"))]
                                0xffffu32 => {
                                    scan_and_pack_name();
                                    cur_val = -1;
                                }
                                _ => {
                                    not_aat_font_error(71i32, m, n);
                                    cur_val = -1i32
                                }
                            }
                        }
                        24 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    scan_and_pack_name();
                                    cur_val = aat::aat_font_get_named(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                    );
                                }
                                #[cfg(not(target_os = "macos"))]
                                0xffffu32 => {
                                    scan_and_pack_name();
                                    cur_val = -1;
                                }
                                0xfffeu32 => {
                                    if usingGraphite(
                                        FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                    ) as i32
                                        != 0
                                    {
                                        scan_and_pack_name();
                                        cur_val = gr_font_get_named(
                                            m - 14i32,
                                            FONT_LAYOUT_ENGINE[n as usize],
                                        )
                                    } else {
                                        not_aat_gr_font_error(71i32, m, n);
                                        cur_val = -1i32
                                    }
                                }
                                _ => {
                                    not_aat_gr_font_error(71i32, m, n);
                                    cur_val = -1i32
                                }
                            }
                        }
                        28 => {
                            scan_font_ident();
                            n = cur_val;
                            match FONT_AREA[n as usize] as u32 {
                                #[cfg(target_os = "macos")]
                                0xffffu32 => {
                                    scan_int();
                                    k = cur_val;
                                    scan_and_pack_name();
                                    cur_val = aat::aat_font_get_named_1(
                                        m - 14i32,
                                        (FONT_LAYOUT_ENGINE[n as usize]) as _,
                                        k,
                                    );
                                }
                                #[cfg(not(target_os = "macos"))]
                                0xffffu32 => {
                                    scan_int();
                                    k = cur_val;
                                    scan_and_pack_name();
                                    cur_val = -1;
                                }
                                0xfffeu32 => {
                                    if usingGraphite(
                                        FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                    ) as i32
                                        != 0
                                    {
                                        scan_int();
                                        k = cur_val;
                                        scan_and_pack_name();
                                        cur_val = gr_font_get_named_1(
                                            m - 14i32,
                                            FONT_LAYOUT_ENGINE[n as usize],
                                            k,
                                        )
                                    } else {
                                        not_aat_gr_font_error(71i32, m, n);
                                        cur_val = -1i32
                                    }
                                }
                                _ => {
                                    not_aat_gr_font_error(71i32, m, n);
                                    cur_val = -1i32
                                }
                            }
                        }
                        30 => {
                            scan_font_ident();
                            n = cur_val;
                            if FONT_AREA[n as usize] as u32 == 0xfffeu32
                                && usingOpenType(
                                    FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                ) as i32
                                    != 0
                            {
                                cur_val = ot_font_get(m - 14i32, FONT_LAYOUT_ENGINE[n as usize])
                            } else {
                                cur_val = 0i32
                            }
                        }
                        31 | 33 => {
                            scan_font_ident();
                            n = cur_val;
                            if FONT_AREA[n as usize] as u32 == 0xfffeu32
                                && usingOpenType(
                                    FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                ) as i32
                                    != 0
                            {
                                scan_int();
                                cur_val = ot_font_get_1(
                                    m - 14i32,
                                    FONT_LAYOUT_ENGINE[n as usize],
                                    cur_val,
                                )
                            } else {
                                not_ot_font_error(71i32, m, n);
                                cur_val = -1i32
                            }
                        }
                        32 | 34 => {
                            scan_font_ident();
                            n = cur_val;
                            if FONT_AREA[n as usize] as u32 == 0xfffeu32
                                && usingOpenType(
                                    FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                ) as i32
                                    != 0
                            {
                                scan_int();
                                k = cur_val;
                                scan_int();
                                cur_val = ot_font_get_2(
                                    m - 14i32,
                                    FONT_LAYOUT_ENGINE[n as usize],
                                    k,
                                    cur_val,
                                )
                            } else {
                                not_ot_font_error(71i32, m, n);
                                cur_val = -1i32
                            }
                        }
                        35 => {
                            scan_font_ident();
                            n = cur_val;
                            if FONT_AREA[n as usize] as u32 == 0xfffeu32
                                && usingOpenType(
                                    FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                ) as i32
                                    != 0
                            {
                                scan_int();
                                k = cur_val;
                                scan_int();
                                kk = cur_val;
                                scan_int();
                                cur_val = ot_font_get_3(
                                    m - 14i32,
                                    FONT_LAYOUT_ENGINE[n as usize],
                                    k,
                                    kk,
                                    cur_val,
                                )
                            } else {
                                not_ot_font_error(71i32, m, n);
                                cur_val = -1i32
                            }
                        }
                        36 => {
                            if FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32
                                == 0xffffu32
                                || FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32
                                    == 0xfffeu32
                            {
                                scan_int();
                                n = cur_val;
                                cur_val = map_char_to_glyph(EQTB[(CUR_FONT_LOC) as usize].b32.s1, n)
                            } else {
                                not_native_font_error(
                                    71i32,
                                    m,
                                    EQTB[(CUR_FONT_LOC) as usize].b32.s1,
                                );
                                cur_val = 0i32
                            }
                        }
                        37 => {
                            if FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32
                                == 0xffffu32
                                || FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32
                                    == 0xfffeu32
                            {
                                scan_and_pack_name();
                                cur_val = map_glyph_to_index(EQTB[(CUR_FONT_LOC) as usize].b32.s1)
                            } else {
                                not_native_font_error(
                                    71i32,
                                    m,
                                    EQTB[(CUR_FONT_LOC) as usize].b32.s1,
                                );
                                cur_val = 0i32
                            }
                        }
                        38 => {
                            scan_font_ident();
                            n = cur_val;
                            if FONT_AREA[n as usize] as u32 == 0xffffu32 {
                                cur_val = 1i32
                            } else if FONT_AREA[n as usize] as u32 == 0xfffeu32
                                && usingOpenType(
                                    FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                ) as i32
                                    != 0
                            {
                                cur_val = 2i32
                            } else if FONT_AREA[n as usize] as u32 == 0xfffeu32
                                && usingGraphite(
                                    FONT_LAYOUT_ENGINE[n as usize] as XeTeXLayoutEngine,
                                ) as i32
                                    != 0
                            {
                                cur_val = 3i32
                            } else {
                                cur_val = 0i32
                            }
                        }
                        39 | 40 => {
                            scan_font_ident();
                            n = cur_val;
                            if FONT_AREA[n as usize] as u32 == 0xffffu32
                                || FONT_AREA[n as usize] as u32 == 0xfffeu32
                            {
                                cur_val = get_font_char_range(n, (m == 39i32) as i32)
                            } else if m == 39i32 {
                                cur_val = FONT_BC[n as usize] as i32
                            } else {
                                cur_val = FONT_EC[n as usize] as i32
                            }
                        }
                        41 => cur_val = pdf_last_x_pos,
                        42 => cur_val = pdf_last_y_pos,
                        46 => {
                            scan_and_pack_name();
                            cur_val = count_pdf_file_pages()
                        }
                        7 => cur_val = cur_level as i32 - 1i32,
                        8 => cur_val = cur_group as i32,
                        9 => {
                            q = cond_ptr;
                            cur_val = 0i32;
                            while q != TEX_NULL {
                                cur_val += 1;
                                q = MEM[q as usize].b32.s1
                            }
                        }
                        10 => {
                            if cond_ptr == TEX_NULL {
                                cur_val = 0i32
                            } else if (cur_if as i32) < 32i32 {
                                cur_val = cur_if as i32 + 1i32
                            } else {
                                cur_val = -(cur_if as i32 - 31i32)
                            }
                        }
                        11 => {
                            if if_limit as i32 == 4i32 || if_limit as i32 == 3i32 {
                                cur_val = 1i32
                            } else if if_limit as i32 == 2i32 {
                                cur_val = -1i32
                            } else {
                                cur_val = 0i32
                            }
                        }
                        12 | 13 => {
                            scan_normal_glue();
                            q = cur_val;
                            if m == 12i32 {
                                cur_val = MEM[q as usize].b16.s1 as i32
                            } else {
                                cur_val = MEM[q as usize].b16.s0 as i32
                            }
                            delete_glue_ref(q);
                        }
                        _ => {}
                    }
                    cur_val_level = 0_u8
                }
            } else {
                cur_val = 0i32;
                tx = cur_list.tail;
                if tx < hi_mem_min {
                    if MEM[tx as usize].b16.s1 as i32 == 9 && MEM[tx as usize].b16.s0 as i32 == 3 {
                        r = cur_list.head;
                        loop {
                            q = r;
                            r = MEM[q as usize].b32.s1;
                            if !(r != tx) {
                                break;
                            }
                        }
                        tx = q
                    }
                }
                if cur_chr == 3i32 {
                    cur_val_level = 0_u8;
                    if tx == cur_list.head || cur_list.mode as i32 == 0i32 {
                        cur_val = -1i32
                    }
                } else {
                    cur_val_level = cur_chr as u8
                }
                if tx < hi_mem_min && cur_list.mode as i32 != 0i32 {
                    match cur_chr {
                        0 => {
                            if MEM[tx as usize].b16.s1 as i32 == 12 {
                                cur_val = MEM[(tx + 1) as usize].b32.s1
                            }
                        }
                        1 => {
                            if MEM[tx as usize].b16.s1 as i32 == 11 {
                                cur_val = MEM[(tx + 1) as usize].b32.s1
                            }
                        }
                        2 => {
                            if MEM[tx as usize].b16.s1 as i32 == 10 {
                                cur_val = MEM[(tx + 1) as usize].b32.s0;
                                if MEM[tx as usize].b16.s0 as i32 == 99 {
                                    cur_val_level = 3_u8
                                }
                            }
                        }
                        3 => {
                            if MEM[tx as usize].b16.s1 as i32 <= 13 {
                                cur_val = MEM[tx as usize].b16.s1 as i32 + 1
                            } else {
                                cur_val = 13i32 + 2i32
                            }
                        }
                        _ => {}
                    }
                } else if cur_list.mode as i32 == 1i32 && tx == cur_list.head {
                    match cur_chr {
                        0 => cur_val = last_penalty,
                        1 => cur_val = last_kern,
                        2 => {
                            if last_glue != 0x3fffffffi32 {
                                cur_val = last_glue
                            }
                        }
                        3 => cur_val = last_node_type,
                        _ => {}
                    }
                }
            }
        }
        _ => {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"You can\'t use `");
            print_cmd_chr(cur_cmd as u16, cur_chr);
            print_cstr(b"\' after ");
            print_esc_cstr(b"the");
            help_ptr = 1_u8;
            help_line[0] = b"I\'m forgetting what you said and using zero instead.";
            error();
            cur_val = 0i32;
            if level as i32 != 5i32 {
                cur_val_level = 1_u8
            } else {
                cur_val_level = 0_u8
            }
        }
    }
    while cur_val_level as i32 > level as i32 {
        /*447:*/
        if cur_val_level as i32 == 2i32 {
            cur_val = MEM[(cur_val + 1) as usize].b32.s1
        } else if cur_val_level as i32 == 3i32 {
            mu_error();
        }
        cur_val_level = cur_val_level.wrapping_sub(1)
    }
    if negative {
        if cur_val_level as i32 >= 2i32 {
            cur_val = new_spec(cur_val);
            MEM[(cur_val + 1) as usize].b32.s1 = -MEM[(cur_val + 1) as usize].b32.s1;
            MEM[(cur_val + 2) as usize].b32.s1 = -MEM[(cur_val + 2) as usize].b32.s1;
            MEM[(cur_val + 3) as usize].b32.s1 = -MEM[(cur_val + 3) as usize].b32.s1
        } else {
            cur_val = -cur_val
        }
    } else if cur_val_level as i32 >= 2i32 && cur_val_level as i32 <= 3i32 {
        MEM[cur_val as usize].b32.s1 += 1
    };
}
pub(crate) unsafe fn scan_int() {
    let mut negative: bool = false;
    let mut m: i32 = 0;
    let mut d: small_number = 0;
    let mut vacuous: bool = false;
    let mut OK_so_far: bool = false;
    radix = 0i32 as small_number;
    OK_so_far = true;
    negative = false;
    loop {
        loop
        /*424:*/
        {
            get_x_token();
            if !(cur_cmd as i32 == 10i32) {
                break;
            }
        }
        if cur_tok == 0x1800000i32 + '-' as i32 {
            negative = !negative;
            cur_tok = 0x1800000i32 + '+' as i32
        }
        if !(cur_tok == 0x1800000i32 + '+' as i32) {
            break;
        }
    }
    if cur_tok == 0x1800000i32 + '`' as i32 {
        /*460:*/
        get_token(); /*461:*/
        if cur_tok < 0x1ffffffi32 {
            cur_val = cur_chr; /*462:*/
            if cur_cmd as i32 <= 2i32 {
                if cur_cmd as i32 == 2i32 {
                    align_state += 1
                } else {
                    align_state -= 1
                }
            }
        } else if cur_tok < 0x1ffffffi32 + (1i32 + (0x10ffffi32 + 1i32)) {
            cur_val = cur_tok - (0x1ffffffi32 + 1i32)
        } else {
            cur_val = cur_tok - (0x1ffffffi32 + (1i32 + (0x10ffffi32 + 1i32)))
        } /*:463*/
        if cur_val > 0x10ffffi32 {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Improper alphabetic constant");
            help_ptr = 2_u8;
            help_line[1] = b"A one-character control sequence belongs after a ` mark.";
            help_line[0] = b"So I\'m essentially inserting \\0 here.";
            cur_val = '0' as i32;
            back_error();
        } else {
            get_x_token();
            if cur_cmd as i32 != 10i32 {
                back_input();
            }
        }
    } else if cur_cmd as i32 >= 68i32 && cur_cmd as i32 <= 91i32 {
        scan_something_internal(0i32 as small_number, false);
    } else {
        radix = 10i32 as small_number;
        m = 0xccccccci32;
        if cur_tok == 0x1800000i32 + '\'' as i32 {
            radix = 8i32 as small_number;
            m = 0x10000000i32;
            get_x_token();
        } else if cur_tok == 0x1800000i32 + '\"' as i32 {
            radix = 16i32 as small_number;
            m = 0x8000000i32;
            get_x_token();
        }
        vacuous = true;
        cur_val = 0i32;
        loop {
            if cur_tok < 0x1800000i32 + '0' as i32 + radix as i32
                && cur_tok >= 0x1800000i32 + '0' as i32
                && cur_tok <= 0x1800000i32 + '0' as i32 + 9i32
            {
                d = (cur_tok - (0x1800000i32 + '0' as i32)) as small_number
            } else {
                if !(radix as i32 == 16i32) {
                    break;
                }
                if cur_tok <= 0x1600000i32 + 'A' as i32 + 5i32
                    && cur_tok >= 0x1600000i32 + 'A' as i32
                {
                    d = (cur_tok - (0x1600000i32 + 'A' as i32) + 10i32) as small_number
                } else {
                    if !(cur_tok <= 0x1800000i32 + 'A' as i32 + 5i32
                        && cur_tok >= 0x1800000i32 + 'A' as i32)
                    {
                        break;
                    }
                    d = (cur_tok - (0x1800000i32 + 'A' as i32) + 10i32) as small_number
                }
            }
            vacuous = false;
            if cur_val >= m && (cur_val > m || d as i32 > 7i32 || radix as i32 != 10i32) {
                if OK_so_far {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Number too big");
                    help_ptr = 2_u8;
                    help_line[1] = b"I can only go up to 2147483647=\'17777777777=\"7FFFFFFF,";
                    help_line[0] = b"so I\'m using that number instead of yours.";
                    error();
                    cur_val = 0x7fffffffi32;
                    OK_so_far = false
                }
            } else {
                cur_val = cur_val * radix as i32 + d as i32
            }
            get_x_token();
        }
        if vacuous {
            /*464:*/
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Missing number, treated as zero");
            help_ptr = 3_u8;
            help_line[2] = b"A number should have been here; I inserted `0\'.";
            help_line[1] = b"(If you can\'t figure out why I needed to see a number,";
            help_line[0] = b"look up `weird error\' in the index to The TeXbook.)";
            back_error();
        } else if cur_cmd as i32 != 10i32 {
            back_input();
        }
    }
    if negative {
        cur_val = -cur_val
    };
}
unsafe extern "C" fn round_decimals(mut k: small_number) -> scaled_t {
    let mut a: i32 = 0i32;
    while k as i32 > 0i32 {
        k -= 1;
        a = (a + dig[k as usize] as i32 * 0x20000i32) / 10i32
    }
    (a + 1i32) / 2i32
}
pub(crate) unsafe fn xetex_scan_dimen(
    mut mu: bool,
    mut inf: bool,
    mut shortcut: bool,
    mut requires_units: bool,
) {
    let mut current_block: u64;
    let mut negative: bool = false;
    let mut f: i32 = 0;
    let mut num: i32 = 0;
    let mut denom: i32 = 0;
    let mut k: small_number = 0;
    let mut kk: small_number = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut v: scaled_t = 0;
    let mut save_cur_val: i32 = 0;
    f = 0i32;
    arith_error = false;
    cur_order = 0i32 as glue_ord;
    negative = false;
    if !shortcut {
        negative = false;
        loop {
            loop {
                get_x_token();
                if !(cur_cmd as i32 == 10i32) {
                    break;
                }
            }
            if cur_tok == 0x1800000i32 + '-' as i32 {
                negative = !negative;
                cur_tok = 0x1800000i32 + '+' as i32
            }
            if !(cur_tok == 0x1800000i32 + '+' as i32) {
                break;
            }
        }
        if cur_cmd as i32 >= 68i32 && cur_cmd as i32 <= 91i32 {
            /*468:*/
            if mu {
                scan_something_internal(3i32 as small_number, false);
                if cur_val_level as i32 >= 2i32 {
                    v = MEM[(cur_val + 1) as usize].b32.s1;
                    delete_glue_ref(cur_val);
                    cur_val = v
                }
                if cur_val_level as i32 == 3i32 {
                    current_block = 16246449912548656671;
                } else {
                    if cur_val_level as i32 != 0i32 {
                        mu_error();
                    }
                    current_block = 5028470053297453708;
                }
            } else {
                scan_something_internal(1i32 as small_number, false);
                if cur_val_level as i32 == 1i32 {
                    current_block = 16246449912548656671;
                } else {
                    current_block = 5028470053297453708;
                }
            }
        } else {
            back_input();
            if cur_tok == 0x1800000i32 + ',' as i32 {
                cur_tok = 0x1800000i32 + '.' as i32
            }
            if cur_tok != 0x1800000i32 + '.' as i32 {
                scan_int();
            } else {
                radix = 10i32 as small_number;
                cur_val = 0i32
            }
            if cur_tok == 0x1800000i32 + ',' as i32 {
                cur_tok = 0x1800000i32 + '.' as i32
            }
            if radix as i32 == 10i32 && cur_tok == 0x1800000i32 + '.' as i32 {
                /*471:*/
                k = 0i32 as small_number; /* if(requires_units) */
                p = TEX_NULL;
                get_token();
                loop {
                    get_x_token();
                    if cur_tok > 0x1800000i32 + '0' as i32 + 9i32
                        || cur_tok < 0x1800000i32 + '0' as i32
                    {
                        break;
                    }
                    if (k as i32) < 17i32 {
                        q = get_avail();
                        MEM[q as usize].b32.s1 = p;
                        MEM[q as usize].b32.s0 = cur_tok - (0x1800000 + '0' as i32);
                        p = q;
                        k += 1
                    }
                }
                kk = k;
                while kk as i32 >= 1i32 {
                    dig[(kk as i32 - 1i32) as usize] = MEM[p as usize].b32.s0 as u8;
                    q = p;
                    p = MEM[p as usize].b32.s1;
                    MEM[q as usize].b32.s1 = avail;
                    avail = q;
                    kk -= 1
                }
                f = round_decimals(k);
                if cur_cmd as i32 != 10i32 {
                    back_input();
                }
            }
            current_block = 5028470053297453708;
        }
    } else {
        current_block = 5028470053297453708;
    }
    match current_block {
        5028470053297453708 => {
            if cur_val < 0i32 {
                negative = !negative;
                cur_val = -cur_val
            }
            if requires_units {
                if inf {
                    /*473:*/
                    if scan_keyword(b"fil") {
                        cur_order = 1i32 as glue_ord;
                        while scan_keyword(b"l") {
                            if cur_order as i32 == 3i32 {
                                if file_line_error_style_p != 0 {
                                    print_file_line();
                                } else {
                                    print_nl_cstr(b"! ");
                                }
                                print_cstr(b"Illegal unit of measure (");
                                print_cstr(b"replaced by filll)");
                                help_ptr = 1_u8;
                                help_line[0] = b"I dddon\'t go any higher than filll.";
                                error();
                            } else {
                                cur_order = cur_order.wrapping_add(1)
                            }
                        }
                        current_block = 6063453238281986051;
                    } else {
                        current_block = 2750570471926810434;
                    }
                } else {
                    current_block = 2750570471926810434;
                }
                match current_block {
                    2750570471926810434 => {
                        save_cur_val = cur_val;
                        loop {
                            get_x_token();
                            if !(cur_cmd as i32 == 10i32) {
                                break;
                            }
                        }
                        if (cur_cmd as i32) < 68i32 || cur_cmd as i32 > 91i32 {
                            back_input();
                            if mu {
                                current_block = 17751730340908002208;
                            } else {
                                if scan_keyword(b"em") {
                                    v = FONT_INFO[(6 + PARAM_BASE
                                        [EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize])
                                        as usize]
                                        .b32
                                        .s1;
                                    current_block = 5195798230510548452;
                                } else if scan_keyword(b"ex") {
                                    v = FONT_INFO[(5 + PARAM_BASE
                                        [EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize])
                                        as usize]
                                        .b32
                                        .s1;
                                    current_block = 5195798230510548452;
                                } else {
                                    current_block = 17751730340908002208;
                                }
                                match current_block {
                                    17751730340908002208 => {}
                                    _ => {
                                        get_x_token();
                                        if cur_cmd as i32 != 10i32 {
                                            back_input();
                                        }
                                        current_block = 7531702508219610202;
                                    }
                                }
                            }
                            match current_block {
                                7531702508219610202 => {}
                                _ => {
                                    if mu {
                                        /*475:*/
                                        if scan_keyword(b"mu") {
                                            current_block = 6063453238281986051;
                                        } else {
                                            if file_line_error_style_p != 0 {
                                                print_file_line();
                                            } else {
                                                print_nl_cstr(b"! ");
                                            }
                                            print_cstr(b"Illegal unit of measure (");
                                            print_cstr(b"mu inserted)");
                                            help_ptr = 4_u8;
                                            help_line[3] =
                                                b"The unit of measurement in math glue must be mu.";
                                            help_line[2] =
                                                b"To recover gracefully from this error, it\'s best to";
                                            help_line[1] =
                                                b"delete the erroneous units; e.g., type `2\' to delete";
                                            help_line[0] =
                                                b"two letters. (See Chapter 27 of The TeXbook.)";
                                            error();
                                            current_block = 6063453238281986051;
                                        }
                                    } else {
                                        if scan_keyword(b"true") {
                                            /*476:*/
                                            prepare_mag(); /* magic ratio consant */
                                            if EQTB[(INT_BASE + 17i32) as usize].b32.s1 != 1000i32 {
                                                cur_val = xn_over_d(
                                                    cur_val,
                                                    1000i32,
                                                    EQTB[(INT_BASE + 17i32) as usize].b32.s1,
                                                ); /* magic ratio consant */
                                                f = (((1000i32 * f) as i64
                                                    + 65536 * tex_remainder as i64)
                                                    / EQTB[(INT_BASE + 17i32) as usize].b32.s1
                                                        as i64)
                                                    as i32;
                                                cur_val =
                                                    (cur_val as i64 + f as i64 / 65536) as i32;
                                                f = (f as i64 % 65536) as i32
                                            }
                                        }
                                        if scan_keyword(b"pt") {
                                            current_block = 6063453238281986051;
                                        } else {
                                            if scan_keyword(b"in") {
                                                num = 7227i32;
                                                denom = 100i32;
                                                current_block = 15908231092227701503;
                                            } else if scan_keyword(b"pc") {
                                                num = 12i32;
                                                denom = 1i32;
                                                current_block = 15908231092227701503;
                                            } else if scan_keyword(b"cm") {
                                                num = 7227i32;
                                                denom = 254i32;
                                                current_block = 15908231092227701503;
                                            /* magic ratio consant */
                                            } else if scan_keyword(b"mm") {
                                                num = 7227i32;
                                                denom = 2540i32;
                                                current_block = 15908231092227701503;
                                            /* magic ratio consant */
                                            /* magic ratio consant */
                                            } else if scan_keyword(b"bp") {
                                                num = 7227i32;
                                                denom = 7200i32;
                                                current_block = 15908231092227701503;
                                            /* magic ratio consant */
                                            /* magic ratio consant */
                                            } else if scan_keyword(b"dd") {
                                                num = 1238i32;
                                                denom = 1157i32;
                                                current_block = 15908231092227701503;
                                            /* magic ratio consant */
                                            /* magic ratio consant */
                                            } else if scan_keyword(b"cc") {
                                                num = 14856i32;
                                                denom = 1157i32;
                                                current_block = 15908231092227701503;
                                            /* magic ratio consant */
                                            /* magic ratio consant */
                                            } else if scan_keyword(b"sp") {
                                                current_block = 8982780081639585757;
                                            /*478:*/
                                            } else {
                                                if file_line_error_style_p != 0 {
                                                    print_file_line();
                                                } else {
                                                    print_nl_cstr(b"! ");
                                                }
                                                print_cstr(b"Illegal unit of measure (");
                                                print_cstr(b"pt inserted)");
                                                help_ptr = 6_u8;
                                                help_line[5] =
                                                    b"Dimensions can be in units of em, ex, in, pt, pc,";
                                                help_line[4] =
                                                    b"cm, mm, dd, cc, bp, or sp; but yours is a new one!";
                                                help_line[3] =
                                                    b"I\'ll assume that you meant to say pt, for printer\'s points.";
                                                help_line[2] =
                                                    b"To recover gracefully from this error, it\'s best to";
                                                help_line[1] =
                                                    b"delete the erroneous units; e.g., type `2\' to delete";
                                                help_line[0] =
                                                    b"two letters. (See Chapter 27 of The TeXbook.)";
                                                error();
                                                current_block = 6063453238281986051;
                                            }
                                            match current_block {
                                                6063453238281986051 => {}
                                                8982780081639585757 => {}
                                                _ => {
                                                    cur_val = xn_over_d(cur_val, num, denom);
                                                    f = (((num * f) as i64
                                                        + 65536 * tex_remainder as i64)
                                                        / denom as i64)
                                                        as i32;
                                                    cur_val =
                                                        (cur_val as i64 + f as i64 / 65536) as i32;
                                                    f = (f as i64 % 65536) as i32;
                                                    current_block = 6063453238281986051;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            if mu {
                                scan_something_internal(3i32 as small_number, false);
                                if cur_val_level as i32 >= 2i32 {
                                    v = MEM[(cur_val + 1) as usize].b32.s1;
                                    delete_glue_ref(cur_val);
                                    cur_val = v
                                }
                                if cur_val_level as i32 != 3i32 {
                                    mu_error();
                                }
                            } else {
                                scan_something_internal(1i32 as small_number, false);
                            }
                            v = cur_val;
                            current_block = 7531702508219610202;
                        }
                        match current_block {
                            6063453238281986051 => {}
                            8982780081639585757 => {}
                            _ => {
                                cur_val = mult_and_add(
                                    save_cur_val,
                                    v,
                                    xn_over_d(v, f, 65536 as i32),
                                    0x3fffffffi32,
                                );
                                current_block = 16246449912548656671;
                            }
                        }
                    }
                    _ => {}
                }
                match current_block {
                    16246449912548656671 => {}
                    _ => {
                        match current_block {
                            6063453238281986051 => {
                                if cur_val >= 16384i32 {
                                    arith_error = true
                                } else {
                                    cur_val = (cur_val as i64 * 65536 + f as i64) as i32
                                }
                            }
                            _ => {}
                        }
                        get_x_token();
                        if cur_cmd as i32 != 10i32 {
                            back_input();
                        }
                    }
                }
            } else if cur_val >= 16384i32 {
                arith_error = true
            } else {
                cur_val = (cur_val as i64 * 65536 + f as i64) as i32
            }
        }
        _ => {}
    }
    if arith_error as i32 != 0 || cur_val.abs() >= 0x40000000i32 {
        /*479:*/
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Dimension too large");
        help_ptr = 2_u8;
        help_line[1] = b"I can\'t work with sizes bigger than about 19 feet.";
        help_line[0] = b"Continue and I\'ll use the largest value I can.";
        error();
        cur_val = 0x3fffffffi32;
        arith_error = false
    }
    if negative {
        cur_val = -cur_val
    };
}
pub(crate) unsafe fn scan_dimen(mut mu: bool, mut inf: bool, mut shortcut: bool) {
    xetex_scan_dimen(mu, inf, shortcut, true);
}
pub(crate) unsafe fn scan_decimal() {
    xetex_scan_dimen(false, false, false, false);
}
pub(crate) unsafe fn scan_glue(mut level: small_number) {
    let mut negative: bool = false;
    let mut q: i32 = 0;
    let mut mu: bool = false;
    mu = level as i32 == 3i32;
    negative = false;
    loop {
        loop {
            get_x_token();
            if !(cur_cmd as i32 == 10i32) {
                break;
            }
        }
        if cur_tok == 0x1800000i32 + 45i32 {
            /*"-"*/
            negative = !negative;
            cur_tok = 0x1800000i32 + 43i32
            /*"+"*/
        }
        if !(cur_tok == 0x1800000i32 + 43i32) {
            break;
        }
        /*"+"*/
    }
    if cur_cmd as i32 >= 68i32 && cur_cmd as i32 <= 91i32 {
        scan_something_internal(level, negative);
        if cur_val_level as i32 >= 2i32 {
            if cur_val_level as i32 != level as i32 {
                mu_error();
            }
            return;
        }
        if cur_val_level as i32 == 0i32 {
            scan_dimen(mu, false, true);
        } else if level as i32 == 3i32 {
            mu_error();
        }
    } else {
        back_input();
        scan_dimen(mu, false, false);
        if negative {
            cur_val = -cur_val
        }
    }
    q = new_spec(0i32);
    MEM[(q + 1) as usize].b32.s1 = cur_val;
    if scan_keyword(b"plus") {
        scan_dimen(mu, true, false);
        MEM[(q + 2) as usize].b32.s1 = cur_val;
        MEM[q as usize].b16.s1 = cur_order as u16
    }
    if scan_keyword(b"minus") {
        scan_dimen(mu, true, false);
        MEM[(q + 3) as usize].b32.s1 = cur_val;
        MEM[q as usize].b16.s0 = cur_order as u16
    }
    cur_val = q;
    /*:481*/
}
pub(crate) unsafe fn add_or_sub(
    mut x: i32,
    mut y: i32,
    mut max_answer: i32,
    mut negative: bool,
) -> i32 {
    let mut a: i32 = 0;
    if negative {
        y = -y
    }
    if x >= 0i32 {
        if y <= max_answer - x {
            a = x + y
        } else {
            arith_error = true;
            a = 0i32
        }
    } else if y >= -max_answer - x {
        a = x + y
    } else {
        arith_error = true;
        a = 0i32
    }
    a
}
pub(crate) unsafe fn quotient(mut n: i32, mut d: i32) -> i32 {
    let mut negative: bool = false;
    let mut a: i32 = 0;
    if d == 0i32 {
        arith_error = true;
        a = 0i32
    } else {
        if d > 0i32 {
            negative = false
        } else {
            d = -d;
            negative = true
        }
        if n < 0i32 {
            n = -n;
            negative = !negative
        }
        a = n / d;
        n = n - a * d;
        d = n - d;
        if d + n >= 0i32 {
            a += 1
        }
        if negative {
            a = -a
        }
    }
    a
}
pub(crate) unsafe fn fract(mut x: i32, mut n: i32, mut d: i32, mut max_answer: i32) -> i32 {
    let mut current_block: u64;
    let mut negative: bool = false;
    let mut a: i32 = 0;
    let mut f: i32 = 0;
    let mut h: i32 = 0;
    let mut r: i32 = 0;
    let mut t: i32 = 0;
    if d == 0i32 {
        current_block = 17166748944382662577;
    } else {
        a = 0i32;
        if d > 0i32 {
            negative = false
        } else {
            d = -d;
            negative = true
        }
        if x < 0i32 {
            x = -x;
            negative = !negative;
            current_block = 12349973810996921269;
        } else if x == 0i32 {
            current_block = 8704816881991807296;
        } else {
            current_block = 12349973810996921269;
        }
        match current_block {
            8704816881991807296 => {}
            _ => {
                if n < 0i32 {
                    n = -n;
                    negative = !negative
                }
                t = n / d;
                if t > max_answer / x {
                    current_block = 17166748944382662577;
                } else {
                    a = t * x;
                    n = n - t * d;
                    if n == 0i32 {
                        current_block = 8791566675823797574;
                    } else {
                        t = x / d;
                        if t > (max_answer - a) / n {
                            current_block = 17166748944382662577;
                        } else {
                            a = a + t * n;
                            x = x - t * d;
                            if x == 0i32 {
                                current_block = 8791566675823797574;
                            } else {
                                if x < n {
                                    t = x;
                                    x = n;
                                    n = t
                                }
                                f = 0i32;
                                r = d / 2i32 - d;
                                h = -r;
                                loop {
                                    if n & 1i32 != 0 {
                                        r = r + x;
                                        if r >= 0i32 {
                                            r = r - d;
                                            f += 1
                                        }
                                    }
                                    n = n / 2i32;
                                    if n == 0i32 {
                                        break;
                                    }
                                    if x < h {
                                        x = x + x
                                    } else {
                                        t = x - d;
                                        x = t + x;
                                        f = f + n;
                                        if !(x < n) {
                                            continue;
                                        }
                                        if x == 0i32 {
                                            break;
                                        }
                                        t = x;
                                        x = n;
                                        n = t
                                    }
                                }
                                if f > max_answer - a {
                                    current_block = 17166748944382662577;
                                } else {
                                    a = a + f;
                                    current_block = 8791566675823797574;
                                }
                            }
                        }
                    }
                    match current_block {
                        17166748944382662577 => {}
                        _ => {
                            if negative {
                                a = -a
                            }
                            current_block = 8704816881991807296;
                        }
                    }
                }
            }
        }
    }
    match current_block {
        17166748944382662577 => {
            arith_error = true;
            a = 0i32
        }
        _ => {}
    }
    a
}
pub(crate) unsafe fn scan_expr() {
    let mut a: bool = false;
    let mut b: bool = false;
    let mut l: small_number = 0;
    let mut r: small_number = 0;
    let mut s: small_number = 0;
    let mut o: small_number = 0;
    let mut e: i32 = 0;
    let mut t: i32 = 0;
    let mut f: i32 = 0;
    let mut n: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    l = cur_val_level as small_number;
    a = arith_error;
    b = false;
    p = TEX_NULL;
    'c_78022: loop {
        r = 0i32 as small_number;
        e = 0i32;
        s = 0i32 as small_number;
        t = 0i32;
        n = 0i32;
        loop {
            if s as i32 == 0i32 {
                o = l
            } else {
                o = 0i32 as small_number
            }
            loop {
                get_x_token();
                if !(cur_cmd as i32 == 10i32) {
                    break;
                }
            }
            if cur_tok == 0x1800000i32 + 40i32 {
                break;
            }
            back_input();
            if o as i32 == 0i32 {
                scan_int();
            } else if o as i32 == 1i32 {
                scan_dimen(false, false, false);
            } else if o as i32 == 2i32 {
                scan_normal_glue();
            } else {
                scan_mu_glue();
            }
            f = cur_val;
            loop {
                loop
                /*1572:*//*424:*/
                {
                    get_x_token();
                    if !(cur_cmd as i32 == 10i32) {
                        break;
                    }
                }
                if cur_tok == 0x1800000i32 + 43i32 {
                    o = 1i32 as small_number
                } else if cur_tok == 0x1800000i32 + 45i32 {
                    o = 2i32 as small_number
                } else if cur_tok == 0x1800000i32 + 42i32 {
                    o = 3i32 as small_number
                } else if cur_tok == 0x1800000i32 + 47i32 {
                    o = 4i32 as small_number
                } else {
                    o = 0i32 as small_number;
                    if p == TEX_NULL {
                        if cur_cmd as i32 != 0i32 {
                            back_input();
                        }
                    } else if cur_tok != 0x1800000i32 + 41i32 {
                        if file_line_error_style_p != 0 {
                            print_file_line();
                        } else {
                            print_nl_cstr(b"! ");
                        }
                        print_cstr(b"Missing ) inserted for expression");
                        help_ptr = 1_u8;
                        help_line[0] =
                            b"I was expecting to see `+\', `-\', `*\', `/\', or `)\'. Didn\'t.";
                        back_error();
                    }
                }
                arith_error = b;
                if l as i32 == 0i32 || s as i32 > 2i32 {
                    if f > 0x7fffffffi32 || f < -0x7fffffffi32 {
                        arith_error = true;
                        f = 0i32
                    }
                } else if l as i32 == 1i32 {
                    if f.abs() > 0x3fffffffi32 {
                        arith_error = true;
                        f = 0i32
                    }
                } else if (MEM[(f + 1) as usize].b32.s1).abs() > 0x3fffffff
                    || (MEM[(f + 2) as usize].b32.s1).abs() > 0x3fffffff
                    || (MEM[(f + 3) as usize].b32.s1).abs() > 0x3fffffff
                {
                    arith_error = true;
                    delete_glue_ref(f);
                    f = new_spec(0i32)
                }
                match s as i32 {
                    0 => {
                        /*1579: */
                        if l as i32 >= 2i32 && o as i32 != 0i32 {
                            t = new_spec(f);
                            delete_glue_ref(f);
                            if MEM[(t + 2) as usize].b32.s1 == 0 {
                                MEM[t as usize].b16.s1 = 0_u16
                            }
                            if MEM[(t + 3) as usize].b32.s1 == 0 {
                                MEM[t as usize].b16.s0 = 0_u16
                            }
                        } else {
                            t = f
                        }
                    }
                    3 => {
                        if o as i32 == 4i32 {
                            n = f;
                            o = 5i32 as small_number
                        } else if l as i32 == 0i32 {
                            t = mult_and_add(t, f, 0, 0x7fffffff)
                        } else if l as i32 == 1i32 {
                            t = mult_and_add(t, f, 0, 0x3fffffff)
                        } else {
                            MEM[(t + 1) as usize].b32.s1 =
                                mult_and_add(MEM[(t + 1) as usize].b32.s1, f, 0, 0x3fffffff);
                            MEM[(t + 2) as usize].b32.s1 =
                                mult_and_add(MEM[(t + 2) as usize].b32.s1, f, 0, 0x3fffffff);
                            MEM[(t + 3) as usize].b32.s1 =
                                mult_and_add(MEM[(t + 3) as usize].b32.s1, f, 0, 0x3fffffff)
                        }
                    }
                    4 => {
                        if (l as i32) < 2i32 {
                            t = quotient(t, f)
                        } else {
                            MEM[(t + 1) as usize].b32.s1 =
                                quotient(MEM[(t + 1) as usize].b32.s1, f);
                            MEM[(t + 2) as usize].b32.s1 =
                                quotient(MEM[(t + 2) as usize].b32.s1, f);
                            MEM[(t + 3) as usize].b32.s1 = quotient(MEM[(t + 3) as usize].b32.s1, f)
                        }
                    }
                    5 => {
                        if l as i32 == 0i32 {
                            t = fract(t, n, f, 0x7fffffffi32)
                        } else if l as i32 == 1i32 {
                            t = fract(t, n, f, 0x3fffffffi32)
                        } else {
                            MEM[(t + 1) as usize].b32.s1 =
                                fract(MEM[(t + 1) as usize].b32.s1, n, f, 0x3fffffff);
                            MEM[(t + 2) as usize].b32.s1 =
                                fract(MEM[(t + 2) as usize].b32.s1, n, f, 0x3fffffff);
                            MEM[(t + 3) as usize].b32.s1 =
                                fract(MEM[(t + 3) as usize].b32.s1, n, f, 0x3fffffff)
                        }
                    }
                    _ => {}
                }
                if o as i32 > 2i32 {
                    s = o
                } else {
                    /*1580: */
                    s = 0i32 as small_number;
                    if r as i32 == 0i32 {
                        e = t
                    } else if l as i32 == 0i32 {
                        e = add_or_sub(e, t, 0x7fffffffi32, r as i32 == 2i32)
                    } else if l as i32 == 1i32 {
                        e = add_or_sub(e, t, 0x3fffffffi32, r as i32 == 2i32)
                    } else {
                        /*1582: */
                        MEM[(e + 1) as usize].b32.s1 = add_or_sub(
                            MEM[(e + 1) as usize].b32.s1,
                            MEM[(t + 1) as usize].b32.s1,
                            0x3fffffffi32,
                            r as i32 == 2i32,
                        );
                        if MEM[e as usize].b16.s1 as i32 == MEM[t as usize].b16.s1 as i32 {
                            MEM[(e + 2) as usize].b32.s1 = add_or_sub(
                                MEM[(e + 2) as usize].b32.s1,
                                MEM[(t + 2) as usize].b32.s1,
                                0x3fffffffi32,
                                r as i32 == 2i32,
                            )
                        } else if (MEM[e as usize].b16.s1 as i32) < MEM[t as usize].b16.s1 as i32
                            && MEM[(t + 2) as usize].b32.s1 != 0
                        {
                            MEM[(e + 2) as usize].b32.s1 = MEM[(t + 2) as usize].b32.s1;
                            MEM[e as usize].b16.s1 = MEM[t as usize].b16.s1
                        }
                        if MEM[e as usize].b16.s0 as i32 == MEM[t as usize].b16.s0 as i32 {
                            MEM[(e + 3) as usize].b32.s1 = add_or_sub(
                                MEM[(e + 3) as usize].b32.s1,
                                MEM[(t + 3) as usize].b32.s1,
                                0x3fffffffi32,
                                r as i32 == 2i32,
                            )
                        } else if (MEM[e as usize].b16.s0 as i32) < MEM[t as usize].b16.s0 as i32
                            && MEM[(t + 3) as usize].b32.s1 != 0
                        {
                            MEM[(e + 3) as usize].b32.s1 = MEM[(t + 3) as usize].b32.s1;
                            MEM[e as usize].b16.s0 = MEM[t as usize].b16.s0
                        }
                        delete_glue_ref(t);
                        if MEM[(e + 2) as usize].b32.s1 == 0 {
                            MEM[e as usize].b16.s1 = 0_u16
                        }
                        if MEM[(e + 3) as usize].b32.s1 == 0 {
                            MEM[e as usize].b16.s0 = 0_u16
                        }
                    }
                    r = o
                }
                b = arith_error;
                if o as i32 != 0i32 {
                    break;
                }
                if !(p != TEX_NULL) {
                    break 'c_78022;
                }
                /*1577: */
                f = e;
                q = p;
                e = MEM[(q + 1) as usize].b32.s1;
                t = MEM[(q + 2) as usize].b32.s1;
                n = MEM[(q + 3) as usize].b32.s1;
                s = (MEM[q as usize].b16.s0 as i32 / 4) as small_number;
                r = (MEM[q as usize].b16.s0 as i32 % 4) as small_number;
                l = MEM[q as usize].b16.s1 as small_number;
                p = MEM[q as usize].b32.s1;
                free_node(q, 4i32);
            }
        }
        /*1576: */
        q = get_node(4i32);
        MEM[q as usize].b32.s1 = p;
        MEM[q as usize].b16.s1 = l as u16;
        MEM[q as usize].b16.s0 = (4 * s as i32 + r as i32) as u16;
        MEM[(q + 1) as usize].b32.s1 = e;
        MEM[(q + 2) as usize].b32.s1 = t;
        MEM[(q + 3) as usize].b32.s1 = n;
        p = q;
        l = o
    }
    if b {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Arithmetic overflow");
        help_ptr = 2_u8;
        help_line[1] = b"I can\'t evaluate this expression,";
        help_line[0] = b"since the result is out of range.";
        error();
        if l as i32 >= 2i32 {
            delete_glue_ref(e);
            e = 0i32;
            MEM[e as usize].b32.s1 += 1
        } else {
            e = 0i32
        }
    }
    arith_error = a;
    cur_val = e;
    cur_val_level = l as u8;
}
pub(crate) unsafe fn scan_normal_glue() {
    scan_glue(2i32 as small_number);
}
pub(crate) unsafe fn scan_mu_glue() {
    scan_glue(3i32 as small_number);
}
pub(crate) unsafe fn scan_rule_spec() -> i32 {
    let mut q: i32 = 0;
    q = new_rule();
    if cur_cmd as i32 == 35i32 {
        MEM[(q + 1) as usize].b32.s1 = 26214
    } else {
        MEM[(q + 3) as usize].b32.s1 = 26214;
        MEM[(q + 2) as usize].b32.s1 = 0
    }
    loop {
        if scan_keyword(b"width") {
            scan_dimen(false, false, false);
            MEM[(q + 1) as usize].b32.s1 = cur_val
        } else if scan_keyword(b"height") {
            scan_dimen(false, false, false);
            MEM[(q + 3) as usize].b32.s1 = cur_val
        } else {
            if !scan_keyword(b"depth") {
                break;
            }
            scan_dimen(false, false, false);
            MEM[(q + 2) as usize].b32.s1 = cur_val
        }
    }
    q
}
pub(crate) unsafe fn scan_general_text() {
    let mut s: u8 = 0;
    let mut w: i32 = 0;
    let mut d: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut unbalance: i32 = 0;
    s = scanner_status;
    w = warning_index;
    d = def_ref;
    scanner_status = 5_u8;
    warning_index = cur_cs;
    def_ref = get_avail();
    MEM[def_ref as usize].b32.s0 = TEX_NULL;
    p = def_ref;
    scan_left_brace();
    unbalance = 1i32;
    loop {
        get_token();
        if cur_tok < 0x600000i32 {
            if (cur_cmd as i32) < 2i32 {
                unbalance += 1
            } else {
                unbalance -= 1;
                if unbalance == 0i32 {
                    break;
                }
            }
        }
        q = get_avail();
        MEM[p as usize].b32.s1 = q;
        MEM[q as usize].b32.s0 = cur_tok;
        p = q
    }
    q = MEM[def_ref as usize].b32.s1;
    MEM[def_ref as usize].b32.s1 = avail;
    avail = def_ref;
    if q == TEX_NULL {
        cur_val = 4999999i32 - 3i32
    } else {
        cur_val = p
    }
    MEM[(4999999 - 3) as usize].b32.s1 = q;
    scanner_status = s;
    warning_index = w;
    def_ref = d;
}
pub(crate) unsafe fn pseudo_start() {
    let mut s: str_number = 0;
    let mut l: pool_pointer = 0;
    let mut m: pool_pointer = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut w: b16x4 = b16x4 {
        s0: 0,
        s1: 0,
        s2: 0,
        s3: 0,
    };
    let mut nl: i32 = 0;
    let mut sz: i32 = 0;
    scan_general_text();
    let old_setting_0 = selector;
    selector = Selector::NEW_STRING;
    token_show(4999999i32 - 3i32);
    selector = old_setting_0;
    flush_list(MEM[(4999999 - 3) as usize].b32.s1);
    if pool_ptr + 1i32 > pool_size {
        overflow(b"pool size", pool_size - init_pool_ptr);
    }
    s = make_string();
    *str_pool.offset(pool_ptr as isize) = ' ' as i32 as packed_UTF16_code;
    l = *str_start.offset((s as i64 - 65536) as isize);
    nl = EQTB[(INT_BASE + 49i32) as usize].b32.s1;
    p = get_avail();
    q = p;
    while l < pool_ptr {
        m = l;
        while l < pool_ptr && *str_pool.offset(l as isize) as i32 != nl {
            l += 1
        }
        sz = (l - m + 7i32) / 4i32;
        if sz == 1i32 {
            sz = 2i32
        }
        r = get_node(sz);
        MEM[q as usize].b32.s1 = r;
        q = r;
        MEM[q as usize].b32.s0 = sz;
        while sz > 2i32 {
            sz -= 1;
            r += 1;
            w.s3 = *str_pool.offset(m as isize);
            w.s2 = *str_pool.offset((m + 1i32) as isize);
            w.s1 = *str_pool.offset((m + 2i32) as isize);
            w.s0 = *str_pool.offset((m + 3i32) as isize);
            MEM[r as usize].b16 = w;
            m = m + 4i32
        }
        w.s3 = ' ' as i32 as u16;
        w.s2 = ' ' as i32 as u16;
        w.s1 = ' ' as i32 as u16;
        w.s0 = ' ' as i32 as u16;
        if l > m {
            w.s3 = *str_pool.offset(m as isize);
            if l > m + 1i32 {
                w.s2 = *str_pool.offset((m + 1i32) as isize);
                if l > m + 2i32 {
                    w.s1 = *str_pool.offset((m + 2i32) as isize);
                    if l > m + 3i32 {
                        w.s0 = *str_pool.offset((m + 3i32) as isize)
                    }
                }
            }
        }
        MEM[(r + 1) as usize].b16 = w;
        if *str_pool.offset(l as isize) as i32 == nl {
            l += 1
        }
    }
    MEM[p as usize].b32.s0 = MEM[p as usize].b32.s1;
    MEM[p as usize].b32.s1 = pseudo_files;
    pseudo_files = p;
    str_ptr -= 1;
    pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize);
    begin_file_reading();
    line = 0i32;
    cur_input.limit = cur_input.start;
    cur_input.loc = cur_input.limit + 1i32;
    if EQTB[(INT_BASE + 61i32) as usize].b32.s1 > 0i32 {
        if term_offset > max_print_line - 3i32 {
            print_ln();
        } else if term_offset > 0i32 || file_offset > 0i32 {
            print_char(' ' as i32);
        }
        cur_input.name = 19i32;
        print_cstr(b"( ");
        open_parens += 1;
        rust_stdout.as_mut().unwrap().flush().unwrap();
    } else {
        cur_input.name = 18i32;
        cur_input.synctex_tag = 0i32
    };
}
pub(crate) unsafe fn str_toks_cat(mut b: pool_pointer, mut cat: small_number) -> i32 {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut t: i32 = 0;
    let mut k: pool_pointer = 0;
    if pool_ptr + 1i32 > pool_size {
        overflow(b"pool size", pool_size - init_pool_ptr);
    }
    p = 4999999i32 - 3i32;
    MEM[p as usize].b32.s1 = TEX_NULL;
    k = b;
    while k < pool_ptr {
        t = *str_pool.offset(k as isize) as i32;
        if t == ' ' as i32 && cat as i32 == 0i32 {
            t = 0x1400020i32
        } else {
            if t >= 0xd800i32
                && t < 0xdc00i32
                && k + 1i32 < pool_ptr
                && *str_pool.offset((k + 1i32) as isize) as i32 >= 0xdc00i32
                && (*str_pool.offset((k + 1i32) as isize) as i32) < 0xe000i32
            {
                k += 1;
                t = (65536
                    + ((t - 0xd800i32) * 1024i32) as i64
                    + (*str_pool.offset(k as isize) as i32 - 0xdc00i32) as i64)
                    as i32
            }
            if cat as i32 == 0i32 {
                t = 0x1800000i32 + t
            } else {
                t = 0x200000i32 * cat as i32 + t
            }
        }
        q = avail;
        if q == TEX_NULL {
            q = get_avail()
        } else {
            avail = MEM[q as usize].b32.s1;
            MEM[q as usize].b32.s1 = TEX_NULL
        }
        MEM[p as usize].b32.s1 = q;
        MEM[q as usize].b32.s0 = t;
        p = q;
        k += 1
    }
    pool_ptr = b;
    p
}
pub(crate) unsafe fn str_toks(mut b: pool_pointer) -> i32 {
    str_toks_cat(b, 0i32 as small_number)
}
pub(crate) unsafe fn the_toks() -> i32 {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut b: pool_pointer = 0;
    let mut c: small_number = 0;
    if cur_chr & 1i32 != 0 {
        c = cur_chr as small_number;
        scan_general_text();
        if c as i32 == 1i32 {
            return cur_val;
        } else {
            let old_setting_0 = selector;
            selector = Selector::NEW_STRING;
            b = pool_ptr;
            p = get_avail();
            MEM[p as usize].b32.s1 = MEM[(4999999 - 3) as usize].b32.s1;
            token_show(p);
            flush_list(p);
            selector = old_setting_0;
            return str_toks(b);
        }
    }
    get_x_token();
    scan_something_internal(5i32 as small_number, false);
    if cur_val_level as i32 >= 4i32 {
        /*485: */
        p = 4999999i32 - 3i32;
        MEM[p as usize].b32.s1 = TEX_NULL;
        if cur_val_level as i32 == 4i32 {
            q = get_avail();
            MEM[p as usize].b32.s1 = q;
            MEM[q as usize].b32.s0 = 0x1ffffff + cur_val;
            p = q
        } else if cur_val != TEX_NULL {
            r = MEM[cur_val as usize].b32.s1;
            while r != TEX_NULL {
                q = avail;
                if q == TEX_NULL {
                    q = get_avail()
                } else {
                    avail = MEM[q as usize].b32.s1;
                    MEM[q as usize].b32.s1 = TEX_NULL
                }
                MEM[p as usize].b32.s1 = q;
                MEM[q as usize].b32.s0 = MEM[r as usize].b32.s0;
                p = q;
                r = MEM[r as usize].b32.s1
            }
        }
        return p;
    } else {
        let old_setting_0 = selector;
        selector = Selector::NEW_STRING;
        b = pool_ptr;
        match cur_val_level as i32 {
            0 => print_int(cur_val),
            1 => {
                print_scaled(cur_val);
                print_cstr(b"pt");
            }
            2 => {
                print_spec(cur_val, b"pt\x00" as *const u8 as *const i8);
                delete_glue_ref(cur_val);
            }
            3 => {
                print_spec(cur_val, b"mu\x00" as *const u8 as *const i8);
                delete_glue_ref(cur_val);
            }
            _ => {}
        }
        selector = old_setting_0;
        return str_toks(b);
    };
}
pub(crate) unsafe fn ins_the_toks() {
    MEM[(4999999 - 12) as usize].b32.s1 = the_toks();
    begin_token_list(MEM[(4999999 - 3) as usize].b32.s1, 5_u16);
}
pub(crate) unsafe fn conv_toks() {
    let mut save_warning_index: i32 = 0;
    let mut save_def_ref: i32 = 0;
    let mut boolvar: bool = false;
    let mut s: str_number = 0;
    let mut u: str_number = 0;
    let mut c: small_number = 0;
    let mut save_scanner_status: small_number = 0;
    let mut b: pool_pointer = 0;
    let mut fnt: i32 = 0i32;
    let mut arg1: i32 = 0i32;
    let mut arg2: i32 = 0i32;
    let mut font_name_str: str_number = 0;
    let mut i: small_number = 0;
    let mut quote_char: UTF16_code = 0;
    let mut cat: small_number = 0;
    let mut saved_chr: UnicodeScalar = 0;
    let mut p: i32 = TEX_NULL;
    let mut q: i32 = 0;
    cat = 0i32 as small_number;
    c = cur_chr as small_number;
    match c as i32 {
        0 | 1 => scan_int(),
        2 | 3 => {
            save_scanner_status = scanner_status as small_number;
            scanner_status = 0_u8;
            get_token();
            scanner_status = save_scanner_status as u8
        }
        4 => scan_font_ident(),
        13 => scan_usv_num(),
        14 => {
            scan_usv_num();
            saved_chr = cur_val;
            scan_int();
            if cur_val < 1i32 || cur_val > 12i32 || cur_val == 5i32 || cur_val == 9i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Invalid code (");
                print_int(cur_val);
                print_cstr(b"), should be in the ranges 1..4, 6..8, 10..12");
                help_ptr = 1_u8;
                help_line[0] = b"I\'m going to use 12 instead of that illegal code value.";
                error();
                cat = 12i32 as small_number
            } else {
                cat = cur_val as small_number
            }
            cur_val = saved_chr
        }
        43 => {
            save_scanner_status = scanner_status as small_number;
            save_warning_index = warning_index;
            save_def_ref = def_ref;
            if *str_start.offset((str_ptr - 65536i32) as isize) < pool_ptr {
                u = make_string()
            } else {
                u = 0i32
            }
            compare_strings();
            def_ref = save_def_ref;
            warning_index = save_warning_index;
            scanner_status = save_scanner_status as u8;
            if u != 0i32 {
                str_ptr -= 1
            }
        }
        44 => {
            save_scanner_status = scanner_status as small_number;
            save_warning_index = warning_index;
            save_def_ref = def_ref;
            if *str_start.offset((str_ptr - 65536i32) as isize) < pool_ptr {
                u = make_string()
            } else {
                u = 0i32
            }
            boolvar = scan_keyword(b"file");
            scan_pdf_ext_toks();
            if selector == Selector::NEW_STRING {
                pdf_error(
                    b"tokens",
                    b"tokens_to_string() called while selector = new_string",
                );
            }
            let old_setting_0 = selector;
            selector = Selector::NEW_STRING;
            show_token_list(MEM[def_ref as usize].b32.s1, TEX_NULL, pool_size - pool_ptr);
            selector = old_setting_0;
            s = make_string();
            delete_token_ref(def_ref);
            def_ref = save_def_ref;
            warning_index = save_warning_index;
            scanner_status = save_scanner_status as u8;
            b = pool_ptr;
            getmd5sum(s, boolvar);
            MEM[(4999999 - 12) as usize].b32.s1 = str_toks(b);
            if s == str_ptr - 1i32 {
                str_ptr -= 1;
                pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize)
            }
            begin_token_list(MEM[(4999999 - 3) as usize].b32.s1, 5_u16);
            if u != 0i32 {
                str_ptr -= 1
            }
            return;
        }
        7 => {
            scan_font_ident();
            fnt = cur_val;
            if FONT_AREA[fnt as usize] as u32 == 0xffffu32 {
                scan_int();
                arg1 = cur_val;
                arg2 = 0i32
            } else {
                not_aat_font_error(110i32, c as i32, fnt);
            }
        }
        8 => {
            scan_font_ident();
            fnt = cur_val;
            if FONT_AREA[fnt as usize] as u32 == 0xffffu32
                || FONT_AREA[fnt as usize] as u32 == 0xfffeu32
                    && usingGraphite(FONT_LAYOUT_ENGINE[fnt as usize] as XeTeXLayoutEngine) as i32
                        != 0
            {
                scan_int();
                arg1 = cur_val;
                arg2 = 0i32
            } else {
                not_aat_gr_font_error(110i32, c as i32, fnt);
            }
        }
        9 => {
            scan_font_ident();
            fnt = cur_val;
            if FONT_AREA[fnt as usize] as u32 == 0xffffu32
                || FONT_AREA[fnt as usize] as u32 == 0xfffeu32
                    && usingGraphite(FONT_LAYOUT_ENGINE[fnt as usize] as XeTeXLayoutEngine) as i32
                        != 0
            {
                scan_int();
                arg1 = cur_val;
                scan_int();
                arg2 = cur_val
            } else {
                not_aat_gr_font_error(110i32, c as i32, fnt);
            }
        }
        10 => {
            scan_font_ident();
            fnt = cur_val;
            if FONT_AREA[fnt as usize] as u32 == 0xffffu32
                || FONT_AREA[fnt as usize] as u32 == 0xfffeu32
            {
                scan_int();
                arg1 = cur_val
            } else {
                not_native_font_error(110i32, c as i32, fnt);
            }
        }
        11 | 12 => {
            scan_register_num();
            if cur_val < 256i32 {
                p = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr == TEX_NULL {
                    p = TEX_NULL
                } else {
                    p = MEM[(cur_ptr + 1) as usize].b32.s1
                }
            }
            if p == TEX_NULL || MEM[p as usize].b16.s1 as i32 != 0 {
                pdf_error(b"marginkern", b"a non-empty hbox expected");
            }
        }
        15 => {
            if job_name == 0i32 {
                open_log_file();
            }
        }
        5 | 6 | _ => {}
    }
    let old_setting_0 = selector;
    selector = Selector::NEW_STRING;
    b = pool_ptr;
    match c as i32 {
        0 => print_int(cur_val),
        1 => print_roman_int(cur_val),
        2 => {
            if cur_cs != 0i32 {
                sprint_cs(cur_cs);
            } else {
                print_char(cur_chr);
            }
        }
        3 => print_meaning(),
        4 => {
            font_name_str = FONT_NAME[cur_val as usize];
            match FONT_AREA[cur_val as usize] as u32 {
                0xffffu32 | 0xfffeu32 => {
                    quote_char = '\"' as i32 as UTF16_code;
                    i = 0i32 as small_number;
                    while i as i32 <= length(font_name_str) - 1i32 {
                        if *str_pool.offset(
                            (*str_start.offset((font_name_str as i64 - 65536) as isize) + i as i32)
                                as isize,
                        ) as i32
                            == '\"' as i32
                        {
                            quote_char = '\'' as i32 as UTF16_code
                        }
                        i += 1
                    }
                    print_char(quote_char as i32);
                    print(font_name_str);
                    print_char(quote_char as i32);
                }
                _ => print(font_name_str),
            }
            if FONT_SIZE[cur_val as usize] != FONT_DSIZE[cur_val as usize] {
                print_cstr(b" at ");
                print_scaled(FONT_SIZE[cur_val as usize]);
                print_cstr(b"pt");
            }
        }
        13 | 14 => print_char(cur_val),
        5 => print_cstr(b".6"),
        43 => print_int(cur_val),
        6 => print_cstr(b".99998"),
        7 => {
            match FONT_AREA[fnt as usize] as u32 {
                #[cfg(target_os = "macos")]
                0xffffu32 => {
                    aat::aat_print_font_name(
                        c as i32,
                        (FONT_LAYOUT_ENGINE[fnt as usize]) as _,
                        arg1,
                        arg2,
                    );
                }
                #[cfg(not(target_os = "macos"))]
                0xffffu32 => {
                    // do nothing
                }
                _ => {
                    // do nothing
                }
            }
        }
        8 | 9 => {
            match FONT_AREA[fnt as usize] as u32 {
                #[cfg(target_os = "macos")]
                0xffffu32 => {
                    aat::aat_print_font_name(
                        c as i32,
                        (FONT_LAYOUT_ENGINE[fnt as usize]) as _,
                        arg1,
                        arg2,
                    );
                }
                #[cfg(not(target_os = "macos"))]
                0xffffu32 => {
                    // do nothing
                }
                0xfffeu32 => {
                    if usingGraphite(FONT_LAYOUT_ENGINE[fnt as usize] as XeTeXLayoutEngine) as i32
                        != 0
                    {
                        gr_print_font_name(c as i32, FONT_LAYOUT_ENGINE[fnt as usize], arg1, arg2);
                    }
                }
                _ => {}
            }
        }
        10 => match FONT_AREA[fnt as usize] as u32 {
            0xffffu32 | 0xfffeu32 => print_glyph_name(fnt, arg1),
            _ => {}
        },
        11 => {
            p = MEM[(p + 5) as usize].b32.s1;
            while p != TEX_NULL
                && (p < hi_mem_min
                    && (MEM[p as usize].b16.s1 as i32 == 3
                        || MEM[p as usize].b16.s1 as i32 == 4
                        || MEM[p as usize].b16.s1 as i32 == 5
                        || MEM[p as usize].b16.s1 as i32 == 12
                        || MEM[p as usize].b16.s1 as i32 == 7
                            && MEM[(p + 1) as usize].b32.s0 == TEX_NULL
                            && MEM[(p + 1) as usize].b32.s1 == TEX_NULL
                            && MEM[p as usize].b16.s0 as i32 == 0
                        || MEM[p as usize].b16.s1 as i32 == 9 && MEM[(p + 1) as usize].b32.s1 == 0
                        || MEM[p as usize].b16.s1 as i32 == 11
                            && (MEM[(p + 1) as usize].b32.s1 == 0
                                || MEM[p as usize].b16.s0 as i32 == 0)
                        || MEM[p as usize].b16.s1 as i32 == 10
                            && MEM[(p + 1) as usize].b32.s0 == 0
                        || MEM[p as usize].b16.s1 as i32 == 0
                            && MEM[(p + 1) as usize].b32.s1 == 0
                            && MEM[(p + 3) as usize].b32.s1 == 0
                            && MEM[(p + 2) as usize].b32.s1 == 0
                            && MEM[(p + 5) as usize].b32.s1 == TEX_NULL)
                    || p < hi_mem_min
                        && MEM[p as usize].b16.s1 as i32 == 10
                        && MEM[p as usize].b16.s0 as i32 == 7 + 1)
            {
                p = MEM[p as usize].b32.s1
            }
            if p != TEX_NULL
                && p < hi_mem_min
                && MEM[p as usize].b16.s1 as i32 == 40
                && MEM[p as usize].b16.s0 as i32 == 0
            {
                print_scaled(MEM[(p + 1) as usize].b32.s1);
            } else {
                print('0' as i32);
            }
            print_cstr(b"pt");
        }
        12 => {
            q = MEM[(p + 5) as usize].b32.s1;
            p = prev_rightmost(q, TEX_NULL);
            while p != TEX_NULL
                && (p < hi_mem_min
                    && (MEM[p as usize].b16.s1 as i32 == 3
                        || MEM[p as usize].b16.s1 as i32 == 4
                        || MEM[p as usize].b16.s1 as i32 == 5
                        || MEM[p as usize].b16.s1 as i32 == 12
                        || MEM[p as usize].b16.s1 as i32 == 7
                            && MEM[(p + 1) as usize].b32.s0 == TEX_NULL
                            && MEM[(p + 1) as usize].b32.s1 == TEX_NULL
                            && MEM[p as usize].b16.s0 as i32 == 0
                        || MEM[p as usize].b16.s1 as i32 == 9 && MEM[(p + 1) as usize].b32.s1 == 0
                        || MEM[p as usize].b16.s1 as i32 == 11
                            && (MEM[(p + 1) as usize].b32.s1 == 0
                                || MEM[p as usize].b16.s0 as i32 == 0)
                        || MEM[p as usize].b16.s1 as i32 == 10
                            && MEM[(p + 1) as usize].b32.s0 == 0
                        || MEM[p as usize].b16.s1 as i32 == 0
                            && MEM[(p + 1) as usize].b32.s1 == 0
                            && MEM[(p + 3) as usize].b32.s1 == 0
                            && MEM[(p + 2) as usize].b32.s1 == 0
                            && MEM[(p + 5) as usize].b32.s1 == TEX_NULL)
                    || p < hi_mem_min
                        && MEM[p as usize].b16.s1 as i32 == 10
                        && MEM[p as usize].b16.s0 as i32 == 8 + 1)
            {
                p = prev_rightmost(q, p)
            }
            if p != TEX_NULL
                && p < hi_mem_min
                && MEM[p as usize].b16.s1 as i32 == 40
                && MEM[p as usize].b16.s0 as i32 == 1
            {
                print_scaled(MEM[(p + 1) as usize].b32.s1);
            } else {
                print('0' as i32);
            }
            print_cstr(b"pt");
        }
        15 => print_file_name(job_name, 0i32, 0i32),
        _ => {}
    }
    selector = old_setting_0;
    MEM[(4999999 - 12) as usize].b32.s1 = str_toks_cat(b, cat);
    begin_token_list(MEM[(4999999 - 3) as usize].b32.s1, 5_u16);
}
pub(crate) unsafe fn scan_toks(mut macro_def: bool, mut xpand: bool) -> i32 {
    let mut current_block: u64;
    let mut t: i32 = 0;
    let mut s: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut unbalance: i32 = 0;
    let mut hash_brace: i32 = 0;
    if macro_def {
        scanner_status = 2_u8
    } else {
        scanner_status = 5_u8
    }
    warning_index = cur_cs;
    def_ref = get_avail();
    MEM[def_ref as usize].b32.s0 = TEX_NULL;
    p = def_ref;
    hash_brace = 0i32;
    t = 0x1800000i32 + '0' as i32;
    if macro_def {
        loop
        /*493: */
        {
            get_token();
            if cur_tok < 0x600000i32 {
                current_block = 7086859973843054082;
                break;
            }
            if cur_cmd as i32 == 6i32 {
                /*495: */
                s = 0x1a00000i32 + cur_chr;
                get_token();
                if cur_cmd as i32 == 1i32 {
                    hash_brace = cur_tok;
                    q = get_avail();
                    MEM[p as usize].b32.s1 = q;
                    MEM[q as usize].b32.s0 = cur_tok;
                    p = q;
                    q = get_avail();
                    MEM[p as usize].b32.s1 = q;
                    MEM[q as usize].b32.s0 = 0x1c00000;
                    p = q;
                    current_block = 2723324002591448311;
                    break;
                } else if t == 0x1800000i32 + '0' as i32 + 9i32 {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"You already have nine parameters");
                    help_ptr = 1_u8;
                    help_line[0] = b"I\'m going to ignore the # sign you just used.";
                    error();
                } else {
                    t += 1;
                    if cur_tok != t {
                        if file_line_error_style_p != 0 {
                            print_file_line();
                        } else {
                            print_nl_cstr(b"! ");
                        }
                        print_cstr(b"Parameters must be numbered consecutively");
                        help_ptr = 2_u8;
                        help_line[1] =
                            b"I\'ve inserted the digit you should have used after the #.";
                        help_line[0] = b"Type `1\' to delete what you did use.";
                        back_error();
                    }
                    cur_tok = s
                }
            }
            q = get_avail();
            MEM[p as usize].b32.s1 = q;
            MEM[q as usize].b32.s0 = cur_tok;
            p = q
        }
        match current_block {
            2723324002591448311 => {}
            _ => {
                q = get_avail();
                MEM[p as usize].b32.s1 = q;
                MEM[q as usize].b32.s0 = 0x1c00000;
                p = q;
                if cur_cmd as i32 == 2i32 {
                    /*494: */
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Missing { inserted");
                    align_state += 1;
                    help_ptr = 2_u8;
                    help_line[1] =
                        b"Where was the left brace? You said something like `\\def\\a}\',";
                    help_line[0] = b"which I\'m going to interpret as `\\def\\a{}\'.";
                    error();
                    current_block = 17047787784317322882;
                } else {
                    current_block = 2723324002591448311;
                }
            }
        }
    } else {
        scan_left_brace();
        current_block = 2723324002591448311;
    }
    match current_block {
        2723324002591448311 => {
            unbalance = 1i32;
            loop {
                if xpand {
                    loop
                    /*497: */
                    {
                        get_next();
                        if cur_cmd as i32 >= 113i32 {
                            if MEM[MEM[cur_chr as usize].b32.s1 as usize].b32.s0
                                == 0x1c00000i32 + 1i32
                            {
                                cur_cmd = 0i32 as eight_bits;
                                cur_chr = 0x10ffffi32 + 2i32
                            }
                        }
                        if cur_cmd as i32 <= 102i32 {
                            break;
                        }
                        if cur_cmd as i32 != 111i32 {
                            expand();
                        } else {
                            q = the_toks();
                            if MEM[(4999999 - 3) as usize].b32.s1 != TEX_NULL {
                                MEM[p as usize].b32.s1 = MEM[(4999999 - 3) as usize].b32.s1;
                                p = q
                            }
                        }
                    }
                    x_token();
                } else {
                    get_token();
                }
                if cur_tok < 0x600000i32 {
                    if (cur_cmd as i32) < 2i32 {
                        unbalance += 1
                    } else {
                        unbalance -= 1;
                        if unbalance == 0i32 {
                            break;
                        }
                    }
                } else if cur_cmd as i32 == 6i32 {
                    if macro_def {
                        /*498: */
                        s = cur_tok;
                        if xpand {
                            get_x_token();
                        } else {
                            get_token();
                        }
                        if cur_cmd as i32 != 6i32 {
                            if cur_tok <= 0x1800000i32 + '0' as i32 || cur_tok > t {
                                if file_line_error_style_p != 0 {
                                    print_file_line();
                                } else {
                                    print_nl_cstr(b"! ");
                                }
                                print_cstr(b"Illegal parameter number in definition of ");
                                sprint_cs(warning_index);
                                help_ptr = 3_u8;
                                help_line[2] = b"You meant to type ## instead of #, right?";
                                help_line[1] =
                                    b"Or maybe a } was forgotten somewhere earlier, and things";
                                help_line[0] =
                                    b"are all screwed up? I\'m going to assume that you meant ##.";
                                back_error();
                                cur_tok = s
                            } else {
                                cur_tok = 0xa00000i32 - 48i32 + cur_chr
                            }
                        }
                    }
                }
                q = get_avail();
                MEM[p as usize].b32.s1 = q;
                MEM[q as usize].b32.s0 = cur_tok;
                p = q
            }
        }
        _ => {}
    }
    scanner_status = 0_u8;
    if hash_brace != 0i32 {
        q = get_avail();
        MEM[p as usize].b32.s1 = q;
        MEM[q as usize].b32.s0 = hash_brace;
        p = q
    }
    p
}
pub(crate) unsafe fn read_toks(mut n: i32, mut r: i32, mut j: i32) {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut s: i32 = 0;
    let mut m: small_number = 0;
    scanner_status = 2_u8;
    warning_index = r;
    def_ref = get_avail();
    MEM[def_ref as usize].b32.s0 = TEX_NULL;
    p = def_ref;
    q = get_avail();
    MEM[p as usize].b32.s1 = q;
    MEM[q as usize].b32.s0 = 0x1c00000;
    p = q;
    if n < 0i32 || n > 15i32 {
        m = 16i32 as small_number
    } else {
        m = n as small_number
    }
    s = align_state;
    align_state = 1000000i64 as i32;
    loop {
        /*502:*/
        begin_file_reading();
        cur_input.name = m as i32 + 1i32;
        assert!(
            read_open[m as usize] as i32 != 2,
            /*503:*/
            "terminal input forbidden"
        );
        /*505:*/
        if read_open[m as usize] as i32 == 1i32 {
            /*504:*/
            if input_line(read_file[m as usize]) != 0 {
                read_open[m as usize] = 0_u8
            } else {
                u_close(read_file[m as usize]);
                read_open[m as usize] = 2_u8
            }
        } else if input_line(read_file[m as usize]) == 0 {
            u_close(read_file[m as usize]);
            read_open[m as usize] = 2_u8;
            if align_state as i64 != 1000000 {
                runaway();
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"File ended within ");
                print_esc_cstr(b"read");
                help_ptr = 1_u8;
                help_line[0] = b"This \\read has unbalanced braces.";
                align_state = 1000000i64 as i32;
                error();
            }
        }
        cur_input.limit = last;
        if EQTB[(INT_BASE + 48i32) as usize].b32.s1 < 0i32
            || EQTB[(INT_BASE + 48i32) as usize].b32.s1 > 255i32
        {
            cur_input.limit -= 1
        } else {
            *buffer.offset(cur_input.limit as isize) = EQTB[(INT_BASE + 48i32) as usize].b32.s1
        }
        first = cur_input.limit + 1i32;
        cur_input.loc = cur_input.start;
        cur_input.state = 33_u16;
        if j == 1i32 {
            while cur_input.loc <= cur_input.limit {
                cur_chr = *buffer.offset(cur_input.loc as isize);
                cur_input.loc += 1;
                if cur_chr == ' ' as i32 {
                    cur_tok = 0x1400020i32
                } else {
                    cur_tok = cur_chr + 0x1800000i32
                }
                q = get_avail();
                MEM[p as usize].b32.s1 = q;
                MEM[q as usize].b32.s0 = cur_tok;
                p = q
            }
        } else {
            loop {
                get_token();
                if cur_tok == 0i32 {
                    break;
                }
                if (align_state as i64) < 1000000 {
                    loop {
                        get_token();
                        if !(cur_tok != 0i32) {
                            break;
                        }
                    }
                    align_state = 1000000i64 as i32;
                    break;
                } else {
                    q = get_avail();
                    MEM[p as usize].b32.s1 = q;
                    MEM[q as usize].b32.s0 = cur_tok;
                    p = q
                }
            }
        }
        end_file_reading();
        if !(align_state as i64 != 1000000) {
            break;
        }
    }
    cur_val = def_ref;
    scanner_status = 0_u8;
    align_state = s;
}
pub(crate) unsafe fn pass_text() {
    let mut l: i32 = 0;
    let mut save_scanner_status: small_number = 0;
    save_scanner_status = scanner_status as small_number;
    scanner_status = 1_u8;
    l = 0i32;
    skip_line = line;
    loop {
        get_next();
        if cur_cmd as i32 == 108i32 {
            if l == 0i32 {
                break;
            }
            if cur_chr == 2i32 {
                l -= 1
            }
        } else if cur_cmd as i32 == 107i32 {
            l += 1
        }
    }
    scanner_status = save_scanner_status as u8;
    if EQTB[(INT_BASE + 60i32) as usize].b32.s1 > 0i32 {
        show_cur_cmd_chr();
    };
}
pub(crate) unsafe fn change_if_limit(mut l: small_number, mut p: i32) {
    let mut q: i32 = 0;
    if p == cond_ptr {
        if_limit = l as u8
    } else {
        q = cond_ptr;
        loop {
            if q == TEX_NULL {
                confusion(b"if");
            }
            if MEM[q as usize].b32.s1 == p {
                MEM[q as usize].b16.s1 = l as u16;
                return;
            }
            q = MEM[q as usize].b32.s1
        }
    };
}
pub(crate) unsafe fn conditional() {
    let mut current_block: u64;
    let mut b: bool = false;
    let mut e: bool = false;
    let mut r: u8 = 0;
    let mut m: i32 = 0;
    let mut n: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut save_scanner_status: small_number = 0;
    let mut save_cond_ptr: i32 = 0;
    let mut this_if: small_number = 0;
    let mut is_unless: bool = false;
    if EQTB[(INT_BASE + 60i32) as usize].b32.s1 > 0i32 {
        if EQTB[(INT_BASE + 36i32) as usize].b32.s1 <= 1i32 {
            show_cur_cmd_chr();
        }
    }
    p = get_node(2i32);
    MEM[p as usize].b32.s1 = cond_ptr;
    MEM[p as usize].b16.s1 = if_limit as u16;
    MEM[p as usize].b16.s0 = cur_if as u16;
    MEM[(p + 1) as usize].b32.s1 = if_line;
    cond_ptr = p;
    cur_if = cur_chr as small_number;
    if_limit = 1_u8;
    if_line = line;
    save_cond_ptr = cond_ptr;
    is_unless = cur_chr >= 32i32;
    this_if = (cur_chr % 32i32) as small_number;
    match this_if as i32 {
        0 | 1 => {
            get_x_token();
            if cur_cmd as i32 == 0i32 {
                if cur_chr == 0x10ffffi32 + 2i32 {
                    cur_cmd = 13i32 as eight_bits;
                    cur_chr = cur_tok - (0x1ffffffi32 + 1i32)
                }
            }
            if cur_cmd as i32 > 13i32 || cur_chr > 0x10ffffi32 {
                m = 0i32;
                n = 0x10ffffi32 + 1i32
            } else {
                m = cur_cmd as i32;
                n = cur_chr
            }
            get_x_token();
            if cur_cmd as i32 == 0i32 {
                if cur_chr == 0x10ffffi32 + 2i32 {
                    cur_cmd = 13i32 as eight_bits;
                    cur_chr = cur_tok - (0x1ffffffi32 + 1i32)
                }
            }
            if cur_cmd as i32 > 13i32 || cur_chr > 0x10ffffi32 {
                cur_cmd = 0i32 as eight_bits;
                cur_chr = 0x10ffffi32 + 1i32
            }
            if this_if as i32 == 0i32 {
                b = n == cur_chr
            } else {
                b = m == cur_cmd as i32
            }
            current_block = 16915215315900843183;
        }
        2 | 3 => {
            if this_if as i32 == 2i32 {
                scan_int();
            } else {
                scan_dimen(false, false, false);
            }
            n = cur_val;
            loop {
                get_x_token();
                if !(cur_cmd as i32 == 10i32) {
                    break;
                }
            }
            if cur_tok >= 0x1800000i32 + 60i32 && cur_tok <= 0x1800000i32 + 62i32 {
                r = (cur_tok - 0x1800000i32) as u8
            } else {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Missing = inserted for ");
                print_cmd_chr(107_u16, this_if as i32);
                help_ptr = 1_u8;
                help_line[0] = b"I was expecting to see `<\', `=\', or `>\'. Didn\'t.";
                back_error();
                r = '=' as i32 as u8
            }
            if this_if as i32 == 2i32 {
                scan_int();
            } else {
                scan_dimen(false, false, false);
            }
            match r as i32 {
                60 => {
                    /*"<"*/
                    b = n < cur_val
                }
                61 => {
                    /*"="*/
                    b = n == cur_val
                }
                62 => {
                    /*">"*/
                    b = n > cur_val
                }
                _ => {}
            } /*527:*/
            current_block = 16915215315900843183; /* !shellenabledp */
        }
        4 => {
            scan_int();
            b = cur_val & 1i32 != 0;
            current_block = 16915215315900843183;
        }
        5 => {
            b = (cur_list.mode as i32).abs() == 1i32;
            current_block = 16915215315900843183;
        }
        6 => {
            b = (cur_list.mode as i32).abs() == 104i32;
            current_block = 16915215315900843183;
        }
        7 => {
            b = (cur_list.mode as i32).abs() == 207i32;
            current_block = 16915215315900843183;
        }
        8 => {
            b = (cur_list.mode as i32) < 0i32;
            current_block = 16915215315900843183;
        }
        9 | 10 | 11 => {
            scan_register_num();
            if cur_val < 256i32 {
                p = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr == TEX_NULL {
                    p = TEX_NULL
                } else {
                    p = MEM[(cur_ptr + 1) as usize].b32.s1
                }
            }
            if this_if as i32 == 9i32 {
                b = p == TEX_NULL
            } else if p == TEX_NULL {
                b = false
            } else if this_if as i32 == 10i32 {
                b = MEM[p as usize].b16.s1 as i32 == 0
            } else {
                b = MEM[p as usize].b16.s1 as i32 == 1
            }
            current_block = 16915215315900843183;
        }
        12 => {
            save_scanner_status = scanner_status as small_number;
            scanner_status = 0_u8;
            get_next();
            n = cur_cs;
            p = cur_cmd as i32;
            q = cur_chr;
            get_next();
            if cur_cmd as i32 != p {
                b = false
            } else if (cur_cmd as i32) < 113i32 {
                b = cur_chr == q
            } else {
                p = MEM[cur_chr as usize].b32.s1;
                q = MEM[EQTB[n as usize].b32.s1 as usize].b32.s1;
                if p == q {
                    b = true
                } else {
                    while p != TEX_NULL && q != TEX_NULL {
                        if MEM[p as usize].b32.s0 != MEM[q as usize].b32.s0 {
                            p = TEX_NULL
                        } else {
                            p = MEM[p as usize].b32.s1;
                            q = MEM[q as usize].b32.s1
                        }
                    }
                    b = p == TEX_NULL && q == TEX_NULL
                }
            }
            scanner_status = save_scanner_status as u8;
            current_block = 16915215315900843183;
        }
        13 => {
            scan_four_bit_int_or_18();
            if cur_val == 18i32 {
                b = true
            } else {
                b = read_open[cur_val as usize] as i32 == 2i32
            }
            current_block = 16915215315900843183;
        }
        14 => {
            b = true;
            current_block = 16915215315900843183;
        }
        15 => {
            b = false;
            current_block = 16915215315900843183;
        }
        17 => {
            save_scanner_status = scanner_status as small_number;
            scanner_status = 0_u8;
            get_next();
            b = cur_cmd as i32 != 103i32;
            scanner_status = save_scanner_status as u8;
            current_block = 16915215315900843183;
        }
        18 => {
            n = get_avail();
            p = n;
            e = is_in_csname;
            is_in_csname = true;
            loop {
                get_x_token();
                if cur_cs == 0i32 {
                    q = get_avail();
                    MEM[p as usize].b32.s1 = q;
                    MEM[q as usize].b32.s0 = cur_tok;
                    p = q
                }
                if !(cur_cs == 0i32) {
                    break;
                }
            }
            if cur_cmd as i32 != 67i32 {
                /*391:*/
                if file_line_error_style_p != 0 {
                    print_file_line(); /*:1556*/
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Missing ");
                print_esc_cstr(b"endcsname");
                print_cstr(b" inserted");
                help_ptr = 2_u8;
                help_line[1] = b"The control sequence marked <to be read again> should";
                help_line[0] = b"not appear between \\csname and \\endcsname.";
                back_error();
            }
            m = first;
            p = MEM[n as usize].b32.s1;
            while p != TEX_NULL {
                if m >= max_buf_stack {
                    max_buf_stack = m + 1i32;
                    if max_buf_stack == buf_size {
                        overflow(b"buffer size", buf_size);
                    }
                }
                *buffer.offset(m as isize) = MEM[p as usize].b32.s0 % 0x200000;
                m += 1;
                p = MEM[p as usize].b32.s1
            }
            if m == first {
                cur_cs = 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32)
            } else if m == first + 1i32 {
                cur_cs = 1i32 + (0x10ffffi32 + 1i32) + *buffer.offset(first as isize)
            } else {
                cur_cs = id_lookup(first, m - first)
            }
            flush_list(n);
            b = EQTB[cur_cs as usize].b16.s1 as i32 != 103i32;
            is_in_csname = e;
            current_block = 16915215315900843183;
        }
        20 => {
            b = is_in_csname;
            current_block = 16915215315900843183;
        }
        19 => {
            scan_font_ident();
            n = cur_val;
            scan_usv_num();
            if FONT_AREA[n as usize] as u32 == 0xffffu32
                || FONT_AREA[n as usize] as u32 == 0xfffeu32
            {
                b = map_char_to_glyph(n, cur_val) > 0i32
            } else if FONT_BC[n as usize] as i32 <= cur_val && FONT_EC[n as usize] as i32 >= cur_val
            {
                b = FONT_INFO[(CHAR_BASE[n as usize] + effective_char(1i32 != 0, n, cur_val as u16))
                    as usize]
                    .b16
                    .s3 as i32
                    > 0i32
            } else {
                b = false
            }
            current_block = 16915215315900843183;
        }
        16 => {
            scan_int();
            n = cur_val;
            if EQTB[(INT_BASE + 36i32) as usize].b32.s1 > 1i32 {
                begin_diagnostic();
                print_cstr(b"{case ");
                print_int(n);
                print_char('}' as i32);
                end_diagnostic(false);
            }
            loop {
                if !(n != 0i32) {
                    current_block = 8672804474533504599;
                    break;
                }
                pass_text();
                if cond_ptr == save_cond_ptr {
                    if !(cur_chr == 4i32) {
                        current_block = 17018179191097466409;
                        break;
                    }
                    n -= 1
                } else if cur_chr == 2i32 {
                    /*515:*/
                    if IF_STACK[IN_OPEN] == cond_ptr {
                        if_warning();
                    }
                    p = cond_ptr;
                    if_line = MEM[(p + 1) as usize].b32.s1;
                    cur_if = MEM[p as usize].b16.s0 as small_number;
                    if_limit = MEM[p as usize].b16.s1 as u8;
                    cond_ptr = MEM[p as usize].b32.s1;
                    free_node(p, 2i32);
                }
            }
            match current_block {
                17018179191097466409 => {}
                _ => {
                    change_if_limit(4i32 as small_number, save_cond_ptr);
                    return;
                }
            }
        }
        21 => {
            save_scanner_status = scanner_status as small_number;
            scanner_status = 0_u8;
            get_next();
            scanner_status = save_scanner_status as u8;
            if cur_cs < 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) + 1i32 {
                m = prim_lookup(cur_cs - (1i32 + (0x10ffffi32 + 1i32)))
            } else {
                m = prim_lookup((*hash.offset(cur_cs as isize)).s1)
            }
            b = cur_cmd as i32 != 103i32
                && m != 0i32
                && cur_cmd as i32 == prim_eqtb[m as usize].b16.s1 as i32
                && cur_chr == prim_eqtb[m as usize].b32.s1;
            current_block = 16915215315900843183;
        }
        _ => current_block = 16915215315900843183,
    }
    match current_block {
        16915215315900843183 => {
            if is_unless {
                b = !b
            }
            if EQTB[(INT_BASE + 36i32) as usize].b32.s1 > 1i32 {
                /*521:*/
                begin_diagnostic();
                if b {
                    print_cstr(b"{true}");
                } else {
                    print_cstr(b"{false}");
                }
                end_diagnostic(false);
            }
            if b {
                change_if_limit(3i32 as small_number, save_cond_ptr);
                return;
            }
            loop {
                pass_text();
                if cond_ptr == save_cond_ptr {
                    if cur_chr != 4i32 {
                        break;
                    }
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Extra ");
                    print_esc_cstr(b"or");
                    help_ptr = 1_u8;
                    help_line[0] = b"I\'m ignoring this; it doesn\'t match any \\if.";
                    error();
                } else if cur_chr == 2i32 {
                    /*515:*/
                    if IF_STACK[IN_OPEN] == cond_ptr {
                        if_warning();
                    }
                    p = cond_ptr;
                    if_line = MEM[(p + 1) as usize].b32.s1;
                    cur_if = MEM[p as usize].b16.s0 as small_number;
                    if_limit = MEM[p as usize].b16.s1 as u8;
                    cond_ptr = MEM[p as usize].b32.s1;
                    free_node(p, 2i32);
                }
            }
        }
        _ => {}
    }
    if cur_chr == 2i32 {
        /*515:*/
        if IF_STACK[IN_OPEN] == cond_ptr {
            if_warning();
        }
        p = cond_ptr;
        if_line = MEM[(p + 1) as usize].b32.s1;
        cur_if = MEM[p as usize].b16.s0 as small_number;
        if_limit = MEM[p as usize].b16.s1 as u8;
        cond_ptr = MEM[p as usize].b32.s1;
        free_node(p, 2i32);
    } else {
        if_limit = 2_u8
    };
}
pub(crate) unsafe fn begin_name() {
    area_delimiter = 0i32;
    ext_delimiter = 0i32;
    quoted_filename = false;
    file_name_quote_char = 0i32 as UTF16_code;
}
pub(crate) unsafe fn more_name(mut c: UTF16_code) -> bool {
    if stop_at_space as i32 != 0 && file_name_quote_char as i32 == 0i32 && c as i32 == ' ' as i32 {
        return false;
    }
    if stop_at_space as i32 != 0
        && file_name_quote_char as i32 != 0i32
        && c as i32 == file_name_quote_char as i32
    {
        file_name_quote_char = 0i32 as UTF16_code;
        return true;
    }
    if stop_at_space as i32 != 0
        && file_name_quote_char as i32 == 0i32
        && (c as i32 == '\"' as i32 || c as i32 == '\'' as i32)
    {
        file_name_quote_char = c;
        quoted_filename = true;
        return true;
    }
    if pool_ptr + 1i32 > pool_size {
        overflow(b"pool size", pool_size - init_pool_ptr);
    }
    let fresh37 = pool_ptr;
    pool_ptr = pool_ptr + 1;
    *str_pool.offset(fresh37 as isize) = c;
    if c as i32 == '/' as i32 {
        area_delimiter = cur_length();
        ext_delimiter = 0i32
    } else if c as i32 == '.' as i32 {
        ext_delimiter = cur_length()
    }
    true
}
pub(crate) unsafe fn end_name() {
    let mut temp_str: str_number = 0;
    let mut j: pool_pointer = 0;
    if str_ptr + 3i32 > max_strings {
        overflow(b"number of strings", max_strings - init_str_ptr);
    }
    /* area_delimiter is the length from the start of the filename to the
     * directory seperator "/", which we use to construct the stringpool
     * string `cur_area`. If there was already a string in the stringpool for
     * the area, reuse it. */
    if area_delimiter == 0i32 {
        cur_area = (65536 + 1i32 as i64) as str_number
    } else {
        cur_area = str_ptr;
        *str_start.offset(((str_ptr + 1i32) as i64 - 65536) as isize) =
            *str_start.offset((str_ptr - 65536i32) as isize) + area_delimiter;
        str_ptr += 1;
        temp_str = search_string(cur_area);
        if temp_str > 0i32 {
            cur_area = temp_str;
            str_ptr -= 1;
            j = *str_start.offset(((str_ptr + 1i32) as i64 - 65536) as isize);
            while j <= pool_ptr - 1i32 {
                *str_pool.offset((j - area_delimiter) as isize) = *str_pool.offset(j as isize);
                j += 1
            }
            pool_ptr = pool_ptr - area_delimiter
        }
    }
    /* ext_delimiter is the length from the start of the filename to the
     * extension '.' delimiter, which we use to construct the stringpool
     * strings `cur_ext` and `cur_name`. */
    if ext_delimiter == 0i32 {
        cur_ext = (65536 + 1i32 as i64) as str_number;
        cur_name = slow_make_string()
    } else {
        cur_name = str_ptr;
        *str_start.offset(((str_ptr + 1i32) as i64 - 65536) as isize) =
            *str_start.offset((str_ptr - 65536i32) as isize) + ext_delimiter
                - area_delimiter
                - 1i32;
        str_ptr += 1;
        cur_ext = make_string();
        str_ptr -= 1;
        temp_str = search_string(cur_name);
        if temp_str > 0i32 {
            cur_name = temp_str;
            str_ptr -= 1;
            j = *str_start.offset(((str_ptr + 1i32) as i64 - 65536) as isize);
            while j <= pool_ptr - 1i32 {
                *str_pool.offset((j - ext_delimiter + area_delimiter + 1i32) as isize) =
                    *str_pool.offset(j as isize);
                j += 1
            }
            pool_ptr = pool_ptr - ext_delimiter + area_delimiter + 1i32
        }
        cur_ext = slow_make_string()
    };
}
pub(crate) unsafe fn pack_file_name(mut n: str_number, mut a: str_number, mut e: str_number) {
    // Note that we populate the buffer in an order different than how the
    // arguments are passed to this function!
    let mut work_buffer: *mut i8 =
        xmalloc_array((length(a) + length(n) + length(e)) as usize * 3 + 1);
    *work_buffer.offset(0) = '\u{0}' as i32 as i8;
    let mut a_utf8: *mut i8 = gettexstring(a);
    strcat(work_buffer, a_utf8);
    free(a_utf8 as *mut libc::c_void);
    let mut n_utf8: *mut i8 = gettexstring(n);
    strcat(work_buffer, n_utf8);
    free(n_utf8 as *mut libc::c_void);
    let mut e_utf8: *mut i8 = gettexstring(e);
    strcat(work_buffer, e_utf8);
    free(e_utf8 as *mut libc::c_void);
    name_length = strlen(work_buffer) as i32;
    free(name_of_file as *mut libc::c_void);
    name_of_file = xmalloc_array(name_length as usize + 1);
    strcpy(name_of_file, work_buffer);
    free(work_buffer as *mut libc::c_void);
}
pub(crate) unsafe fn make_name_string() -> str_number {
    let mut k: i32 = 0;
    let mut save_area_delimiter: pool_pointer = 0;
    let mut save_ext_delimiter: pool_pointer = 0;
    let mut save_name_in_progress: bool = false;
    let mut save_stop_at_space: bool = false;
    if pool_ptr + name_length > pool_size || str_ptr == max_strings || cur_length() > 0i32 {
        return '?' as i32;
    }
    make_utf16_name();
    k = 0i32;
    while k < name_length16 {
        let fresh38 = pool_ptr;
        pool_ptr = pool_ptr + 1;
        *str_pool.offset(fresh38 as isize) = *name_of_file16.offset(k as isize);
        k += 1
    }
    let mut Result: str_number = make_string();
    save_area_delimiter = area_delimiter;
    save_ext_delimiter = ext_delimiter;
    save_name_in_progress = name_in_progress;
    save_stop_at_space = stop_at_space;
    name_in_progress = true;
    begin_name();
    stop_at_space = false;
    k = 0i32;
    while k < name_length16 && more_name(*name_of_file16.offset(k as isize)) as i32 != 0 {
        k += 1
    }
    stop_at_space = save_stop_at_space;
    end_name();
    name_in_progress = save_name_in_progress;
    area_delimiter = save_area_delimiter;
    ext_delimiter = save_ext_delimiter;
    Result
}
pub(crate) unsafe fn scan_file_name() {
    name_in_progress = true;
    begin_name();
    loop {
        get_x_token();
        if !(cur_cmd as i32 == 10i32) {
            break;
        }
    }
    loop {
        if cur_cmd as i32 > 12i32 || cur_chr > 0xffffi32 {
            back_input();
            break;
        } else {
            if !more_name(cur_chr as UTF16_code) {
                break;
            }
            get_x_token();
        }
    }
    end_name();
    name_in_progress = false;
}
pub(crate) unsafe fn pack_job_name(s: &[u8]) {
    cur_area = (65536 + 1i32 as i64) as str_number;
    cur_ext = maketexstring(s);
    cur_name = job_name;
    pack_file_name(cur_name, cur_area, cur_ext);
}
pub(crate) unsafe fn open_log_file() {
    let mut k: i32 = 0;
    let mut l: i32 = 0;
    let old_setting_0 = selector;
    if job_name == 0i32 {
        job_name = maketexstring(b"texput")
    }
    pack_job_name(b".log");
    log_file = ttstub_output_open(name_of_file, 0i32);
    if log_file.is_none() {
        abort!(
            "cannot open log file output \"{}\"",
            CStr::from_ptr(name_of_file).display()
        );
    }
    texmf_log_name = make_name_string();
    selector = Selector::LOG_ONLY;
    log_opened = true;
    INPUT_STACK[INPUT_PTR] = cur_input;
    /* Here we catch the log file up with anything that has already been
     * printed. The eqtb reference is end_line_char. */
    print_nl_cstr(b"**");
    l = INPUT_STACK[0].limit;
    if *buffer.offset(l as isize) == EQTB[(INT_BASE + 48i32) as usize].b32.s1 {
        l -= 1
    }
    k = 1i32;
    while k <= l {
        print(*buffer.offset(k as isize));
        k += 1
    }
    print_ln();
    selector = (u8::from(old_setting_0) + 2).into();
}
pub(crate) unsafe fn start_input(mut primary_input_name: *const i8) {
    let mut format = TTInputFormat::TEX;
    let mut temp_str: str_number = 0;
    if !primary_input_name.is_null() {
        /* If this is the case, we're opening the primary input file, and the
         * name that we should use to refer to it has been handed directly to
         * us. We emulate the hacks used below to fill in cur_name, etc., from
         * a UTF-8 C string. It looks like the `cur_{name,area,ext}` strings
         * are hardly used so it'd be nice to get rid of them someday. */
        format = TTInputFormat::TECTONIC_PRIMARY;
        name_in_progress = true;
        begin_name();
        stop_at_space = false;
        let mut cp: *const u8 = primary_input_name as *const u8;
        assert!(
            !((pool_ptr as usize).wrapping_add(strlen(primary_input_name).wrapping_mul(2))
                >= pool_size as usize),
            "string pool overflow [{} bytes]",
            pool_size,
        );
        let mut rval: u32 = 0;
        loop {
            let fresh39 = cp;
            cp = cp.offset(1);
            rval = *fresh39 as u32;
            if !(rval != 0_u32) {
                break;
            }
            let mut extraBytes: u16 = bytesFromUTF8[rval as usize] as u16;
            let mut current_block_21: u64;
            match extraBytes as i32 {
                5 => {
                    /* note: code falls through cases! */
                    rval <<= 6i32;
                    if *cp != 0 {
                        let fresh40 = cp;
                        cp = cp.offset(1);
                        rval = (rval as u32).wrapping_add(*fresh40 as u32) as u32 as u32
                    }
                    current_block_21 = 7676382540965064243;
                }
                4 => current_block_21 = 7676382540965064243,
                3 => current_block_21 = 13258898395114305131,
                2 => current_block_21 = 10625751394499422232,
                1 => current_block_21 = 4051951890355284227,
                0 | _ => current_block_21 = 14818589718467733107,
            }
            match current_block_21 {
                7676382540965064243 => {
                    rval <<= 6i32;
                    if *cp != 0 {
                        let fresh41 = cp;
                        cp = cp.offset(1);
                        rval = (rval as u32).wrapping_add(*fresh41 as u32) as u32 as u32
                    }
                    current_block_21 = 13258898395114305131;
                }
                _ => {}
            }
            match current_block_21 {
                13258898395114305131 => {
                    rval <<= 6i32;
                    if *cp != 0 {
                        let fresh42 = cp;
                        cp = cp.offset(1);
                        rval = (rval as u32).wrapping_add(*fresh42 as u32) as u32 as u32
                    }
                    current_block_21 = 10625751394499422232;
                }
                _ => {}
            }
            match current_block_21 {
                10625751394499422232 => {
                    rval <<= 6i32;
                    if *cp != 0 {
                        let fresh43 = cp;
                        cp = cp.offset(1);
                        rval = (rval as u32).wrapping_add(*fresh43 as u32) as u32 as u32
                    }
                    current_block_21 = 4051951890355284227;
                }
                _ => {}
            }
            match current_block_21 {
                4051951890355284227 => {
                    rval <<= 6i32;
                    if *cp != 0 {
                        let fresh44 = cp;
                        cp = cp.offset(1);
                        rval = (rval as u32).wrapping_add(*fresh44 as u32) as u32 as u32
                    }
                }
                _ => {}
            }
            rval = (rval as u32).wrapping_sub(offsetsFromUTF8[extraBytes as usize]) as u32 as u32;
            if rval > 0xffff_u32 {
                rval = (rval as u32).wrapping_sub(0x10000_u32) as u32 as u32;
                let fresh45 = pool_ptr;
                pool_ptr = pool_ptr + 1;
                *str_pool.offset(fresh45 as isize) =
                    (0xd800_u32).wrapping_add(rval.wrapping_div(0x400_u32)) as packed_UTF16_code;
                let fresh46 = pool_ptr;
                pool_ptr = pool_ptr + 1;
                *str_pool.offset(fresh46 as isize) =
                    (0xdc00_u32).wrapping_add(rval.wrapping_rem(0x400_u32)) as packed_UTF16_code
            } else {
                let fresh47 = pool_ptr;
                pool_ptr = pool_ptr + 1;
                *str_pool.offset(fresh47 as isize) = rval as packed_UTF16_code
            }
            if rval == '/' as i32 as u32 {
                area_delimiter = cur_length();
                ext_delimiter = 0i32
            } else if rval == '.' as i32 as u32 {
                ext_delimiter = cur_length()
            }
        }
        stop_at_space = true;
        end_name();
        name_in_progress = false
    } else {
        /* Scan in the file name from the current token stream. The file name to
         * input is saved as the stringpool strings `cur_{name,area,ext}` and the
         * UTF-8 string `name_of_file`. */
        scan_file_name();
    }
    pack_file_name(cur_name, cur_area, cur_ext);
    /* Open up the new file to be read. The name of the file to be read comes
     * from `name_of_file`. */
    begin_file_reading();
    if u_open_in(
        &mut INPUT_FILE[cur_input.index as usize],
        format,
        b"rb\x00" as *const u8 as *const i8,
        EQTB[(INT_BASE + 77i32) as usize].b32.s1,
        EQTB[(INT_BASE + 78i32) as usize].b32.s1,
    ) == 0
    {
        abort!(
            "failed to open input file \"{}\"",
            CStr::from_ptr(name_of_file).display()
        );
    }
    /* Now re-encode `name_of_file` into the UTF-16 variable `name_of_file16`,
     * and use that to recompute `cur_{name,area,ext}`. */
    make_utf16_name();
    name_in_progress = true;
    begin_name();
    stop_at_space = false;
    let mut k: i32 = 0i32;
    while k < name_length16 && more_name(*name_of_file16.offset(k as isize)) as i32 != 0 {
        k += 1
    }
    stop_at_space = true;
    end_name();
    name_in_progress = false;
    /* Now generate a stringpool string corresponding to the full path of the
     * input file. This calls make_utf16_name() again and reruns through the
     * {begin,more,end}_name() trifecta to re-re-compute
     * `cur_{name,area,ext}`. */
    cur_input.name = make_name_string();
    SOURCE_FILENAME_STACK[IN_OPEN] = cur_input.name;
    /* *This* variant is a TeX string made out of `name_of_input_file`. */
    FULL_SOURCE_FILENAME_STACK[IN_OPEN] =
        maketexstring(CStr::from_ptr(name_of_input_file).to_bytes());
    if cur_input.name == str_ptr - 1i32 {
        temp_str = search_string(cur_input.name);
        if temp_str > 0i32 {
            cur_input.name = temp_str;
            str_ptr -= 1;
            pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize)
        }
    }
    /* Finally we start really doing stuff with the newly-opened file. */
    if job_name == 0i32 {
        job_name = cur_name; /* this is the "flush_string" macro which discards the most recent string */
        open_log_file(); /* "really a CFDictionaryRef or XeTeXLayoutEngine" */
    } /* = first_math_fontdimen (=10) + lastMathConstant (= radicalDegreeBottomRaisePercent = 55) */
    if term_offset + length(FULL_SOURCE_FILENAME_STACK[IN_OPEN]) > max_print_line - 2i32 {
        print_ln();
    } else if term_offset > 0i32 || file_offset > 0i32 {
        print_char(' ' as i32);
    }
    print_char('(' as i32);
    open_parens += 1;
    print(FULL_SOURCE_FILENAME_STACK[IN_OPEN]);
    rust_stdout.as_mut().unwrap().flush().unwrap();
    cur_input.state = 33_u16;
    synctex_start_input();
    line = 1i32;
    input_line(INPUT_FILE[cur_input.index as usize]);
    cur_input.limit = last;
    if EQTB[(INT_BASE + 48i32) as usize].b32.s1 < 0i32
        || EQTB[(INT_BASE + 48i32) as usize].b32.s1 > 255i32
    {
        cur_input.limit -= 1
    } else {
        *buffer.offset(cur_input.limit as isize) = EQTB[(INT_BASE + 48i32) as usize].b32.s1
    }
    first = cur_input.limit + 1i32;
    cur_input.loc = cur_input.start;
}
pub(crate) unsafe fn effective_char_info(mut f: internal_font_number, mut c: u16) -> b16x4 {
    if !xtx_ligature_present && !(FONT_MAPPING[f as usize]).is_null() {
        c = apply_tfm_font_mapping(FONT_MAPPING[f as usize], c as i32) as u16
    }
    xtx_ligature_present = false;
    FONT_INFO[(CHAR_BASE[f as usize] + c as i32) as usize].b16
}
pub(crate) unsafe fn char_warning(mut f: internal_font_number, mut c: i32) {
    let mut old_setting_0: i32 = 0;
    if EQTB[(INT_BASE + 35i32) as usize].b32.s1 > 0i32 {
        old_setting_0 = EQTB[(INT_BASE + 29i32) as usize].b32.s1;
        if EQTB[(INT_BASE + 35i32) as usize].b32.s1 > 1i32 {
            EQTB[(INT_BASE + 29i32) as usize].b32.s1 = 1i32
        }
        begin_diagnostic();
        print_nl_cstr(b"Missing character: There is no ");
        if (c as i64) < 65536 {
            print(c);
        } else {
            print_char(c);
        }
        print_cstr(b" in font ");
        print(FONT_NAME[f as usize]);
        print_char('!' as i32);
        end_diagnostic(false);
        EQTB[(INT_BASE + 29i32) as usize].b32.s1 = old_setting_0
    }
    let mut fn_0: *mut i8 = gettexstring(FONT_NAME[f as usize]);
    let mut chr: *mut i8 = 0 as *mut i8;
    let prev_selector = selector;
    let mut s: i32 = 0;
    selector = Selector::NEW_STRING;
    if c < 0x10000i32 {
        print(c);
    } else {
        print_char(c);
    }
    selector = prev_selector;
    s = make_string();
    chr = gettexstring(s);
    str_ptr -= 1;
    pool_ptr = *str_start.offset((str_ptr - 0x10000i32) as isize);
    ttstub_issue_warning(
        b"could not represent character \"%s\" in font \"%s\"\x00" as *const u8 as *const i8,
        chr,
        fn_0,
    );
    free(fn_0 as *mut libc::c_void);
    free(chr as *mut libc::c_void);
    if !gave_char_warning_help {
        ttstub_issue_warning(
            b"  you may need to load the `fontspec` package and use (e.g.) \\setmainfont to\x00"
                as *const u8 as *const i8,
        );
        ttstub_issue_warning(
            b"  choose a different font that covers the unrepresentable character(s)\x00"
                as *const u8 as *const i8,
        );
        gave_char_warning_help = true
    };
}
pub(crate) unsafe fn new_native_word_node(mut f: internal_font_number, mut n: i32) -> i32 {
    let mut l: i32 = 0;
    let mut q: i32 = 0;
    l = (6i32 as u64).wrapping_add(
        (n as u64)
            .wrapping_mul(::std::mem::size_of::<UTF16_code>() as u64)
            .wrapping_add(::std::mem::size_of::<memory_word>() as u64)
            .wrapping_sub(1i32 as u64)
            .wrapping_div(::std::mem::size_of::<memory_word>() as u64),
    ) as i32;
    q = get_node(l);
    MEM[q as usize].b16.s1 = 8_u16;
    if EQTB[(INT_BASE + 81i32) as usize].b32.s1 > 0i32 {
        MEM[q as usize].b16.s0 = 41_u16
    } else {
        MEM[q as usize].b16.s0 = 40_u16
    }
    MEM[(q + 4) as usize].b16.s3 = l as u16;
    MEM[(q + 4) as usize].b16.s2 = f as u16;
    MEM[(q + 4) as usize].b16.s1 = n as u16;
    MEM[(q + 4) as usize].b16.s0 = 0_u16;
    MEM[(q + 5) as usize].ptr = 0 as *mut libc::c_void;
    q
}
pub(crate) unsafe fn new_native_character(
    mut f: internal_font_number,
    mut c: UnicodeScalar,
) -> i32 {
    let mut p: i32 = 0;
    let mut i: i32 = 0;
    let mut len: i32 = 0;
    if !(FONT_MAPPING[f as usize]).is_null() {
        if c as i64 > 65535 {
            if pool_ptr + 2i32 > pool_size {
                overflow(b"pool size", pool_size - init_pool_ptr);
            }
            *str_pool.offset(pool_ptr as isize) =
                ((c as i64 - 65536) / 1024i32 as i64 + 0xd800i32 as i64) as packed_UTF16_code;
            pool_ptr += 1;
            *str_pool.offset(pool_ptr as isize) =
                ((c as i64 - 65536) % 1024i32 as i64 + 0xdc00i32 as i64) as packed_UTF16_code;
            pool_ptr += 1
        } else {
            if pool_ptr + 1i32 > pool_size {
                overflow(b"pool size", pool_size - init_pool_ptr);
            }
            *str_pool.offset(pool_ptr as isize) = c as packed_UTF16_code;
            pool_ptr += 1
        }
        len = apply_mapping(
            FONT_MAPPING[f as usize],
            &mut *str_pool.offset(*str_start.offset((str_ptr - 65536i32) as isize) as isize),
            cur_length(),
        );
        pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize);
        i = 0i32;
        while i < len {
            if *mapped_text.offset(i as isize) as i32 >= 0xd800i32
                && (*mapped_text.offset(i as isize) as i32) < 0xdc00i32
            {
                c = (*mapped_text.offset(i as isize) as i32 - 0xd800i32) * 1024i32
                    + *mapped_text.offset((i + 1i32) as isize) as i32
                    + 9216i32;
                if map_char_to_glyph(f, c) == 0i32 {
                    char_warning(f, c);
                }
                i += 2i32
            } else {
                if map_char_to_glyph(f, *mapped_text.offset(i as isize) as i32) == 0i32 {
                    char_warning(f, *mapped_text.offset(i as isize) as i32);
                }
                i += 1i32
            }
        }
        p = new_native_word_node(f, len);
        i = 0i32;
        while i <= len - 1i32 {
            *(&mut MEM[(p + 6) as usize] as *mut memory_word as *mut u16).offset(i as isize) =
                *mapped_text.offset(i as isize);
            i += 1
        }
    } else {
        if EQTB[(INT_BASE + 35i32) as usize].b32.s1 > 0i32 {
            if map_char_to_glyph(f, c) == 0i32 {
                char_warning(f, c);
            }
        }
        p = get_node(6i32 + 1i32);
        MEM[p as usize].b16.s1 = 8_u16;
        MEM[p as usize].b16.s0 = 40_u16;
        MEM[(p + 4) as usize].b16.s3 = (6 + 1) as u16;
        MEM[(p + 4) as usize].b16.s0 = 0_u16;
        MEM[(p + 5) as usize].ptr = 0 as *mut libc::c_void;
        MEM[(p + 4) as usize].b16.s2 = f as u16;
        if c as i64 > 65535 {
            MEM[(p + 4) as usize].b16.s1 = 2_u16;
            *(&mut MEM[(p + 6) as usize] as *mut memory_word as *mut u16).offset(0) =
                ((c as i64 - 65536) / 1024i32 as i64 + 0xd800i32 as i64) as u16;
            *(&mut MEM[(p + 6) as usize] as *mut memory_word as *mut u16).offset(1) =
                ((c as i64 - 65536) % 1024i32 as i64 + 0xdc00i32 as i64) as u16
        } else {
            MEM[(p + 4) as usize].b16.s1 = 1_u16;
            *(&mut MEM[(p + 6) as usize] as *mut memory_word as *mut u16).offset(0) = c as u16
        }
    }
    measure_native_node(
        &mut MEM[p as usize] as *mut memory_word as *mut libc::c_void,
        (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
    );
    p
}
pub(crate) unsafe fn font_feature_warning(
    mut featureNameP: *const libc::c_void,
    mut featLen: i32,
    mut settingNameP: *const libc::c_void,
    mut setLen: i32,
) {
    begin_diagnostic();
    print_nl_cstr(b"Unknown ");
    if setLen > 0i32 {
        print_cstr(b"selector `");
        print_utf8_str(settingNameP as *const u8, setLen);
        print_cstr(b"\' for ");
    }
    print_cstr(b"feature `");
    print_utf8_str(featureNameP as *const u8, featLen);
    print_cstr(b"\' in font `");
    let mut i: i32 = 0i32;
    while *name_of_file.offset(i as isize) as i32 != 0i32 {
        print_raw_char(*name_of_file.offset(i as isize) as UTF16_code, true);
        i += 1
    }
    print_cstr(b"\'.");
    end_diagnostic(false);
}
pub(crate) unsafe fn font_mapping_warning(
    mut mappingNameP: *const libc::c_void,
    mut mappingNameLen: i32,
    mut warningType: i32,
) {
    begin_diagnostic();
    if warningType == 0i32 {
        print_nl_cstr(b"Loaded mapping `");
    } else {
        print_nl_cstr(b"Font mapping `");
    }
    print_utf8_str(mappingNameP as *const u8, mappingNameLen);
    print_cstr(b"\' for font `");
    let mut i: i32 = 0i32;
    while *name_of_file.offset(i as isize) as i32 != 0i32 {
        print_raw_char(*name_of_file.offset(i as isize) as UTF16_code, true);
        i += 1
    }
    match warningType {
        1 => print_cstr(b"\' not found."),
        2 => {
            print_cstr(b"\' not usable;");
            print_nl_cstr(b"bad mapping file or incorrect mapping type.");
        }
        _ => print_cstr(b"\'."),
    }
    end_diagnostic(false);
}
pub(crate) unsafe fn graphite_warning() {
    begin_diagnostic();
    print_nl_cstr(b"Font `");
    let mut i: i32 = 0i32;
    while *name_of_file.offset(i as isize) as i32 != 0i32 {
        print_raw_char(*name_of_file.offset(i as isize) as UTF16_code, true);
        i += 1
    }
    print_cstr(b"\' does not support Graphite. Trying OpenType layout instead.");
    end_diagnostic(false);
}
pub(crate) unsafe fn load_native_font(
    mut u: i32,
    mut nom: str_number,
    mut aire: str_number,
    mut s: scaled_t,
) -> internal_font_number {
    let mut k: i32 = 0;
    let mut num_font_dimens: i32 = 0;
    let mut font_engine: *mut libc::c_void = 0 as *mut libc::c_void;
    let mut actual_size: scaled_t = 0;
    let mut p: i32 = 0;
    let mut ascent: scaled_t = 0;
    let mut descent: scaled_t = 0;
    let mut font_slant: scaled_t = 0;
    let mut x_ht: scaled_t = 0;
    let mut cap_ht: scaled_t = 0;
    let mut f: internal_font_number = 0;
    let mut full_name: str_number = 0;
    font_engine = find_native_font(name_of_file, s);
    if font_engine.is_null() {
        return 0i32;
    }
    if s >= 0i32 {
        actual_size = s
    } else if s != -1000i32 {
        actual_size = xn_over_d(loaded_font_design_size, -s, 1000i32)
    } else {
        actual_size = loaded_font_design_size
    }
    if pool_ptr + name_length > pool_size {
        overflow(b"pool size", pool_size - init_pool_ptr);
    }
    k = 0i32;
    while k < name_length {
        let fresh50 = pool_ptr;
        pool_ptr = pool_ptr + 1;
        *str_pool.offset(fresh50 as isize) = *name_of_file.offset(k as isize) as packed_UTF16_code;
        k += 1
    }
    full_name = make_string();
    f = 0i32 + 1i32;
    while f <= font_ptr {
        if FONT_AREA[f as usize] == native_font_type_flag
            && str_eq_str(FONT_NAME[f as usize], full_name) as i32 != 0
            && FONT_SIZE[f as usize] == actual_size
        {
            release_font_engine(font_engine, native_font_type_flag);
            str_ptr -= 1;
            pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize);
            return f;
        }
        f += 1
    }
    if native_font_type_flag as u32 == 0xfffeu32
        && isOpenTypeMathFont(font_engine as XeTeXLayoutEngine) as i32 != 0
    {
        num_font_dimens = 65i32
    } else {
        num_font_dimens = 8i32
    }
    if font_ptr == FONT_MAX as i32 || fmem_ptr + num_font_dimens > FONT_MEM_SIZE as i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Font ");
        sprint_cs(u);
        print_char('=' as i32);
        if file_name_quote_char as i32 != 0i32 {
            print_char(file_name_quote_char as i32);
        }
        print_file_name(nom, aire, cur_ext);
        if file_name_quote_char as i32 != 0i32 {
            print_char(file_name_quote_char as i32);
        }
        if s >= 0i32 {
            print_cstr(b" at ");
            print_scaled(s);
            print_cstr(b"pt");
        } else if s != -1000i32 {
            print_cstr(b" scaled ");
            print_int(-s);
        }
        print_cstr(b" not loaded: Not enough room left");
        help_ptr = 4_u8;
        help_line[3] = b"I\'m afraid I won\'t be able to make use of this font,";
        help_line[2] = b"because my memory for character-size data is too small.";
        help_line[1] = b"If you\'re really stuck, ask a wizard to enlarge me.";
        help_line[0] = b"Or maybe try `I\\font<same font id>=<name of loaded font>\'.";
        error();
        return 0i32;
    }
    font_ptr += 1;
    FONT_AREA[font_ptr as usize] = native_font_type_flag;
    FONT_NAME[font_ptr as usize] = full_name;
    FONT_CHECK[font_ptr as usize].s3 = 0_u16;
    FONT_CHECK[font_ptr as usize].s2 = 0_u16;
    FONT_CHECK[font_ptr as usize].s1 = 0_u16;
    FONT_CHECK[font_ptr as usize].s0 = 0_u16;
    FONT_GLUE[font_ptr as usize] = TEX_NULL;
    FONT_DSIZE[font_ptr as usize] = loaded_font_design_size;
    FONT_SIZE[font_ptr as usize] = actual_size;
    match native_font_type_flag as u32 {
        #[cfg(target_os = "macos")]
        0xffffu32 => {
            aat::aat_get_font_metrics(
                font_engine as _,
                &mut ascent,
                &mut descent,
                &mut x_ht,
                &mut cap_ht,
                &mut font_slant,
            );
        }
        #[cfg(not(target_os = "macos"))]
        0xffffu32 => {
            // do nothing
        }
        _ => {
            ot_get_font_metrics(
                font_engine,
                &mut ascent,
                &mut descent,
                &mut x_ht,
                &mut cap_ht,
                &mut font_slant,
            );
        }
    }
    HEIGHT_BASE[font_ptr as usize] = ascent;
    DEPTH_BASE[font_ptr as usize] = -descent;
    FONT_PARAMS[font_ptr as usize] = num_font_dimens;
    FONT_BC[font_ptr as usize] = 0 as UTF16_code;
    FONT_EC[font_ptr as usize] = 65535 as UTF16_code;
    *font_used.offset(font_ptr as isize) = false;
    HYPHEN_CHAR[font_ptr as usize] = EQTB[(INT_BASE + 46i32) as usize].b32.s1;
    SKEW_CHAR[font_ptr as usize] = EQTB[(INT_BASE + 47i32) as usize].b32.s1;
    PARAM_BASE[font_ptr as usize] = fmem_ptr - 1i32;
    FONT_LAYOUT_ENGINE[font_ptr as usize] = font_engine;
    FONT_MAPPING[font_ptr as usize] = 0 as *mut libc::c_void;
    FONT_LETTER_SPACE[font_ptr as usize] = loaded_font_letter_space;
    /* "measure the width of the space character and set up font parameters" */
    p = new_native_character(font_ptr, ' ' as i32); /* space_stretch */
    s = MEM[(p + 1) as usize].b32.s1 + loaded_font_letter_space; /* space_shrink */
    free_node(p, MEM[(p + 4) as usize].b16.s3 as i32); /* quad */
    let fresh53 = fmem_ptr; /* extra_space */
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh53 as usize].b32.s1 = font_slant;
    let fresh54 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh54 as usize].b32.s1 = s;
    let fresh55 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh55 as usize].b32.s1 = s / 2;
    let fresh56 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh56 as usize].b32.s1 = s / 3;
    let fresh57 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh57 as usize].b32.s1 = x_ht;
    let fresh58 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh58 as usize].b32.s1 = FONT_SIZE[font_ptr as usize];
    let fresh59 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh59 as usize].b32.s1 = s / 3;
    let fresh60 = fmem_ptr;
    fmem_ptr = fmem_ptr + 1;
    FONT_INFO[fresh60 as usize].b32.s1 = cap_ht;
    if num_font_dimens == 65i32 {
        let fresh61 = fmem_ptr;
        fmem_ptr = fmem_ptr + 1;
        FONT_INFO[fresh61 as usize].b32.s1 = num_font_dimens;
        k = 0i32;
        while k <= 55i32 {
            /* 55 = lastMathConstant */
            let fresh62 = fmem_ptr; /*:582*/
            fmem_ptr = fmem_ptr + 1;
            FONT_INFO[fresh62 as usize].b32.s1 = get_ot_math_constant(font_ptr, k);
            k += 1
        }
    }
    FONT_MAPPING[font_ptr as usize] = loaded_font_mapping;
    FONT_FLAGS[font_ptr as usize] = loaded_font_flags;
    font_ptr
}
pub(crate) unsafe fn do_locale_linebreaks(mut s: i32, mut len: i32) {
    let mut offs: i32 = 0;
    let mut prevOffs: i32 = 0;
    let mut i: i32 = 0;
    let mut use_penalty: bool = false;
    let mut use_skip: bool = false;
    if EQTB[(INT_BASE + 68i32) as usize].b32.s1 == 0i32 || len == 1i32 {
        MEM[cur_list.tail as usize].b32.s1 = new_native_word_node(main_f, len);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        let mut for_end: i32 = 0;
        i = 0i32;
        for_end = len - 1i32;
        if i <= for_end {
            loop {
                *(&mut MEM[(cur_list.tail + 6) as usize] as *mut memory_word as *mut u16)
                    .offset(i as isize) = *native_text.offset((s + i) as isize);
                let fresh64 = i;
                i = i + 1;
                if !(fresh64 < for_end) {
                    break;
                }
            }
        }
        measure_native_node(
            &mut MEM[cur_list.tail as usize] as *mut memory_word as *mut libc::c_void,
            (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
        );
    } else {
        use_skip = EQTB[(GLUE_BASE + 15i32) as usize].b32.s1 != 0i32;
        use_penalty = EQTB[(INT_BASE + 69i32) as usize].b32.s1 != 0i32 || !use_skip;
        linebreak_start(
            main_f,
            EQTB[(INT_BASE + 68i32) as usize].b32.s1,
            native_text.offset(s as isize),
            len,
        );
        offs = 0i32;
        loop {
            prevOffs = offs;
            offs = linebreak_next();
            if offs > 0i32 {
                if prevOffs != 0i32 {
                    if use_penalty {
                        MEM[cur_list.tail as usize].b32.s1 =
                            new_penalty(EQTB[(INT_BASE + 69i32) as usize].b32.s1);
                        cur_list.tail = MEM[cur_list.tail as usize].b32.s1
                    }
                    if use_skip {
                        MEM[cur_list.tail as usize].b32.s1 = new_param_glue(15 as small_number);
                        cur_list.tail = MEM[cur_list.tail as usize].b32.s1
                    }
                }
                MEM[cur_list.tail as usize].b32.s1 = new_native_word_node(main_f, offs - prevOffs);
                cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                let mut for_end_0: i32 = 0;
                i = prevOffs;
                for_end_0 = offs - 1i32;
                if i <= for_end_0 {
                    loop {
                        *(&mut MEM[(cur_list.tail + 6) as usize] as *mut memory_word as *mut u16)
                            .offset((i - prevOffs) as isize) =
                            *native_text.offset((s + i) as isize);
                        let fresh65 = i;
                        i = i + 1;
                        if !(fresh65 < for_end_0) {
                            break;
                        }
                    }
                }
                measure_native_node(
                    &mut MEM[cur_list.tail as usize] as *mut memory_word as *mut libc::c_void,
                    (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
                );
            }
            if offs < 0i32 {
                break;
            }
        }
    };
}
pub(crate) unsafe fn bad_utf8_warning() {
    begin_diagnostic();
    print_nl_cstr(b"Invalid UTF-8 byte or sequence");
    if cur_input.name == 0i32 {
        print_cstr(b" in terminal input");
    } else {
        print_cstr(b" at line ");
        print_int(line);
    }
    print_cstr(b" replaced by U+FFFD.");
    end_diagnostic(false);
}
pub(crate) unsafe fn get_input_normalization_state() -> i32 {
    if EQTB.is_empty() {
        0
    } else {
        EQTB[(INT_BASE + 76i32) as usize].b32.s1
    }
}
pub(crate) unsafe fn get_tracing_fonts_state() -> i32 {
    EQTB[(INT_BASE + 79i32) as usize].b32.s1
}
pub(crate) unsafe fn read_font_info(
    mut u: i32,
    mut nom: str_number,
    mut aire: str_number,
    mut s: scaled_t,
) -> internal_font_number {
    let mut k: font_index = 0;
    let mut name_too_long: bool = false;
    let mut lf: i32 = 0;
    let mut lh: i32 = 0;
    let mut bc: i32 = 0;
    let mut ec: i32 = 0;
    let mut nw: i32 = 0;
    let mut nh: i32 = 0;
    let mut nd: i32 = 0;
    let mut ni: i32 = 0;
    let mut nl: i32 = 0;
    let mut nk: i32 = 0;
    let mut ne: i32 = 0;
    let mut np: i32 = 0;
    let mut f: internal_font_number = 0;
    let mut g: internal_font_number = 0;
    let mut a: i32 = 0;
    let mut b: i32 = 0;
    let mut c: i32 = 0;
    let mut d: i32 = 0;
    let mut qw: b16x4 = b16x4 {
        s0: 0,
        s1: 0,
        s2: 0,
        s3: 0,
    };
    let mut sw: scaled_t = 0;
    let mut bch_label: i32 = 0;
    let mut bchar_0: i16 = 0;
    let mut z: scaled_t = 0;
    let mut alpha: i32 = 0;
    let mut beta: u8 = 0;

    g = FONT_BASE;

    pack_file_name(nom, aire, cur_ext);

    if INTPAR(INT_PAR__xetex_tracing_fonts) > 0 {
        begin_diagnostic();
        print_nl_cstr(b"Requested font \"");
        print_c_string(name_of_file);
        print('\"' as i32);
        if s < 0 {
            print_cstr(b" scaled ");
            print_int(-s);
        } else {
            print_cstr(b" at ");
            print_scaled(s);
            print_cstr(b"pt");
        }
        end_diagnostic(false);
    }

    if quoted_filename {
        g = load_native_font(u, nom, aire, s);
        if g != FONT_BASE {
            return done(None, g);
        }
    }

    name_too_long = length(nom) > 255i32 || length(aire) > 255i32;
    if name_too_long {
        return bad_tfm(None, g, u, nom, aire, s, name_too_long);
    }
    pack_file_name(nom, aire, (65536 + 1i32 as i64) as str_number);
    check_for_tfm_font_mapping();

    let mut tfm_file_owner = tt_xetex_open_input(TTInputFormat::TFM);
    if tfm_file_owner.is_none() {
        if !quoted_filename {
            g = load_native_font(u, nom, aire, s);
            if g != FONT_BASE {
                return done(None, g);
            }
        }
        return bad_tfm(None, g, u, nom, aire, s, name_too_long);
    }

    let tfm_file = tfm_file_owner.as_mut().unwrap();

    /* We are a bit cavalier about EOF-checking since we can't very
     * conveniently implement feof() in the Rust layer, and it only ever is
     * used in this one place. */

    macro_rules! READFIFTEEN (
        ($x:expr) => {
            $x = ttstub_input_getc(tfm_file);
            if $x > 127 || $x == libc::EOF {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            $x *= 256;
            $x += ttstub_input_getc(tfm_file);

        };
    );

    READFIFTEEN!(lf);
    READFIFTEEN!(lh);
    READFIFTEEN!(bc);
    READFIFTEEN!(ec);

    if bc > ec + 1 || ec > 255 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    if bc > 255 {
        bc = 1;
        ec = 0
    }

    READFIFTEEN!(nw);
    READFIFTEEN!(nh);
    READFIFTEEN!(nd);
    READFIFTEEN!(ni);
    READFIFTEEN!(nl);
    READFIFTEEN!(nk);
    READFIFTEEN!(ne);
    READFIFTEEN!(np);

    if lf != 6 + lh + (ec - bc + 1) + nw + nh + nd + ni + nl + nk + ne + np {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    } else if nw == 0 || nh == 0 || nd == 0 || ni == 0 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }

    lf = lf - 6 - lh;
    if np < 7 {
        lf = lf + 7 - np
    }
    assert!(
        !(font_ptr == FONT_MAX as i32 || fmem_ptr + lf > FONT_MEM_SIZE as i32),
        "not enough memory to load another font"
    );

    f = font_ptr + 1;
    CHAR_BASE[f as usize] = fmem_ptr - bc;
    WIDTH_BASE[f as usize] = CHAR_BASE[f as usize] + ec + 1;
    HEIGHT_BASE[f as usize] = WIDTH_BASE[f as usize] + nw;
    DEPTH_BASE[f as usize] = HEIGHT_BASE[f as usize] + nh;
    ITALIC_BASE[f as usize] = DEPTH_BASE[f as usize] + nd;
    LIG_KERN_BASE[f as usize] = ITALIC_BASE[f as usize] + ni;
    KERN_BASE[f as usize] = LIG_KERN_BASE[f as usize] + nl - 256 * 128;
    EXTEN_BASE[f as usize] = KERN_BASE[f as usize] + 256 * 128 + nk;
    PARAM_BASE[f as usize] = EXTEN_BASE[f as usize] + ne;
    if lh < 2 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    a = ttstub_input_getc(tfm_file);
    qw.s3 = a as u16;
    b = ttstub_input_getc(tfm_file);
    qw.s2 = b as u16;
    c = ttstub_input_getc(tfm_file);
    qw.s1 = c as u16;
    d = ttstub_input_getc(tfm_file);
    qw.s0 = d as u16;
    if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    FONT_CHECK[f as usize] = qw;

    READFIFTEEN!(z);
    z = z * 256 + ttstub_input_getc(tfm_file);
    z = z * 16 + ttstub_input_getc(tfm_file) / 16;
    if z < 65536 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    while lh > 2 {
        ttstub_input_getc(tfm_file);
        ttstub_input_getc(tfm_file);
        ttstub_input_getc(tfm_file);
        ttstub_input_getc(tfm_file);
        lh -= 1
    }
    FONT_DSIZE[f as usize] = z;
    if s != -1000 {
        if s >= 0 {
            z = s
        } else {
            z = xn_over_d(z, -s, 1000)
        }
    }
    FONT_SIZE[f as usize] = z;

    k = fmem_ptr;
    loop {
        if !(k <= WIDTH_BASE[f as usize] - 1i32) {
            break;
        }
        a = ttstub_input_getc(tfm_file);
        qw.s3 = a as u16;
        b = ttstub_input_getc(tfm_file);
        qw.s2 = b as u16;
        c = ttstub_input_getc(tfm_file);
        qw.s1 = c as u16;
        d = ttstub_input_getc(tfm_file);
        qw.s0 = d as u16;
        if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
        FONT_INFO[k as usize].b16 = qw;

        if a >= nw || b / 16 >= nh || b % 16 >= nd || c / 4 >= ni {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }

        match c % 4 {
            1 => {
                if d >= nl {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
            }
            3 => {
                if d >= ne {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
            }
            2 => {
                if d < bc || d > ec {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
                loop {
                    if !(d < k + bc - fmem_ptr) {
                        break;
                    }
                    qw = FONT_INFO[(CHAR_BASE[f as usize] + d) as usize].b16;
                    if qw.s1 as i32 % 4 != LIST_TAG {
                        break;
                    }
                    d = qw.s0 as i32
                }
                if d == k + bc - fmem_ptr {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
            }
            _ => {}
        }
        k += 1
    }

    alpha = 16;
    while z >= 0x800000 {
        z = z / 2;
        alpha = alpha + alpha
    }
    beta = (256 / alpha) as u8;
    alpha = alpha * z;

    for k in WIDTH_BASE[f as usize]..=LIG_KERN_BASE[f as usize] - 1 {
        a = ttstub_input_getc(tfm_file);
        b = ttstub_input_getc(tfm_file);
        c = ttstub_input_getc(tfm_file);
        d = ttstub_input_getc(tfm_file);
        if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
        sw = ((d * z / 256 + c * z) / 256 + b * z) / beta as i32;

        if a == 0 {
            FONT_INFO[k as usize].b32.s1 = sw
        } else if a == 255 {
            FONT_INFO[k as usize].b32.s1 = sw - alpha
        } else {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
    }

    if FONT_INFO[WIDTH_BASE[f as usize] as usize].b32.s1 != 0 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    if FONT_INFO[HEIGHT_BASE[f as usize] as usize].b32.s1 != 0 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    if FONT_INFO[DEPTH_BASE[f as usize] as usize].b32.s1 != 0 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }
    if FONT_INFO[ITALIC_BASE[f as usize] as usize].b32.s1 != 0 {
        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
    }

    bch_label = 32767;
    bchar_0 = 256;
    if nl > 0 {
        for k in LIG_KERN_BASE[f as usize]..=KERN_BASE[f as usize] + 256 * 128 - 1 {
            a = ttstub_input_getc(tfm_file);
            qw.s3 = a as u16;
            b = ttstub_input_getc(tfm_file);
            qw.s2 = b as u16;
            c = ttstub_input_getc(tfm_file);
            qw.s1 = c as u16;
            d = ttstub_input_getc(tfm_file);
            qw.s0 = d as u16;
            if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            FONT_INFO[k as usize].b16 = qw;

            if a > 128 {
                if 256 * c + d >= nl {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
                if a == 255 && k == LIG_KERN_BASE[f as usize] {
                    bchar_0 = b as i16
                }
            } else {
                if b != bchar_0 as i32 {
                    if b < bc || b > ec {
                        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                    }

                    qw = FONT_INFO[(CHAR_BASE[f as usize] + b) as usize].b16;
                    if !(qw.s3 > 0) {
                        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                    }
                }

                if c < 128 {
                    if d < bc || d > ec {
                        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                    }
                    qw = FONT_INFO[(CHAR_BASE[f as usize] + d) as usize].b16;
                    if !(qw.s3 > 0) {
                        return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                    }
                } else if 256 * (c - 128) + d >= nk {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
                if a < 128 && k - LIG_KERN_BASE[f as usize] + a + 1i32 >= nl {
                    return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
                }
            }
        }
        if a == 255 {
            bch_label = 256 * c + d
        }
    }

    for k in KERN_BASE[f as usize] + 256 * 128..=EXTEN_BASE[f as usize] - 1 {
        a = ttstub_input_getc(tfm_file);
        b = ttstub_input_getc(tfm_file);
        c = ttstub_input_getc(tfm_file);
        d = ttstub_input_getc(tfm_file);
        if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
        sw = ((d * z / 256i32 + c * z) / 256i32 + b * z) / beta as i32;
        if a == 0 {
            FONT_INFO[k as usize].b32.s1 = sw
        } else if a == 255 {
            FONT_INFO[k as usize].b32.s1 = sw - alpha
        } else {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
    }

    for k in EXTEN_BASE[f as usize]..=PARAM_BASE[f as usize] - 1 {
        a = ttstub_input_getc(tfm_file);
        qw.s3 = a as u16;
        b = ttstub_input_getc(tfm_file);
        qw.s2 = b as u16;
        c = ttstub_input_getc(tfm_file);
        qw.s1 = c as u16;
        d = ttstub_input_getc(tfm_file);
        qw.s0 = d as u16;
        if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
        FONT_INFO[k as usize].b16 = qw;

        if a != 0 {
            if a < bc || a > ec {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            qw = FONT_INFO[(CHAR_BASE[f as usize] + a) as usize].b16;
            if !(qw.s3 as i32 > 0i32) {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
        }

        if b != 0 {
            if b < bc || b > ec {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            qw = FONT_INFO[(CHAR_BASE[f as usize] + b) as usize].b16;
            if !(qw.s3 > 0) {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
        }

        if c != 0 {
            if c < bc || c > ec {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            qw = FONT_INFO[(CHAR_BASE[f as usize] + c) as usize].b16;
            if !(qw.s3 > 0) {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
        }

        if d < bc || d > ec {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
        qw = FONT_INFO[(CHAR_BASE[f as usize] + d) as usize].b16;
        if !(qw.s3 > 0) {
            return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
        }
    }

    for k in 1..=np {
        if k == 1 {
            sw = ttstub_input_getc(tfm_file);
            if sw == libc::EOF {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            if sw > 127 {
                sw = sw - 256
            }

            sw = sw * 256 + ttstub_input_getc(tfm_file);
            sw = sw * 256 + ttstub_input_getc(tfm_file);
            FONT_INFO[PARAM_BASE[f as usize] as usize].b32.s1 =
                sw * 16 + ttstub_input_getc(tfm_file) / 16
        } else {
            a = ttstub_input_getc(tfm_file);
            b = ttstub_input_getc(tfm_file);
            c = ttstub_input_getc(tfm_file);
            d = ttstub_input_getc(tfm_file);
            if a == libc::EOF || b == libc::EOF || c == libc::EOF || d == libc::EOF {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
            sw = ((d * z / 256i32 + c * z) / 256i32 + b * z) / beta as i32;
            if a == 0 {
                FONT_INFO[(PARAM_BASE[f as usize] + k - 1i32) as usize]
                    .b32
                    .s1 = sw
            } else if a == 255 {
                FONT_INFO[(PARAM_BASE[f as usize] + k - 1i32) as usize]
                    .b32
                    .s1 = sw - alpha
            } else {
                return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);
            }
        }
    }

    for k in np + 1..=7 {
        FONT_INFO[(PARAM_BASE[f as usize] + k - 1i32) as usize]
            .b32
            .s1 = 0;
    }

    if np >= 7 {
        FONT_PARAMS[f as usize] = np
    } else {
        FONT_PARAMS[f as usize] = 7
    }

    HYPHEN_CHAR[f as usize] = INTPAR(INT_PAR__default_hyphen_char);
    SKEW_CHAR[f as usize] = INTPAR(INT_PAR__default_skew_char);
    if bch_label < nl {
        BCHAR_LABEL[f as usize] = bch_label + LIG_KERN_BASE[f as usize]
    } else {
        BCHAR_LABEL[f as usize] = NON_ADDRESS;
    }
    FONT_BCHAR[f as usize] = bchar_0 as _;
    FONT_FALSE_BCHAR[f as usize] = bchar_0 as nine_bits;

    if bchar_0 as i32 <= ec {
        if bchar_0 as i32 >= bc {
            qw = FONT_INFO[(CHAR_BASE[f as usize] + bchar_0 as i32) as usize].b16;
            if qw.s3 as i32 > 0i32 {
                FONT_FALSE_BCHAR[f as usize] = 65536
            }
        }
    }

    FONT_NAME[f as usize] = nom;
    FONT_AREA[f as usize] = aire;
    FONT_BC[f as usize] = bc as UTF16_code;
    FONT_EC[f as usize] = ec as UTF16_code;
    FONT_GLUE[f as usize] = TEX_NULL;
    PARAM_BASE[f as usize] -= 1;
    fmem_ptr = fmem_ptr + lf;
    font_ptr = f;
    g = f;
    FONT_MAPPING[f as usize] = load_tfm_font_mapping();

    return done(tfm_file_owner, g);

    /// Called on error
    unsafe fn bad_tfm(
        tfm_file: Option<InputHandleWrapper>,
        g: i32,
        u: i32,
        nom: i32,
        aire: i32,
        s: i32,
        name_too_long: bool,
    ) -> i32 {
        if INTPAR(INT_PAR__suppress_fontnotfound_error) == 0 {
            /* NOTE: must preserve this path to keep passing the TRIP tests */
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Font ");
            sprint_cs(u);
            print_char('=' as i32);
            if file_name_quote_char as i32 != 0i32 {
                print_char(file_name_quote_char as i32);
            }
            print_file_name(nom, aire, cur_ext);
            if file_name_quote_char as i32 != 0i32 {
                print_char(file_name_quote_char as i32);
            }
            if s >= 0 {
                print_cstr(b" at ");
                print_scaled(s);
                print_cstr(b"pt");
            } else if s != -1000 {
                print_cstr(b" scaled ");
                print_int(-s);
            }
            if tfm_file.is_some() {
                print_cstr(b" not loadable: Bad metric (TFM) file");
            } else if name_too_long {
                print_cstr(b" not loadable: Metric (TFM) file name too long");
            } else {
                print_cstr(b" not loadable: Metric (TFM) file or installed font not found");
            }
            help_ptr = 5_u8;
            help_line[4] = b"I wasn\'t able to read the size data for this font,";
            help_line[3] = b"so I will ignore the font specification.";
            help_line[2] = b"[Wizards can fix TFM files using TFtoPL/PLtoTF.]";
            help_line[1] = b"You might try inserting a different font spec;";
            help_line[0] = b"e.g., type `I\\font<same font id>=<substitute font name>\'.";
            error();
        }
        return done(tfm_file, g);
    }
    // unreachable
    // return bad_tfm(tfm_file_owner, g, u, nom, aire, s, name_too_long);

    unsafe fn done(tfm_file: Option<InputHandleWrapper>, g: i32) -> i32 {
        let file_opened = tfm_file.is_some();
        if let Some(handle) = tfm_file {
            ttstub_input_close(handle);
        }

        if INTPAR(INT_PAR__xetex_tracing_fonts) > 0 {
            if g == FONT_BASE {
                begin_diagnostic();
                print_nl_cstr(b" -> font not found, using \"nullfont\"");
                end_diagnostic(false);
            } else if file_opened {
                begin_diagnostic();
                print_nl_cstr(b" -> ");
                print_c_string(name_of_file);
                end_diagnostic(false);
            }
        }
        g
    }
    // unreachable
    // return done(tfm_file_owner, g);
}
pub(crate) unsafe fn new_character(mut f: internal_font_number, mut c: UTF16_code) -> i32 {
    let mut p: i32 = 0;
    let mut ec: u16 = 0;
    if FONT_AREA[f as usize] as u32 == 0xffffu32 || FONT_AREA[f as usize] as u32 == 0xfffeu32 {
        return new_native_character(f, c as UnicodeScalar);
    }
    ec = effective_char(false, f, c) as u16;
    if FONT_BC[f as usize] as i32 <= ec as i32 {
        if FONT_EC[f as usize] as i32 >= ec as i32 {
            if FONT_INFO[(CHAR_BASE[f as usize] + ec as i32) as usize]
                .b16
                .s3 as i32
                > 0i32
            {
                p = get_avail();
                MEM[p as usize].b16.s1 = f as u16;
                MEM[p as usize].b16.s0 = c;
                return p;
            }
        }
    }
    char_warning(f, c as i32);
    TEX_NULL
}
pub(crate) unsafe fn scan_spec(mut c: group_code, mut three_codes: bool) {
    let mut current_block: u64;
    let mut s: i32 = 0;
    let mut spec_code: u8 = 0;
    if three_codes {
        s = SAVE_STACK[SAVE_PTR + 0].b32.s1
    }
    if scan_keyword(b"to") {
        spec_code = 0_u8;
        current_block = 8515828400728868193;
    } else if scan_keyword(b"spread") {
        spec_code = 1_u8;
        current_block = 8515828400728868193;
    } else {
        spec_code = 1_u8;
        cur_val = 0i32;
        current_block = 4427475217998452135;
    }
    match current_block {
        8515828400728868193 => scan_dimen(false, false, false),
        _ => {}
    }
    if three_codes {
        SAVE_STACK[SAVE_PTR + 0].b32.s1 = s;
        SAVE_PTR += 1;
    }
    SAVE_STACK[SAVE_PTR + 0].b32.s1 = spec_code as i32;
    SAVE_STACK[SAVE_PTR + 1].b32.s1 = cur_val;
    SAVE_PTR += 2;
    new_save_level(c);
    scan_left_brace();
}
pub(crate) unsafe fn char_pw(mut p: i32, mut side: small_number) -> scaled_t {
    let mut f: internal_font_number = 0;
    let mut c: i32 = 0;
    if side as i32 == 0i32 {
        last_leftmost_char = TEX_NULL
    } else {
        last_rightmost_char = TEX_NULL
    }
    if p == TEX_NULL {
        return 0i32;
    }
    if p != TEX_NULL
        && !is_char_node(p)
        && MEM[p as usize].b16.s1 as i32 == 8
        && (MEM[p as usize].b16.s0 as i32 == 40 || MEM[p as usize].b16.s0 as i32 == 41)
    {
        if !MEM[(p + 5) as usize].ptr.is_null() {
            f = MEM[(p + 4) as usize].b16.s2 as internal_font_number;
            return round_xn_over_d(
                FONT_INFO[(6 + PARAM_BASE[f as usize]) as usize].b32.s1,
                real_get_native_word_cp(
                    &mut MEM[p as usize] as *mut memory_word as *mut libc::c_void,
                    side as i32,
                ),
                1000i32,
            );
        } else {
            return 0i32;
        }
    }
    if p != TEX_NULL
        && !is_char_node(p)
        && MEM[p as usize].b16.s1 as i32 == 8
        && MEM[p as usize].b16.s0 as i32 == 42
    {
        f = MEM[(p + 4) as usize].b16.s2 as internal_font_number;
        return round_xn_over_d(
            FONT_INFO[(6 + PARAM_BASE[f as usize]) as usize].b32.s1,
            get_cp_code(f, MEM[(p + 4) as usize].b16.s1 as u32, side as i32),
            1000i32,
        );
    }
    if !is_char_node(p) {
        if MEM[p as usize].b16.s1 as i32 == 6 {
            p = p + 1i32
        } else {
            return 0i32;
        }
    }
    f = MEM[p as usize].b16.s1 as internal_font_number;
    c = get_cp_code(f, MEM[p as usize].b16.s0 as u32, side as i32);
    match side as i32 {
        0 => last_leftmost_char = p,
        1 => last_rightmost_char = p,
        _ => {}
    }
    if c == 0i32 {
        return 0i32;
    }
    round_xn_over_d(
        FONT_INFO[(6 + PARAM_BASE[f as usize]) as usize].b32.s1,
        c,
        1000i32,
    )
}
pub(crate) unsafe fn new_margin_kern(mut w: scaled_t, mut _p: i32, mut side: small_number) -> i32 {
    let mut k: i32 = 0;
    k = get_node(3i32);
    MEM[k as usize].b16.s1 = 40_u16;
    MEM[k as usize].b16.s0 = side as u16;
    MEM[(k + 1) as usize].b32.s1 = w;
    k
}
pub(crate) unsafe fn hpack(mut p: i32, mut w: scaled_t, mut m: small_number) -> i32 {
    let mut current_block: u64;
    let mut r: i32 = 0;
    let mut q: i32 = 0;
    let mut h: scaled_t = 0;
    let mut d: scaled_t = 0;
    let mut x: scaled_t = 0;
    let mut s: scaled_t = 0;
    let mut g: i32 = 0;
    let mut o: glue_ord = 0;
    let mut f: internal_font_number = 0;
    let mut i: b16x4 = b16x4 {
        s0: 0,
        s1: 0,
        s2: 0,
        s3: 0,
    };
    let mut pp: i32 = 0;
    let mut ppp: i32 = TEX_NULL;
    let mut total_chars: i32 = 0;
    let mut k: i32 = 0;
    last_badness = 0i32;
    r = get_node(8i32);
    MEM[r as usize].b16.s1 = 0_u16;
    MEM[r as usize].b16.s0 = 0_u16;
    MEM[(r + 4) as usize].b32.s1 = 0;
    q = r + 5i32;
    MEM[q as usize].b32.s1 = p;
    h = 0i32;
    d = 0i32;
    x = 0i32;
    total_stretch[0] = 0i32;
    total_shrink[0] = 0i32;
    total_stretch[1] = 0i32;
    total_shrink[1] = 0i32;
    total_stretch[2] = 0i32;
    total_shrink[2] = 0i32;
    total_stretch[3] = 0i32;
    total_shrink[3] = 0i32;
    if EQTB[(INT_BASE + 71i32) as usize].b32.s1 > 0i32 {
        /*1497: */
        temp_ptr = get_avail();
        MEM[temp_ptr as usize].b32.s0 = 0;
        MEM[temp_ptr as usize].b32.s1 = LR_ptr;
        LR_ptr = temp_ptr
    }
    's_130: while p != TEX_NULL {
        loop
        /*674: */
        {
            while is_char_node(p) {
                /*677: */
                f = MEM[p as usize].b16.s1 as internal_font_number;
                i = FONT_INFO[(CHAR_BASE[f as usize]
                    + effective_char(1i32 != 0, f, MEM[p as usize].b16.s0))
                    as usize]
                    .b16;
                x = x + FONT_INFO[(WIDTH_BASE[f as usize] + i.s3 as i32) as usize]
                    .b32
                    .s1;
                s = FONT_INFO[(HEIGHT_BASE[f as usize] + i.s2 as i32 / 16i32) as usize]
                    .b32
                    .s1;
                if s > h {
                    h = s
                }
                s = FONT_INFO[(DEPTH_BASE[f as usize] + i.s2 as i32 % 16i32) as usize]
                    .b32
                    .s1;
                if s > d {
                    d = s
                }
                p = MEM[p as usize].b32.s1
            }
            if !(p != TEX_NULL) {
                continue 's_130;
            }
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 2 | 13 => {
                    x = x + MEM[(p + 1) as usize].b32.s1;
                    if MEM[p as usize].b16.s1 as i32 >= 2 {
                        s = 0i32
                    } else {
                        s = MEM[(p + 4) as usize].b32.s1
                    }
                    if MEM[(p + 3) as usize].b32.s1 - s > h {
                        h = MEM[(p + 3) as usize].b32.s1 - s
                    }
                    if MEM[(p + 2) as usize].b32.s1 + s > d {
                        d = MEM[(p + 2) as usize].b32.s1 + s
                    }
                    current_block = 1176253869785344635;
                    break;
                }
                3 | 4 | 5 => {
                    if adjust_tail != TEX_NULL || pre_adjust_tail != TEX_NULL {
                        /*680: */
                        while MEM[q as usize].b32.s1 != p {
                            q = MEM[q as usize].b32.s1
                        }
                        if MEM[p as usize].b16.s1 as i32 == 5 {
                            if MEM[p as usize].b16.s0 as i32 != 0 {
                                if pre_adjust_tail == TEX_NULL {
                                    confusion(b"pre vadjust");
                                }
                                MEM[pre_adjust_tail as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1;
                                while MEM[pre_adjust_tail as usize].b32.s1 != TEX_NULL {
                                    pre_adjust_tail = MEM[pre_adjust_tail as usize].b32.s1
                                }
                            } else {
                                if adjust_tail == TEX_NULL {
                                    confusion(b"pre vadjust");
                                }
                                MEM[adjust_tail as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1;
                                while MEM[adjust_tail as usize].b32.s1 != TEX_NULL {
                                    adjust_tail = MEM[adjust_tail as usize].b32.s1
                                }
                            }
                            p = MEM[p as usize].b32.s1;
                            free_node(MEM[q as usize].b32.s1, 2);
                        } else {
                            MEM[adjust_tail as usize].b32.s1 = p;
                            adjust_tail = p;
                            p = MEM[p as usize].b32.s1
                        }
                        MEM[q as usize].b32.s1 = p;
                        p = q
                    }
                    current_block = 1176253869785344635;
                    break;
                }
                8 => match MEM[p as usize].b16.s0 as i32 {
                    40 | 41 => {
                        current_block = 10435735846551762309;
                        break;
                    }
                    42 | 43 | 44 => {
                        current_block = 9371553318591620115;
                        break;
                    }
                    _ => {
                        current_block = 1176253869785344635;
                        break;
                    }
                },
                10 => {
                    g = MEM[(p + 1) as usize].b32.s0;
                    x = x + MEM[(g + 1) as usize].b32.s1;
                    o = MEM[g as usize].b16.s1 as glue_ord;
                    total_stretch[o as usize] =
                        total_stretch[o as usize] + MEM[(g + 2) as usize].b32.s1;
                    o = MEM[g as usize].b16.s0 as glue_ord;
                    total_shrink[o as usize] =
                        total_shrink[o as usize] + MEM[(g + 3) as usize].b32.s1;
                    if MEM[p as usize].b16.s0 as i32 >= 100 {
                        g = MEM[(p + 1) as usize].b32.s1;
                        if MEM[(g + 3) as usize].b32.s1 > h {
                            h = MEM[(g + 3) as usize].b32.s1
                        }
                        if MEM[(g + 2) as usize].b32.s1 > d {
                            d = MEM[(g + 2) as usize].b32.s1
                        }
                    }
                    current_block = 1176253869785344635;
                    break;
                }
                11 => {
                    x = x + MEM[(p + 1) as usize].b32.s1;
                    current_block = 1176253869785344635;
                    break;
                }
                40 => {
                    x = x + MEM[(p + 1) as usize].b32.s1;
                    current_block = 1176253869785344635;
                    break;
                }
                9 => {
                    x = x + MEM[(p + 1) as usize].b32.s1;
                    if EQTB[(INT_BASE + 71i32) as usize].b32.s1 > 0i32 {
                        /*1498: */
                        if MEM[p as usize].b16.s0 as i32 & 1 != 0 {
                            if MEM[LR_ptr as usize].b32.s0
                                == 4i32 * (MEM[p as usize].b16.s0 as i32 / 4) + 3
                            {
                                temp_ptr = LR_ptr; /*689: */
                                LR_ptr = MEM[temp_ptr as usize].b32.s1;
                                MEM[temp_ptr as usize].b32.s1 = avail;
                                avail = temp_ptr
                            } else {
                                LR_problems += 1;
                                MEM[p as usize].b16.s1 = 11_u16;
                                MEM[p as usize].b16.s0 = 1_u16
                            }
                        } else {
                            temp_ptr = get_avail();
                            MEM[temp_ptr as usize].b32.s0 =
                                4i32 * (MEM[p as usize].b16.s0 as i32 / 4) + 3;
                            MEM[temp_ptr as usize].b32.s1 = LR_ptr;
                            LR_ptr = temp_ptr
                        }
                    }
                    current_block = 1176253869785344635;
                    break;
                }
                6 => {
                    MEM[(4999999 - 12) as usize] = MEM[(p + 1) as usize];
                    MEM[(4999999 - 12) as usize].b32.s1 = MEM[p as usize].b32.s1;
                    p = 4999999i32 - 12i32;
                    xtx_ligature_present = true
                }
                _ => {
                    current_block = 1176253869785344635;
                    break;
                }
            }
        }
        match current_block {
            10435735846551762309 => {
                if q != r + 5i32 && MEM[q as usize].b16.s1 as i32 == 7 {
                    k = MEM[q as usize].b16.s0 as i32
                } else {
                    k = 0i32
                }
                while MEM[q as usize].b32.s1 != p {
                    k -= 1;
                    q = MEM[q as usize].b32.s1;
                    if MEM[q as usize].b16.s1 as i32 == 7 {
                        k = MEM[q as usize].b16.s0 as i32
                    }
                }
                pp = MEM[p as usize].b32.s1;
                while k <= 0i32 && pp != TEX_NULL && !is_char_node(pp) {
                    if MEM[pp as usize].b16.s1 as i32 == 8
                        && (MEM[pp as usize].b16.s0 as i32 == 40
                            || MEM[pp as usize].b16.s0 as i32 == 41)
                        && MEM[(pp + 4) as usize].b16.s2 as i32
                            == MEM[(p + 4) as usize].b16.s2 as i32
                    {
                        pp = MEM[pp as usize].b32.s1
                    } else {
                        if !(MEM[pp as usize].b16.s1 as i32 == 7) {
                            break;
                        }
                        ppp = MEM[pp as usize].b32.s1;
                        if !(ppp != TEX_NULL
                            && !is_char_node(ppp)
                            && MEM[ppp as usize].b16.s1 as i32 == 8
                            && (MEM[ppp as usize].b16.s0 as i32 == 40
                                || MEM[ppp as usize].b16.s0 as i32 == 41)
                            && MEM[(ppp + 4) as usize].b16.s2 as i32
                                == MEM[(p + 4) as usize].b16.s2 as i32)
                        {
                            break;
                        }
                        pp = MEM[ppp as usize].b32.s1
                    }
                }
                if pp != MEM[p as usize].b32.s1 {
                    total_chars = 0i32;
                    p = MEM[q as usize].b32.s1;
                    while p != pp {
                        if MEM[p as usize].b16.s1 as i32 == 8 {
                            total_chars = total_chars + MEM[(p + 4) as usize].b16.s1 as i32
                        }
                        ppp = p;
                        p = MEM[p as usize].b32.s1
                    }
                    p = MEM[q as usize].b32.s1;
                    pp = new_native_word_node(
                        MEM[(p + 4) as usize].b16.s2 as internal_font_number,
                        total_chars,
                    );
                    MEM[pp as usize].b16.s0 = MEM[p as usize].b16.s0;
                    MEM[q as usize].b32.s1 = pp;
                    MEM[pp as usize].b32.s1 = MEM[ppp as usize].b32.s1;
                    MEM[ppp as usize].b32.s1 = TEX_NULL;
                    total_chars = 0i32;
                    ppp = p;
                    loop {
                        if MEM[ppp as usize].b16.s1 as i32 == 8 {
                            let mut for_end: i32 = 0;
                            k = 0i32;
                            for_end = MEM[(ppp + 4) as usize].b16.s1 as i32 - 1;
                            if k <= for_end {
                                loop {
                                    *(&mut MEM[(pp + 6) as usize] as *mut memory_word
                                        as *mut u16)
                                        .offset(total_chars as isize) =
                                        *(&mut MEM[(ppp + 6) as usize] as *mut memory_word
                                            as *mut u16)
                                            .offset(k as isize);
                                    total_chars += 1;
                                    let fresh68 = k;
                                    k = k + 1;
                                    if !(fresh68 < for_end) {
                                        break;
                                    }
                                }
                            }
                        }
                        ppp = MEM[ppp as usize].b32.s1;
                        if ppp == TEX_NULL {
                            break;
                        }
                    }
                    flush_node_list(p);
                    p = MEM[q as usize].b32.s1;
                    measure_native_node(
                        &mut MEM[p as usize] as *mut memory_word as *mut libc::c_void,
                        (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
                    );
                }
                if MEM[(p + 3) as usize].b32.s1 > h {
                    h = MEM[(p + 3) as usize].b32.s1
                }
                if MEM[(p + 2) as usize].b32.s1 > d {
                    d = MEM[(p + 2) as usize].b32.s1
                }
                x = x + MEM[(p + 1) as usize].b32.s1
            }
            9371553318591620115 => {
                if MEM[(p + 3) as usize].b32.s1 > h {
                    h = MEM[(p + 3) as usize].b32.s1
                }
                if MEM[(p + 2) as usize].b32.s1 > d {
                    d = MEM[(p + 2) as usize].b32.s1
                }
                x = x + MEM[(p + 1) as usize].b32.s1
            }
            _ => {}
        }
        p = MEM[p as usize].b32.s1
    }
    if adjust_tail != TEX_NULL {
        MEM[adjust_tail as usize].b32.s1 = TEX_NULL
    }
    if pre_adjust_tail != TEX_NULL {
        MEM[pre_adjust_tail as usize].b32.s1 = TEX_NULL
    }
    MEM[(r + 3) as usize].b32.s1 = h;
    MEM[(r + 2) as usize].b32.s1 = d;
    if m as i32 == 1i32 {
        w = x + w
    }
    MEM[(r + 1) as usize].b32.s1 = w;
    x = w - x;
    if x == 0i32 {
        MEM[(r + 5) as usize].b16.s1 = 0_u16;
        MEM[(r + 5) as usize].b16.s0 = 0_u16;
        MEM[(r + 6) as usize].gr = 0.0f64;
        current_block = 2380354494544673732;
    } else if x > 0i32 {
        /*683: */
        if total_stretch[3] != 0i32 {
            o = 3i32 as glue_ord
        } else if total_stretch[2] != 0i32 {
            o = 2i32 as glue_ord
        } else if total_stretch[1] != 0i32 {
            o = 1i32 as glue_ord
        } else {
            o = 0i32 as glue_ord
        } /*normal *//*:684 */
        MEM[(r + 5) as usize].b16.s0 = o as u16;
        MEM[(r + 5) as usize].b16.s1 = 1_u16;
        if total_stretch[o as usize] != 0i32 {
            MEM[(r + 6) as usize].gr = x as f64 / total_stretch[o as usize] as f64
        } else {
            MEM[(r + 5) as usize].b16.s1 = 0_u16;
            MEM[(r + 6) as usize].gr = 0.0f64
        }
        if o as i32 == 0i32 {
            if MEM[(r + 5) as usize].b32.s1 != TEX_NULL {
                /*685: */
                last_badness = badness(x, total_stretch[0]); /*normal *//*:690 */
                if last_badness > EQTB[(INT_BASE + 26i32) as usize].b32.s1 {
                    print_ln();
                    if last_badness > 100i32 {
                        print_nl_cstr(b"Underfull");
                    } else {
                        print_nl_cstr(b"Loose");
                    }
                    print_cstr(b" \\hbox (badness ");
                    print_int(last_badness);
                    current_block = 13814253595362444008;
                } else {
                    current_block = 2380354494544673732;
                }
            } else {
                current_block = 2380354494544673732;
            }
        } else {
            current_block = 2380354494544673732;
        }
    } else {
        if total_shrink[3] != 0i32 {
            o = 3i32 as glue_ord
        } else if total_shrink[2] != 0i32 {
            o = 2i32 as glue_ord
        } else if total_shrink[1] != 0i32 {
            o = 1i32 as glue_ord
        } else {
            o = 0i32 as glue_ord
        }
        MEM[(r + 5) as usize].b16.s0 = o as u16;
        MEM[(r + 5) as usize].b16.s1 = 2_u16;
        if total_shrink[o as usize] != 0i32 {
            MEM[(r + 6) as usize].gr = -x as f64 / total_shrink[o as usize] as f64
        } else {
            MEM[(r + 5) as usize].b16.s1 = 0_u16;
            MEM[(r + 6) as usize].gr = 0.0f64
        }
        if total_shrink[o as usize] < -x
            && o as i32 == 0i32
            && MEM[(r + 5) as usize].b32.s1 != TEX_NULL
        {
            last_badness = 1000000i64 as i32;
            MEM[(r + 6) as usize].gr = 1.0f64;
            if -x - total_shrink[0] > EQTB[(DIMEN_BASE + 8i32) as usize].b32.s1
                || EQTB[(INT_BASE + 26i32) as usize].b32.s1 < 100i32
            {
                if EQTB[(DIMEN_BASE + 16i32) as usize].b32.s1 > 0i32
                    && -x - total_shrink[0] > EQTB[(DIMEN_BASE + 8i32) as usize].b32.s1
                {
                    while MEM[q as usize].b32.s1 != TEX_NULL {
                        q = MEM[q as usize].b32.s1
                    }
                    MEM[q as usize].b32.s1 = new_rule();
                    MEM[(MEM[q as usize].b32.s1 + 1) as usize].b32.s1 =
                        EQTB[(DIMEN_BASE + 16i32) as usize].b32.s1
                }
                print_ln();
                print_nl_cstr(b"Overfull \\hbox (");
                print_scaled(-x - total_shrink[0]);
                print_cstr(b"pt too wide");
                current_block = 13814253595362444008;
            } else {
                current_block = 2380354494544673732;
            }
        } else if o as i32 == 0i32 {
            if MEM[(r + 5) as usize].b32.s1 != TEX_NULL {
                /*692: */
                last_badness = badness(-x, total_shrink[0]);
                if last_badness > EQTB[(INT_BASE + 26i32) as usize].b32.s1 {
                    print_ln();
                    print_nl_cstr(b"Tight \\hbox (badness ");
                    print_int(last_badness);
                    current_block = 13814253595362444008;
                } else {
                    current_block = 2380354494544673732;
                }
            } else {
                current_block = 2380354494544673732;
            }
        } else {
            current_block = 2380354494544673732;
        }
    }
    loop {
        match current_block {
            13814253595362444008 => {
                if output_active {
                    print_cstr(b") has occurred while \\output is active");
                } else {
                    if pack_begin_line != 0i32 {
                        if pack_begin_line > 0i32 {
                            print_cstr(b") in paragraph at lines ");
                        } else {
                            print_cstr(b") in alignment at lines ");
                        }
                        print_int(pack_begin_line.abs());
                        print_cstr(b"--");
                    } else {
                        print_cstr(b") detected at line ");
                    }
                    print_int(line);
                }
                print_ln();
                font_in_short_display = 0i32;
                short_display(MEM[(r + 5) as usize].b32.s1);
                print_ln();
                begin_diagnostic();
                show_box(r);
                end_diagnostic(1i32 != 0);
                current_block = 2380354494544673732;
            }
            _ => {
                if !(EQTB[(INT_BASE + 71i32) as usize].b32.s1 > 0i32) {
                    break;
                }
                /*1499: */
                if MEM[LR_ptr as usize].b32.s0 != 0 {
                    while MEM[q as usize].b32.s1 != TEX_NULL {
                        q = MEM[q as usize].b32.s1
                    } /*:673 */
                    loop {
                        temp_ptr = q;
                        q = new_math(0i32, MEM[LR_ptr as usize].b32.s0 as small_number);
                        MEM[temp_ptr as usize].b32.s1 = q;
                        LR_problems = LR_problems + 10000i32;
                        temp_ptr = LR_ptr;
                        LR_ptr = MEM[temp_ptr as usize].b32.s1;
                        MEM[temp_ptr as usize].b32.s1 = avail;
                        avail = temp_ptr;
                        if MEM[LR_ptr as usize].b32.s0 == 0 {
                            break;
                        }
                    }
                }
                if LR_problems > 0i32 {
                    print_ln();
                    print_nl_cstr(b"\\endL or \\endR problem (");
                    print_int(LR_problems / 10000i32);
                    print_cstr(b" missing, ");
                    print_int(LR_problems % 10000i32);
                    print_cstr(b" extra");
                    LR_problems = 0i32;
                    current_block = 13814253595362444008;
                } else {
                    temp_ptr = LR_ptr;
                    LR_ptr = MEM[temp_ptr as usize].b32.s1;
                    MEM[temp_ptr as usize].b32.s1 = avail;
                    avail = temp_ptr;
                    if LR_ptr != TEX_NULL {
                        confusion(b"LR1");
                    }
                    break;
                }
            }
        }
    }
    r
}
pub(crate) unsafe fn vpackage(
    mut p: i32,
    mut h: scaled_t,
    mut m: small_number,
    mut l: scaled_t,
) -> i32 {
    let mut current_block: u64;
    let mut r: i32 = 0;
    let mut w: scaled_t = 0;
    let mut d: scaled_t = 0;
    let mut x: scaled_t = 0;
    let mut s: scaled_t = 0;
    let mut g: i32 = 0;
    let mut o: glue_ord = 0;
    last_badness = 0i32;
    r = get_node(8i32);
    MEM[r as usize].b16.s1 = 1_u16;
    if EQTB[(INT_BASE + 73i32) as usize].b32.s1 > 0i32 {
        MEM[r as usize].b16.s0 = 1_u16
    } else {
        MEM[r as usize].b16.s0 = 0_u16
    }
    MEM[(r + 4) as usize].b32.s1 = 0;
    MEM[(r + 5) as usize].b32.s1 = p;
    w = 0i32;
    d = 0i32;
    x = 0i32;
    total_stretch[0] = 0i32;
    total_shrink[0] = 0i32;
    total_stretch[1] = 0i32;
    total_shrink[1] = 0i32;
    total_stretch[2] = 0i32;
    total_shrink[2] = 0i32;
    total_stretch[3] = 0i32;
    total_shrink[3] = 0i32;
    while p != TEX_NULL {
        /*694: */
        if is_char_node(p) {
            confusion(b"vpack"); /*701: */
        } else {
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 2 | 13 => {
                    x = x + d + MEM[(p + 3) as usize].b32.s1;
                    d = MEM[(p + 2) as usize].b32.s1;
                    if MEM[p as usize].b16.s1 as i32 >= 2 {
                        s = 0i32
                    } else {
                        s = MEM[(p + 4) as usize].b32.s1
                    }
                    if MEM[(p + 1) as usize].b32.s1 + s > w {
                        w = MEM[(p + 1) as usize].b32.s1 + s
                    }
                }
                8 => {
                    if MEM[p as usize].b16.s0 as i32 == 43 || MEM[p as usize].b16.s0 as i32 == 44 {
                        x = x + d + MEM[(p + 3) as usize].b32.s1;
                        d = MEM[(p + 2) as usize].b32.s1;
                        if MEM[(p + 1) as usize].b32.s1 > w {
                            w = MEM[(p + 1) as usize].b32.s1
                        }
                    }
                }
                10 => {
                    x = x + d;
                    d = 0i32;
                    g = MEM[(p + 1) as usize].b32.s0;
                    x = x + MEM[(g + 1) as usize].b32.s1;
                    o = MEM[g as usize].b16.s1 as glue_ord;
                    total_stretch[o as usize] =
                        total_stretch[o as usize] + MEM[(g + 2) as usize].b32.s1;
                    o = MEM[g as usize].b16.s0 as glue_ord;
                    total_shrink[o as usize] =
                        total_shrink[o as usize] + MEM[(g + 3) as usize].b32.s1;
                    if MEM[p as usize].b16.s0 as i32 >= 100 {
                        g = MEM[(p + 1) as usize].b32.s1;
                        if MEM[(g + 1) as usize].b32.s1 > w {
                            w = MEM[(g + 1) as usize].b32.s1
                        }
                    }
                }
                11 => {
                    x = x + d + MEM[(p + 1) as usize].b32.s1;
                    d = 0i32
                }
                _ => {}
            }
        }
        p = MEM[p as usize].b32.s1
    }
    MEM[(r + 1) as usize].b32.s1 = w;
    if d > l {
        x = x + d - l;
        MEM[(r + 2) as usize].b32.s1 = l
    } else {
        MEM[(r + 2) as usize].b32.s1 = d
    }
    if m as i32 == 1i32 {
        h = x + h
    }
    MEM[(r + 3) as usize].b32.s1 = h;
    x = h - x;
    if x == 0i32 {
        MEM[(r + 5) as usize].b16.s1 = 0_u16;
        MEM[(r + 5) as usize].b16.s0 = 0_u16;
        MEM[(r + 6) as usize].gr = 0.0f64
    } else {
        if x > 0i32 {
            /*698: */
            if total_stretch[3] != 0i32 {
                o = 3i32 as glue_ord
            } else if total_stretch[2] != 0i32 {
                o = 2i32 as glue_ord
            } else if total_stretch[1] != 0i32 {
                o = 1i32 as glue_ord
            } else {
                o = 0i32 as glue_ord
            } /*normal *//*:684 */
            MEM[(r + 5) as usize].b16.s0 = o as u16;
            MEM[(r + 5) as usize].b16.s1 = 1_u16;
            if total_stretch[o as usize] != 0i32 {
                MEM[(r + 6) as usize].gr = x as f64 / total_stretch[o as usize] as f64
            } else {
                MEM[(r + 5) as usize].b16.s1 = 0_u16;
                MEM[(r + 6) as usize].gr = 0.0f64
            }
            if o as i32 == 0i32 {
                if MEM[(r + 5) as usize].b32.s1 != TEX_NULL {
                    /*699: */
                    last_badness = badness(x, total_stretch[0]); /*normal *//*:690 */
                    if last_badness > EQTB[(INT_BASE + 27i32) as usize].b32.s1 {
                        print_ln();
                        if last_badness > 100i32 {
                            print_nl_cstr(b"Underfull");
                        } else {
                            print_nl_cstr(b"Loose");
                        }
                        print_cstr(b" \\vbox (badness ");
                        print_int(last_badness);
                        current_block = 13130523023485106979;
                    } else {
                        current_block = 13281346226780081721;
                    }
                } else {
                    current_block = 13281346226780081721;
                }
            } else {
                current_block = 13281346226780081721;
            }
        } else {
            if total_shrink[3] != 0i32 {
                o = 3i32 as glue_ord
            } else if total_shrink[2] != 0i32 {
                o = 2i32 as glue_ord
            } else if total_shrink[1] != 0i32 {
                o = 1i32 as glue_ord
            } else {
                o = 0i32 as glue_ord
            }
            MEM[(r + 5) as usize].b16.s0 = o as u16;
            MEM[(r + 5) as usize].b16.s1 = 2_u16;
            if total_shrink[o as usize] != 0i32 {
                MEM[(r + 6) as usize].gr = -x as f64 / total_shrink[o as usize] as f64
            } else {
                MEM[(r + 5) as usize].b16.s1 = 0_u16;
                MEM[(r + 6) as usize].gr = 0.0f64
            }
            if total_shrink[o as usize] < -x
                && o as i32 == 0i32
                && MEM[(r + 5) as usize].b32.s1 != TEX_NULL
            {
                last_badness = 1000000i64 as i32;
                MEM[(r + 6) as usize].gr = 1.0f64;
                if -x - total_shrink[0] > EQTB[(DIMEN_BASE + 9i32) as usize].b32.s1
                    || EQTB[(INT_BASE + 27i32) as usize].b32.s1 < 100i32
                {
                    print_ln();
                    print_nl_cstr(b"Overfull \\vbox (");
                    print_scaled(-x - total_shrink[0]);
                    print_cstr(b"pt too high");
                    current_block = 13130523023485106979;
                } else {
                    current_block = 13281346226780081721;
                }
            } else if o as i32 == 0i32 {
                if MEM[(r + 5) as usize].b32.s1 != TEX_NULL {
                    /*703: */
                    last_badness = badness(-x, total_shrink[0]);
                    if last_badness > EQTB[(INT_BASE + 27i32) as usize].b32.s1 {
                        print_ln();
                        print_nl_cstr(b"Tight \\vbox (badness ");
                        print_int(last_badness);
                        current_block = 13130523023485106979;
                    } else {
                        current_block = 13281346226780081721;
                    }
                } else {
                    current_block = 13281346226780081721;
                }
            } else {
                current_block = 13281346226780081721;
            }
        }
        match current_block {
            13281346226780081721 => {}
            _ => {
                if output_active {
                    print_cstr(b") has occurred while \\output is active");
                } else {
                    if pack_begin_line != 0i32 {
                        print_cstr(b") in alignment at lines ");
                        print_int(pack_begin_line.abs());
                        print_cstr(b"--");
                    } else {
                        print_cstr(b") detected at line ");
                    }
                    print_int(line);
                    print_ln();
                }
                begin_diagnostic();
                show_box(r);
                end_diagnostic(1i32 != 0);
            }
        }
    }
    r
}
pub(crate) unsafe fn append_to_vlist(mut b: i32) {
    let mut d: scaled_t = 0;
    let mut p: i32 = 0;
    let mut upwards: bool = false;
    upwards = EQTB[(INT_BASE + 73i32) as usize].b32.s1 > 0i32;
    if cur_list.aux.b32.s1 > -65536000i32 {
        if upwards {
            d = MEM[(EQTB[(GLUE_BASE + 1i32) as usize].b32.s1 + 1i32) as usize]
                .b32
                .s1
                - cur_list.aux.b32.s1
                - MEM[(b + 2) as usize].b32.s1
        } else {
            d = MEM[(EQTB[(GLUE_BASE + 1i32) as usize].b32.s1 + 1i32) as usize]
                .b32
                .s1
                - cur_list.aux.b32.s1
                - MEM[(b + 3) as usize].b32.s1
        }
        if d < EQTB[(DIMEN_BASE + 2i32) as usize].b32.s1 {
            p = new_param_glue(0i32 as small_number)
        } else {
            p = new_skip_param(1i32 as small_number);
            MEM[(temp_ptr + 1) as usize].b32.s1 = d
        }
        MEM[cur_list.tail as usize].b32.s1 = p;
        cur_list.tail = p
    }
    MEM[cur_list.tail as usize].b32.s1 = b;
    cur_list.tail = b;
    if upwards {
        cur_list.aux.b32.s1 = MEM[(b + 3) as usize].b32.s1
    } else {
        cur_list.aux.b32.s1 = MEM[(b + 2) as usize].b32.s1
    };
}
pub(crate) unsafe fn new_noad() -> i32 {
    let mut p: i32 = 0;
    p = get_node(4i32);
    MEM[p as usize].b16.s1 = 16_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32 = empty;
    MEM[(p + 3) as usize].b32 = empty;
    MEM[(p + 2) as usize].b32 = empty;
    p
}
pub(crate) unsafe fn new_style(mut s: small_number) -> i32 {
    let mut p: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 14_u16;
    MEM[p as usize].b16.s0 = s as u16;
    MEM[(p + 1) as usize].b32.s1 = 0;
    MEM[(p + 2) as usize].b32.s1 = 0;
    p
}
pub(crate) unsafe fn new_choice() -> i32 {
    let mut p: i32 = 0;
    p = get_node(3i32);
    MEM[p as usize].b16.s1 = 15_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s0 = TEX_NULL;
    MEM[(p + 1) as usize].b32.s1 = TEX_NULL;
    MEM[(p + 2) as usize].b32.s0 = TEX_NULL;
    MEM[(p + 2) as usize].b32.s1 = TEX_NULL;
    p
}
pub(crate) unsafe fn show_info() {
    show_node_list(MEM[temp_ptr as usize].b32.s0);
}
pub(crate) unsafe fn push_alignment() {
    let mut p: i32 = 0;
    p = get_node(6i32);
    MEM[p as usize].b32.s1 = align_ptr;
    MEM[p as usize].b32.s0 = cur_align;
    MEM[(p + 1) as usize].b32.s0 = MEM[(4999999 - 8) as usize].b32.s1;
    MEM[(p + 1) as usize].b32.s1 = cur_span;
    MEM[(p + 2) as usize].b32.s1 = cur_loop;
    MEM[(p + 3) as usize].b32.s1 = align_state;
    MEM[(p + 4) as usize].b32.s0 = cur_head;
    MEM[(p + 4) as usize].b32.s1 = cur_tail;
    MEM[(p + 5) as usize].b32.s0 = cur_pre_head;
    MEM[(p + 5) as usize].b32.s1 = cur_pre_tail;
    align_ptr = p;
    cur_head = get_avail();
    cur_pre_head = get_avail();
}
pub(crate) unsafe fn pop_alignment() {
    let mut p: i32 = 0;
    MEM[cur_head as usize].b32.s1 = avail;
    avail = cur_head;
    MEM[cur_pre_head as usize].b32.s1 = avail;
    avail = cur_pre_head;
    p = align_ptr;
    cur_tail = MEM[(p + 4) as usize].b32.s1;
    cur_head = MEM[(p + 4) as usize].b32.s0;
    cur_pre_tail = MEM[(p + 5) as usize].b32.s1;
    cur_pre_head = MEM[(p + 5) as usize].b32.s0;
    align_state = MEM[(p + 3) as usize].b32.s1;
    cur_loop = MEM[(p + 2) as usize].b32.s1;
    cur_span = MEM[(p + 1) as usize].b32.s1;
    MEM[(4999999 - 8) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s0;
    cur_align = MEM[p as usize].b32.s0;
    align_ptr = MEM[p as usize].b32.s1;
    free_node(p, 6i32);
}
pub(crate) unsafe fn get_preamble_token() {
    loop {
        get_token();
        while cur_chr == 0x10ffffi32 + 2i32 && cur_cmd as i32 == 4i32 {
            get_token();
            if cur_cmd as i32 > 102i32 {
                expand();
                get_token();
            }
        }
        if cur_cmd as i32 == 9i32 {
            fatal_error(b"(interwoven alignment preambles are not allowed)");
        }
        if !(cur_cmd as i32 == 76i32 && cur_chr == GLUE_BASE + 11i32) {
            break;
        }
        scan_optional_equals();
        scan_glue(2i32 as small_number);
        if EQTB[(INT_BASE + 43i32) as usize].b32.s1 > 0i32 {
            geq_define(
                1i32 + (0x10ffffi32 + 1i32)
                    + (0x10ffffi32 + 1i32)
                    + 1i32
                    + 15000i32
                    + 12i32
                    + 9000i32
                    + 1i32
                    + 1i32
                    + 11i32,
                119_u16,
                cur_val,
            );
        } else {
            eq_define(
                1i32 + (0x10ffffi32 + 1i32)
                    + (0x10ffffi32 + 1i32)
                    + 1i32
                    + 15000i32
                    + 12i32
                    + 9000i32
                    + 1i32
                    + 1i32
                    + 11i32,
                119_u16,
                cur_val,
            );
        }
    }
}
pub(crate) unsafe fn init_align() {
    let mut save_cs_ptr: i32 = 0;
    let mut p: i32 = 0;
    save_cs_ptr = cur_cs;
    push_alignment();
    align_state = -1000000i64 as i32;
    if cur_list.mode as i32 == 207i32
        && (cur_list.tail != cur_list.head || cur_list.aux.b32.s1 != TEX_NULL)
    {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Improper ");
        print_esc_cstr(b"halign");
        print_cstr(b" inside $$\'s");
        help_ptr = 3_u8;
        help_line[2] = b"Displays can use special alignments (like \\eqalignno)";
        help_line[1] = b"only if nothing but the alignment itself is between $$\'s.";
        help_line[0] = b"So I\'ve deleted the formulas that preceded this alignment.";
        error();
        flush_math();
    }
    push_nest();
    if cur_list.mode as i32 == 207i32 {
        cur_list.mode = -1_i16;
        cur_list.aux.b32.s1 = (*nest.offset((nest_ptr - 2i32) as isize)).aux.b32.s1
    } else if cur_list.mode as i32 > 0i32 {
        cur_list.mode = -(cur_list.mode as i32) as i16
        /*:804*/
    }
    scan_spec(6i32 as group_code, false);
    MEM[(4999999 - 8) as usize].b32.s1 = TEX_NULL;
    cur_align = 4999999i32 - 8i32;
    cur_loop = TEX_NULL;
    scanner_status = 4_u8;
    warning_index = save_cs_ptr;
    align_state = -1000000i64 as i32;
    loop {
        MEM[cur_align as usize].b32.s1 = new_param_glue(11 as small_number);
        /*:808 */
        cur_align = MEM[cur_align as usize].b32.s1; /*:807*/
        if cur_cmd as i32 == 5i32 {
            break; /*:813*/
        } /*:806 */
        p = 4999999i32 - 4i32;
        MEM[p as usize].b32.s1 = TEX_NULL;
        loop {
            get_preamble_token();
            if cur_cmd as i32 == 6i32 {
                break;
            }
            if cur_cmd as i32 <= 5i32 && cur_cmd as i32 >= 4i32 && align_state as i64 == -1000000 {
                if p == 4999999i32 - 4i32 && cur_loop == TEX_NULL && cur_cmd as i32 == 4i32 {
                    cur_loop = cur_align
                } else {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Missing # inserted in alignment preamble");
                    help_ptr = 3_u8;
                    help_line[2] = b"There should be exactly one # between &\'s, when an";
                    help_line[1] = b"\\halign or \\valign is being set up. In this case you had";
                    help_line[0] = b"none, so I\'ve put one in; maybe that will work.";
                    back_error();
                    break;
                }
            } else if cur_cmd as i32 != 10i32 || p != 4999999i32 - 4i32 {
                MEM[p as usize].b32.s1 = get_avail();
                p = MEM[p as usize].b32.s1;
                MEM[p as usize].b32.s0 = cur_tok
            }
        }
        MEM[cur_align as usize].b32.s1 = new_null_box();
        cur_align = MEM[cur_align as usize].b32.s1;
        MEM[cur_align as usize].b32.s0 = 4999999 - 9;
        MEM[(cur_align + 1) as usize].b32.s1 = -0x40000000;
        MEM[(cur_align + 3) as usize].b32.s1 = MEM[(4999999 - 4) as usize].b32.s1;
        p = 4999999i32 - 4i32;
        MEM[p as usize].b32.s1 = TEX_NULL;
        loop {
            get_preamble_token();
            if cur_cmd as i32 <= 5i32 && cur_cmd as i32 >= 4i32 && align_state as i64 == -1000000 {
                break;
            }
            if cur_cmd as i32 == 6i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Only one # is allowed per tab");
                help_ptr = 3_u8;
                help_line[2] = b"There should be exactly one # between &\'s, when an";
                help_line[1] = b"\\halign or \\valign is being set up. In this case you had";
                help_line[0] = b"more than one, so I\'m ignoring all but the first.";
                error();
            } else {
                MEM[p as usize].b32.s1 = get_avail();
                p = MEM[p as usize].b32.s1;
                MEM[p as usize].b32.s0 = cur_tok
            }
        }
        MEM[p as usize].b32.s1 = get_avail();
        p = MEM[p as usize].b32.s1;
        MEM[p as usize].b32.s0 = 0x1ffffff + (FROZEN_CONTROL_SEQUENCE + 5i32);
        MEM[(cur_align + 2) as usize].b32.s1 = MEM[(4999999 - 4) as usize].b32.s1
    }
    scanner_status = 0_u8;
    new_save_level(6i32 as group_code);
    if EQTB[(LOCAL_BASE + 8i32) as usize].b32.s1 != TEX_NULL {
        begin_token_list(EQTB[(LOCAL_BASE + 8i32) as usize].b32.s1, 14_u16);
    }
    align_peek();
}
pub(crate) unsafe fn init_span(mut p: i32) {
    push_nest();
    if cur_list.mode as i32 == -104i32 {
        cur_list.aux.b32.s0 = 1000i32
    } else {
        cur_list.aux.b32.s1 = -65536000i32;
        normal_paragraph();
    }
    cur_span = p;
}
pub(crate) unsafe fn init_row() {
    push_nest();
    cur_list.mode = (-105i32 - cur_list.mode as i32) as i16;
    if cur_list.mode as i32 == -104i32 {
        cur_list.aux.b32.s0 = 0i32
    } else {
        cur_list.aux.b32.s1 = 0i32
    }
    MEM[cur_list.tail as usize].b32.s1 = new_glue(
        MEM[(MEM[(4999999 - 8) as usize].b32.s1 + 1) as usize]
            .b32
            .s0,
    );
    cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
    MEM[cur_list.tail as usize].b16.s0 = (11 + 1) as u16;
    cur_align = MEM[MEM[(4999999 - 8) as usize].b32.s1 as usize].b32.s1;
    cur_tail = cur_head;
    cur_pre_tail = cur_pre_head;
    init_span(cur_align);
}
pub(crate) unsafe fn init_col() {
    MEM[(cur_align + 5) as usize].b32.s0 = cur_cmd as i32;
    if cur_cmd as i32 == 63i32 {
        align_state = 0i32
    } else {
        back_input();
        begin_token_list(MEM[(cur_align + 3) as usize].b32.s1, 1_u16);
    };
}
pub(crate) unsafe fn fin_col() -> bool {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut s: i32 = 0;
    let mut u: i32 = 0;
    let mut w: scaled_t = 0;
    let mut o: glue_ord = 0;
    let mut n: i32 = 0;
    if cur_align == TEX_NULL {
        confusion(b"endv");
    }
    q = MEM[cur_align as usize].b32.s1;
    if q == TEX_NULL {
        confusion(b"endv");
    }
    if (align_state as i64) < 500000 {
        fatal_error(b"(interwoven alignment preambles are not allowed)");
    }
    p = MEM[q as usize].b32.s1;
    if p == TEX_NULL && MEM[(cur_align + 5) as usize].b32.s0 < 0x10ffff + 3 {
        if cur_loop != TEX_NULL {
            /*822: */
            MEM[q as usize].b32.s1 = new_null_box(); /*:823 */
            p = MEM[q as usize].b32.s1;
            MEM[p as usize].b32.s0 = 4999999 - 9;
            MEM[(p + 1) as usize].b32.s1 = -0x40000000;
            cur_loop = MEM[cur_loop as usize].b32.s1;
            q = 4999999i32 - 4i32;
            r = MEM[(cur_loop + 3) as usize].b32.s1;
            while r != TEX_NULL {
                MEM[q as usize].b32.s1 = get_avail();
                q = MEM[q as usize].b32.s1;
                MEM[q as usize].b32.s0 = MEM[r as usize].b32.s0;
                r = MEM[r as usize].b32.s1
            }
            MEM[q as usize].b32.s1 = TEX_NULL;
            MEM[(p + 3) as usize].b32.s1 = MEM[(4999999 - 4) as usize].b32.s1;
            q = 4999999i32 - 4i32;
            r = MEM[(cur_loop + 2) as usize].b32.s1;
            while r != TEX_NULL {
                MEM[q as usize].b32.s1 = get_avail();
                q = MEM[q as usize].b32.s1;
                MEM[q as usize].b32.s0 = MEM[r as usize].b32.s0;
                r = MEM[r as usize].b32.s1
            }
            MEM[q as usize].b32.s1 = TEX_NULL;
            MEM[(p + 2) as usize].b32.s1 = MEM[(4999999 - 4) as usize].b32.s1;
            cur_loop = MEM[cur_loop as usize].b32.s1;
            MEM[p as usize].b32.s1 = new_glue(MEM[(cur_loop + 1) as usize].b32.s0)
        } else {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Extra alignment tab has been changed to ");
            print_esc_cstr(b"cr");
            help_ptr = 3_u8;
            help_line[2] = b"You have given more \\span or & marks than there were";
            help_line[1] = b"in the preamble to the \\halign or \\valign now in progress.";
            help_line[0] = b"So I\'ll assume that you meant to type \\cr instead.";
            MEM[(cur_align + 5) as usize].b32.s0 = 0x10ffff + 3;
            error();
        }
    }
    if MEM[(cur_align + 5) as usize].b32.s0 != 0x10ffff + 2 {
        unsave();
        new_save_level(6i32 as group_code);
        if cur_list.mode as i32 == -104i32 {
            adjust_tail = cur_tail;
            pre_adjust_tail = cur_pre_tail;
            u = hpack(
                MEM[cur_list.head as usize].b32.s1,
                0i32,
                1i32 as small_number,
            );
            w = MEM[(u + 1) as usize].b32.s1;
            cur_tail = adjust_tail;
            adjust_tail = TEX_NULL;
            cur_pre_tail = pre_adjust_tail;
            pre_adjust_tail = TEX_NULL
        } else {
            u = vpackage(
                MEM[cur_list.head as usize].b32.s1,
                0i32,
                1i32 as small_number,
                0i32,
            );
            w = MEM[(u + 3) as usize].b32.s1
        }
        n = 0i32;
        if cur_span != cur_align {
            /*827: */
            q = cur_span; /*normal *//*:684 */
            loop {
                n += 1; /*normal *//*:690 */
                q = MEM[MEM[q as usize].b32.s1 as usize].b32.s1; /*tab_skip_code 1 *//*:824 */
                if q == cur_align {
                    break;
                }
            }
            if n > 65535i32 {
                confusion(b"too many spans");
            }
            q = cur_span;
            while MEM[MEM[q as usize].b32.s0 as usize].b32.s1 < n {
                q = MEM[q as usize].b32.s0
            }
            if MEM[MEM[q as usize].b32.s0 as usize].b32.s1 > n {
                s = get_node(2i32);
                MEM[s as usize].b32.s0 = MEM[q as usize].b32.s0;
                MEM[s as usize].b32.s1 = n;
                MEM[q as usize].b32.s0 = s;
                MEM[(s + 1) as usize].b32.s1 = w
            } else if MEM[(MEM[q as usize].b32.s0 + 1) as usize].b32.s1 < w {
                MEM[(MEM[q as usize].b32.s0 + 1) as usize].b32.s1 = w
            }
        } else if w > MEM[(cur_align + 1) as usize].b32.s1 {
            MEM[(cur_align + 1) as usize].b32.s1 = w
        }
        MEM[u as usize].b16.s1 = 13_u16;
        MEM[u as usize].b16.s0 = n as u16;
        if total_stretch[3] != 0i32 {
            o = 3i32 as glue_ord
        } else if total_stretch[2] != 0i32 {
            o = 2i32 as glue_ord
        } else if total_stretch[1] != 0i32 {
            o = 1i32 as glue_ord
        } else {
            o = 0i32 as glue_ord
        }
        MEM[(u + 5) as usize].b16.s0 = o as u16;
        MEM[(u + 6) as usize].b32.s1 = total_stretch[o as usize];
        if total_shrink[3] != 0i32 {
            o = 3i32 as glue_ord
        } else if total_shrink[2] != 0i32 {
            o = 2i32 as glue_ord
        } else if total_shrink[1] != 0i32 {
            o = 1i32 as glue_ord
        } else {
            o = 0i32 as glue_ord
        }
        MEM[(u + 5) as usize].b16.s1 = o as u16;
        MEM[(u + 4) as usize].b32.s1 = total_shrink[o as usize];
        pop_nest();
        MEM[cur_list.tail as usize].b32.s1 = u;
        cur_list.tail = u;
        MEM[cur_list.tail as usize].b32.s1 =
            new_glue(MEM[(MEM[cur_align as usize].b32.s1 + 1) as usize].b32.s0);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[cur_list.tail as usize].b16.s0 = 12_u16;
        if MEM[(cur_align + 5) as usize].b32.s0 >= 0x10ffff + 3 {
            return true;
        }
        init_span(p);
    }
    align_state = 1000000i64 as i32;
    loop {
        get_x_or_protected();
        if cur_cmd as i32 != 10i32 {
            break;
        }
    }
    cur_align = p;
    init_col();
    false
}
pub(crate) unsafe fn fin_row() {
    let mut p: i32 = 0;
    if cur_list.mode as i32 == -104i32 {
        p = hpack(
            MEM[cur_list.head as usize].b32.s1,
            0i32,
            1i32 as small_number,
        );
        pop_nest();
        if cur_pre_head != cur_pre_tail {
            MEM[cur_list.tail as usize].b32.s1 = MEM[cur_pre_head as usize].b32.s1;
            cur_list.tail = cur_pre_tail
        }
        append_to_vlist(p);
        if cur_head != cur_tail {
            MEM[cur_list.tail as usize].b32.s1 = MEM[cur_head as usize].b32.s1;
            cur_list.tail = cur_tail
        }
    } else {
        p = vpackage(
            MEM[cur_list.head as usize].b32.s1,
            0i32,
            1i32 as small_number,
            0x3fffffffi32,
        );
        pop_nest();
        MEM[cur_list.tail as usize].b32.s1 = p;
        cur_list.tail = p;
        cur_list.aux.b32.s0 = 1000i32
    }
    MEM[p as usize].b16.s1 = 13_u16;
    MEM[(p + 6) as usize].b32.s1 = 0;
    if EQTB[(LOCAL_BASE + 8i32) as usize].b32.s1 != TEX_NULL {
        begin_token_list(EQTB[(LOCAL_BASE + 8i32) as usize].b32.s1, 14_u16);
    }
    align_peek();
}
pub(crate) unsafe fn fin_align() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut s: i32 = 0;
    let mut u: i32 = 0;
    let mut v: i32 = 0;
    let mut t: scaled_t = 0;
    let mut w: scaled_t = 0;
    let mut o: scaled_t = 0;
    let mut n: i32 = 0;
    let mut rule_save: scaled_t = 0;
    let mut aux_save: memory_word = memory_word {
        b32: b32x2 { s0: 0, s1: 0 },
    };
    if cur_group as i32 != 6i32 {
        confusion(b"align1");
    }
    unsave();
    if cur_group as i32 != 6i32 {
        confusion(b"align0");
    }
    unsave();
    if (*nest.offset((nest_ptr - 1i32) as isize)).mode as i32 == 207i32 {
        o = EQTB[(DIMEN_BASE + 15i32) as usize].b32.s1
    } else {
        o = 0i32
    }
    q = MEM[MEM[(4999999 - 8) as usize].b32.s1 as usize].b32.s1;
    loop {
        flush_list(MEM[(q + 3) as usize].b32.s1);
        flush_list(MEM[(q + 2) as usize].b32.s1);
        p = MEM[MEM[q as usize].b32.s1 as usize].b32.s1;
        if MEM[(q + 1) as usize].b32.s1 == -0x40000000 {
            /*831: */
            MEM[(q + 1) as usize].b32.s1 = 0;
            r = MEM[q as usize].b32.s1;
            s = MEM[(r + 1) as usize].b32.s0;
            if s != 0i32 {
                MEM[0].b32.s1 += 1;
                delete_glue_ref(s);
                MEM[(r + 1) as usize].b32.s0 = 0
            }
        }
        if MEM[q as usize].b32.s0 != 4999999 - 9 {
            /*832: */
            t = MEM[(q + 1) as usize].b32.s1
                + MEM[(MEM[(MEM[q as usize].b32.s1 + 1) as usize].b32.s0 + 1) as usize]
                    .b32
                    .s1; /*:833 */
            r = MEM[q as usize].b32.s0;
            s = 4999999i32 - 9i32;
            MEM[s as usize].b32.s0 = p;
            n = 1i32;
            loop {
                MEM[(r + 1) as usize].b32.s1 = MEM[(r + 1) as usize].b32.s1 - t;
                u = MEM[r as usize].b32.s0;
                while MEM[r as usize].b32.s1 > n {
                    s = MEM[s as usize].b32.s0;
                    n = MEM[MEM[s as usize].b32.s0 as usize].b32.s1 + 1
                }
                if MEM[r as usize].b32.s1 < n {
                    MEM[r as usize].b32.s0 = MEM[s as usize].b32.s0;
                    MEM[s as usize].b32.s0 = r;
                    MEM[r as usize].b32.s1 -= 1;
                    s = r
                } else {
                    if MEM[(r + 1) as usize].b32.s1
                        > MEM[(MEM[s as usize].b32.s0 + 1) as usize].b32.s1
                    {
                        MEM[(MEM[s as usize].b32.s0 + 1) as usize].b32.s1 =
                            MEM[(r + 1) as usize].b32.s1
                    }
                    free_node(r, 2i32);
                }
                r = u;
                if r == 4999999i32 - 9i32 {
                    break;
                }
            }
        }
        MEM[q as usize].b16.s1 = 13_u16;
        MEM[q as usize].b16.s0 = 0_u16;
        MEM[(q + 3) as usize].b32.s1 = 0;
        MEM[(q + 2) as usize].b32.s1 = 0;
        MEM[(q + 5) as usize].b16.s0 = 0_u16;
        MEM[(q + 5) as usize].b16.s1 = 0_u16;
        MEM[(q + 6) as usize].b32.s1 = 0;
        MEM[(q + 4) as usize].b32.s1 = 0;
        q = p;
        if q == TEX_NULL {
            break;
        }
    }
    SAVE_PTR -= 2;
    pack_begin_line = -cur_list.mode_line;
    if cur_list.mode as i32 == -1i32 {
        rule_save = EQTB[(DIMEN_BASE + 16i32) as usize].b32.s1;
        EQTB[(DIMEN_BASE + 16i32) as usize].b32.s1 = 0i32;
        p = hpack(
            MEM[(4999999 - 8) as usize].b32.s1,
            SAVE_STACK[SAVE_PTR + 1].b32.s1,
            SAVE_STACK[SAVE_PTR + 0].b32.s1 as small_number,
        );
        EQTB[(DIMEN_BASE + 16i32) as usize].b32.s1 = rule_save
    } else {
        q = MEM[MEM[(4999999 - 8) as usize].b32.s1 as usize].b32.s1;
        loop {
            MEM[(q + 3) as usize].b32.s1 = MEM[(q + 1) as usize].b32.s1;
            MEM[(q + 1) as usize].b32.s1 = 0;
            q = MEM[MEM[q as usize].b32.s1 as usize].b32.s1;
            if q == TEX_NULL {
                break;
            }
        }
        p = vpackage(
            MEM[(4999999 - 8) as usize].b32.s1,
            SAVE_STACK[SAVE_PTR + 1].b32.s1,
            SAVE_STACK[SAVE_PTR + 0].b32.s1 as small_number,
            0x3fffffffi32,
        );
        q = MEM[MEM[(4999999 - 8) as usize].b32.s1 as usize].b32.s1;
        loop {
            MEM[(q + 1) as usize].b32.s1 = MEM[(q + 3) as usize].b32.s1;
            MEM[(q + 3) as usize].b32.s1 = 0;
            q = MEM[MEM[q as usize].b32.s1 as usize].b32.s1;
            if q == TEX_NULL {
                break;
            }
        }
    }
    pack_begin_line = 0i32;
    q = MEM[cur_list.head as usize].b32.s1;
    s = cur_list.head;
    while q != TEX_NULL {
        if !is_char_node(q) {
            if MEM[q as usize].b16.s1 as i32 == 13 {
                /*836: */
                if cur_list.mode as i32 == -1i32 {
                    MEM[q as usize].b16.s1 = 0_u16;
                    MEM[(q + 1) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1;
                    if (*nest.offset((nest_ptr - 1i32) as isize)).mode as i32 == 207i32 {
                        MEM[q as usize].b16.s0 = 2_u16
                    }
                } else {
                    MEM[q as usize].b16.s1 = 1_u16;
                    MEM[(q + 3) as usize].b32.s1 = MEM[(p + 3) as usize].b32.s1
                }
                MEM[(q + 5) as usize].b16.s0 = MEM[(p + 5) as usize].b16.s0;
                MEM[(q + 5) as usize].b16.s1 = MEM[(p + 5) as usize].b16.s1;
                MEM[(q + 6) as usize].gr = MEM[(p + 6) as usize].gr;
                MEM[(q + 4) as usize].b32.s1 = o;
                r = MEM[MEM[(q + 5) as usize].b32.s1 as usize].b32.s1;
                s = MEM[MEM[(p + 5) as usize].b32.s1 as usize].b32.s1;
                loop {
                    /*837: */
                    n = MEM[r as usize].b16.s0 as i32; /*840: */
                    t = MEM[(s + 1) as usize].b32.s1;
                    w = t;
                    u = 4999999i32 - 4i32;
                    MEM[r as usize].b16.s0 = 0_u16;
                    while n > 0i32 {
                        n -= 1;
                        s = MEM[s as usize].b32.s1;
                        v = MEM[(s + 1) as usize].b32.s0;
                        MEM[u as usize].b32.s1 = new_glue(v);
                        u = MEM[u as usize].b32.s1;
                        MEM[u as usize].b16.s0 = (11 + 1) as u16;
                        t = t + MEM[(v + 1) as usize].b32.s1;
                        if MEM[(p + 5) as usize].b16.s1 as i32 == 1 {
                            if MEM[v as usize].b16.s1 as i32 == MEM[(p + 5) as usize].b16.s0 as i32
                            {
                                t = t + tex_round(
                                    MEM[(p + 6) as usize].gr * MEM[(v + 2) as usize].b32.s1 as f64,
                                )
                            }
                        } else if MEM[(p + 5) as usize].b16.s1 as i32 == 2 {
                            if MEM[v as usize].b16.s0 as i32 == MEM[(p + 5) as usize].b16.s0 as i32
                            {
                                t = t - tex_round(
                                    MEM[(p + 6) as usize].gr * MEM[(v + 3) as usize].b32.s1 as f64,
                                )
                            }
                        }
                        s = MEM[s as usize].b32.s1;
                        MEM[u as usize].b32.s1 = new_null_box();
                        u = MEM[u as usize].b32.s1;
                        t = t + MEM[(s + 1) as usize].b32.s1;
                        if cur_list.mode as i32 == -1i32 {
                            MEM[(u + 1) as usize].b32.s1 = MEM[(s + 1) as usize].b32.s1
                        } else {
                            MEM[u as usize].b16.s1 = 1_u16;
                            MEM[(u + 3) as usize].b32.s1 = MEM[(s + 1) as usize].b32.s1
                        }
                    }
                    if cur_list.mode as i32 == -1i32 {
                        /*839: */
                        MEM[(r + 3) as usize].b32.s1 = MEM[(q + 3) as usize].b32.s1;
                        MEM[(r + 2) as usize].b32.s1 = MEM[(q + 2) as usize].b32.s1;
                        if t == MEM[(r + 1) as usize].b32.s1 {
                            MEM[(r + 5) as usize].b16.s1 = 0_u16;
                            MEM[(r + 5) as usize].b16.s0 = 0_u16;
                            MEM[(r + 6) as usize].gr = 0.0f64
                        } else if t > MEM[(r + 1) as usize].b32.s1 {
                            MEM[(r + 5) as usize].b16.s1 = 1_u16;
                            if MEM[(r + 6) as usize].b32.s1 == 0 {
                                MEM[(r + 6) as usize].gr = 0.0f64
                            } else {
                                MEM[(r + 6) as usize].gr = (t - MEM[(r + 1) as usize].b32.s1) as f64
                                    / MEM[(r + 6) as usize].b32.s1 as f64
                            }
                        } else {
                            MEM[(r + 5) as usize].b16.s0 = MEM[(r + 5) as usize].b16.s1;
                            MEM[(r + 5) as usize].b16.s1 = 2_u16;
                            if MEM[(r + 4) as usize].b32.s1 == 0 {
                                MEM[(r + 6) as usize].gr = 0.0f64
                            } else if MEM[(r + 5) as usize].b16.s0 as i32 == 0
                                && MEM[(r + 1) as usize].b32.s1 - t > MEM[(r + 4) as usize].b32.s1
                            {
                                MEM[(r + 6) as usize].gr = 1.0f64
                            } else {
                                MEM[(r + 6) as usize].gr = (MEM[(r + 1) as usize].b32.s1 - t) as f64
                                    / MEM[(r + 4) as usize].b32.s1 as f64
                            }
                        }
                        MEM[(r + 1) as usize].b32.s1 = w;
                        MEM[r as usize].b16.s1 = 0_u16
                    } else {
                        MEM[(r + 1) as usize].b32.s1 = MEM[(q + 1) as usize].b32.s1;
                        if t == MEM[(r + 3) as usize].b32.s1 {
                            MEM[(r + 5) as usize].b16.s1 = 0_u16;
                            MEM[(r + 5) as usize].b16.s0 = 0_u16;
                            MEM[(r + 6) as usize].gr = 0.0f64
                        } else if t > MEM[(r + 3) as usize].b32.s1 {
                            MEM[(r + 5) as usize].b16.s1 = 1_u16;
                            if MEM[(r + 6) as usize].b32.s1 == 0 {
                                MEM[(r + 6) as usize].gr = 0.0f64
                            } else {
                                MEM[(r + 6) as usize].gr = (t - MEM[(r + 3) as usize].b32.s1) as f64
                                    / MEM[(r + 6) as usize].b32.s1 as f64
                            }
                        } else {
                            MEM[(r + 5) as usize].b16.s0 = MEM[(r + 5) as usize].b16.s1;
                            MEM[(r + 5) as usize].b16.s1 = 2_u16;
                            if MEM[(r + 4) as usize].b32.s1 == 0 {
                                MEM[(r + 6) as usize].gr = 0.0f64
                            } else if MEM[(r + 5) as usize].b16.s0 as i32 == 0
                                && MEM[(r + 3) as usize].b32.s1 - t > MEM[(r + 4) as usize].b32.s1
                            {
                                MEM[(r + 6) as usize].gr = 1.0f64
                            } else {
                                MEM[(r + 6) as usize].gr = (MEM[(r + 3) as usize].b32.s1 - t) as f64
                                    / MEM[(r + 4) as usize].b32.s1 as f64
                            }
                        }
                        MEM[(r + 3) as usize].b32.s1 = w;
                        MEM[r as usize].b16.s1 = 1_u16
                    }
                    MEM[(r + 4) as usize].b32.s1 = 0;
                    if u != 4999999i32 - 4i32 {
                        MEM[u as usize].b32.s1 = MEM[r as usize].b32.s1;
                        MEM[r as usize].b32.s1 = MEM[(4999999 - 4) as usize].b32.s1;
                        r = u
                    }
                    r = MEM[MEM[r as usize].b32.s1 as usize].b32.s1;
                    s = MEM[MEM[s as usize].b32.s1 as usize].b32.s1;
                    if r == TEX_NULL {
                        break;
                    }
                }
            } else if MEM[q as usize].b16.s1 as i32 == 2 {
                /*835: */
                if MEM[(q + 1) as usize].b32.s1 == -0x40000000 {
                    MEM[(q + 1) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1
                }
                if MEM[(q + 3) as usize].b32.s1 == -0x40000000 {
                    MEM[(q + 3) as usize].b32.s1 = MEM[(p + 3) as usize].b32.s1
                }
                if MEM[(q + 2) as usize].b32.s1 == -0x40000000 {
                    MEM[(q + 2) as usize].b32.s1 = MEM[(p + 2) as usize].b32.s1
                }
                if o != 0i32 {
                    r = MEM[q as usize].b32.s1;
                    MEM[q as usize].b32.s1 = TEX_NULL;
                    q = hpack(q, 0i32, 1i32 as small_number);
                    MEM[(q + 4) as usize].b32.s1 = o;
                    MEM[q as usize].b32.s1 = r;
                    MEM[s as usize].b32.s1 = q
                }
            }
        }
        s = q;
        q = MEM[q as usize].b32.s1
    }
    flush_node_list(p);
    pop_alignment();
    aux_save = cur_list.aux;
    p = MEM[cur_list.head as usize].b32.s1;
    q = cur_list.tail;
    pop_nest();
    if cur_list.mode as i32 == 207i32 {
        /*1241: */
        do_assignments(); /*1232: */
        if cur_cmd as i32 != 3i32 {
            /*1242: */
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Missing $$ inserted");
            help_ptr = 2_u8;
            help_line[1] = b"Displays can use special alignments (like \\eqalignno)";
            help_line[0] = b"only if nothing but the alignment itself is between $$\'s.";
            back_error();
        } else {
            get_x_token();
            if cur_cmd as i32 != 3i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Display math should end with $$");
                help_ptr = 2_u8;
                help_line[1] = b"The `$\' that I just saw supposedly matches a previous `$$\'.";
                help_line[0] = b"So I shall assume that you typed `$$\' both times.";
                back_error();
            }
        }
        flush_node_list(cur_list.eTeX_aux);
        pop_nest();
        MEM[cur_list.tail as usize].b32.s1 = new_penalty(EQTB[(INT_BASE + 11i32) as usize].b32.s1);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[cur_list.tail as usize].b32.s1 = new_param_glue(3 as small_number);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[cur_list.tail as usize].b32.s1 = p;
        if p != TEX_NULL {
            cur_list.tail = q
        }
        MEM[cur_list.tail as usize].b32.s1 = new_penalty(EQTB[(INT_BASE + 12i32) as usize].b32.s1);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[cur_list.tail as usize].b32.s1 = new_param_glue(4 as small_number);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        cur_list.aux.b32.s1 = aux_save.b32.s1;
        resume_after_display();
    } else {
        cur_list.aux = aux_save;
        MEM[cur_list.tail as usize].b32.s1 = p;
        if p != TEX_NULL {
            cur_list.tail = q
        }
        if cur_list.mode as i32 == 1i32 {
            build_page();
        }
    };
}
pub(crate) unsafe fn align_peek() {
    loop {
        align_state = 1000000i64 as i32;
        loop {
            get_x_or_protected();
            if cur_cmd as i32 != 10i32 {
                break;
            }
        }
        if cur_cmd as i32 == 34i32 {
            scan_left_brace();
            new_save_level(7i32 as group_code);
            if cur_list.mode as i32 == -1i32 {
                normal_paragraph();
            }
            break;
        } else if cur_cmd as i32 == 2i32 {
            fin_align();
            break;
        } else {
            if cur_cmd as i32 == 5i32 && cur_chr == 0x10ffffi32 + 4i32 {
                continue;
            }
            init_row();
            init_col();
            break;
        }
    }
}
pub(crate) unsafe fn max_hyphenatable_length() -> i32 {
    if EQTB[(INT_BASE + 82i32) as usize].b32.s1 > 4095i32 {
        return 4095i32;
    }
    EQTB[(INT_BASE + 82i32) as usize].b32.s1
}
pub(crate) unsafe fn eTeX_enabled(mut b: bool, mut j: u16, mut k: i32) -> bool {
    if !b {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Improper ");
        print_cmd_chr(j, k);
        help_ptr = 1_u8;
        help_line[0] = b"Sorry, this optional e-TeX feature has been disabled.";
        error();
    }
    b
}
pub(crate) unsafe fn show_save_groups() {
    let mut current_block: u64;
    let mut p: i32 = 0;
    let mut m: i16 = 0;
    let mut v: save_pointer = 0;
    let mut l: u16 = 0;
    let mut c: group_code = 0;
    let mut a: i8 = 0;
    let mut i: i32 = 0;
    let mut j: u16 = 0;
    let mut s: &[u8] = &[];
    p = nest_ptr;
    *nest.offset(p as isize) = cur_list;
    v = SAVE_PTR as i32;
    l = cur_level;
    c = cur_group;
    SAVE_PTR = cur_boundary as usize;
    cur_level = cur_level.wrapping_sub(1);
    a = 1_i8;
    print_nl_cstr(b"");
    print_ln();
    loop {
        print_nl_cstr(b"### ");
        print_group(1i32 != 0);
        if cur_group as i32 == 0i32 {
            break;
        }
        loop {
            m = (*nest.offset(p as isize)).mode;
            if p > 0i32 {
                p -= 1
            } else {
                m = 1_i16
            }
            if !(m as i32 == 104i32) {
                break;
            }
        }
        print_cstr(b" (");
        match cur_group as i32 {
            1 => {
                p += 1;
                current_block = 11054735442240645164;
            }
            2 | 3 => {
                s = b"hbox";
                current_block = 6002151390280567665;
            }
            4 => {
                s = b"vbox";
                current_block = 6002151390280567665;
            }
            5 => {
                s = b"vtop";
                current_block = 6002151390280567665;
            }
            6 => {
                if a as i32 == 0i32 {
                    if m as i32 == -1i32 {
                        s = b"halign"
                    } else {
                        s = b"valign"
                    }
                    a = 1_i8;
                    current_block = 17798259985923180687;
                } else {
                    if a as i32 == 1i32 {
                        print_cstr(b"align entry");
                    } else {
                        print_esc_cstr(b"cr");
                    }
                    if p >= a as i32 {
                        p = p - a as i32
                    }
                    a = 0_i8;
                    current_block = 5407796692416645153;
                }
            }
            7 => {
                p += 1;
                a = -1_i8;
                print_esc_cstr(b"noalign");
                current_block = 11054735442240645164;
            }
            8 => {
                print_esc_cstr(b"output");
                current_block = 5407796692416645153;
            }
            9 => current_block = 11054735442240645164,
            10 | 13 => {
                if cur_group as i32 == 10i32 {
                    print_esc_cstr(b"discretionary");
                } else {
                    print_esc_cstr(b"mathchoice");
                }
                i = 1i32;
                while i <= 3i32 {
                    if i <= SAVE_STACK[SAVE_PTR - 2].b32.s1 {
                        print_cstr(b"{}");
                    }
                    i += 1
                }
                current_block = 11054735442240645164;
            }
            11 => {
                if SAVE_STACK[SAVE_PTR - 2].b32.s1 == 255 {
                    print_esc_cstr(b"vadjust");
                } else {
                    print_esc_cstr(b"insert");
                    print_int(SAVE_STACK[SAVE_PTR - 2].b32.s1);
                }
                current_block = 11054735442240645164;
            }
            12 => {
                s = b"vcenter";
                current_block = 17798259985923180687;
            }
            14 => {
                p += 1;
                print_esc_cstr(b"begingroup");
                current_block = 5407796692416645153;
            }
            15 => {
                if m as i32 == 207i32 {
                    print_char('$' as i32);
                    current_block = 17441561948628420366;
                } else if (*nest.offset(p as isize)).mode as i32 == 207i32 {
                    print_cmd_chr(48_u16, SAVE_STACK[SAVE_PTR - 2].b32.s1);
                    current_block = 5407796692416645153;
                } else {
                    current_block = 17441561948628420366;
                }
                match current_block {
                    5407796692416645153 => {}
                    _ => {
                        print_char('$' as i32);
                        current_block = 5407796692416645153;
                    }
                }
            }
            16 => {
                if MEM[(*nest.offset((p + 1) as isize)).eTeX_aux as usize]
                    .b16
                    .s1 as i32
                    == 30i32
                {
                    print_esc_cstr(b"left");
                } else {
                    print_esc_cstr(b"middle");
                }
                current_block = 5407796692416645153;
            }
            _ => current_block = 6002151390280567665,
        }
        match current_block {
            6002151390280567665 => {
                i = SAVE_STACK[SAVE_PTR - 4].b32.s1;
                if i != 0i32 {
                    if i < 0x40000000i32 {
                        if ((*nest.offset(p as isize)).mode as i32).abs() == 1i32 {
                            j = 21_u16
                        } else {
                            j = 22_u16
                        }
                        if i > 0i32 {
                            print_cmd_chr(j, 0i32);
                        } else {
                            print_cmd_chr(j, 1i32);
                        }
                        print_scaled(i.abs());
                        print_cstr(b"pt");
                    } else if i < 0x40010000i32 {
                        if i >= 0x40008000i32 {
                            print_esc_cstr(b"global");
                            i = i - (0x40008000i32 - 0x40000000i32)
                        }
                        print_esc_cstr(b"setbox");
                        print_int(i - 0x40000000i32);
                        print_char('=' as i32);
                    } else {
                        print_cmd_chr(31_u16, i - (0x40010001i32 - 100i32));
                    }
                }
                current_block = 17798259985923180687;
            }
            _ => {}
        }
        match current_block {
            17798259985923180687 => {
                print_esc_cstr(s);
                if SAVE_STACK[SAVE_PTR - 2].b32.s1 != 0i32 {
                    print_char(' ' as i32);
                    if SAVE_STACK[SAVE_PTR - 3].b32.s1 == 0i32 {
                        print_cstr(b"to");
                    } else {
                        print_cstr(b"spread");
                    }
                    print_scaled(SAVE_STACK[SAVE_PTR - 2].b32.s1);
                    print_cstr(b"pt");
                }
                current_block = 11054735442240645164;
            }
            _ => {}
        }
        match current_block {
            11054735442240645164 => print_char('{' as i32),
            _ => {}
        }
        print_char(')' as i32);
        cur_level = cur_level.wrapping_sub(1);
        cur_group = SAVE_STACK[SAVE_PTR].b16.s0 as group_code;
        SAVE_PTR = SAVE_STACK[SAVE_PTR].b32.s1 as usize
    }
    SAVE_PTR = v as usize;
    cur_level = l;
    cur_group = c;
}
pub(crate) unsafe fn vert_break(mut p: i32, mut h: scaled_t, mut d: scaled_t) -> i32 {
    let mut current_block: u64;
    let mut prev_p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut pi: i32 = 0;
    let mut b: i32 = 0;
    let mut least_cost: i32 = 0;
    let mut best_place: i32 = TEX_NULL;
    let mut prev_dp: scaled_t = 0;
    let mut t: small_number = 0;
    prev_p = p;
    least_cost = 0x3fffffffi32;
    active_width[1] = 0i32;
    active_width[2] = 0i32;
    active_width[3] = 0i32;
    active_width[4] = 0i32;
    active_width[5] = 0i32;
    active_width[6] = 0i32;
    prev_dp = 0i32;
    loop {
        if p == TEX_NULL {
            pi = -10000i32;
            current_block = 9007357115414505193;
        } else {
            /*1008: */
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 | 2 => {
                    current_block = 15992561690600734426; /*:1010 */
                    match current_block {
                        5335814873276400744 => confusion(b"vertbreak"),
                        15992561690600734426 => {
                            active_width[1] =
                                active_width[1] + prev_dp + MEM[(p + 3) as usize].b32.s1;
                            prev_dp = MEM[(p + 2) as usize].b32.s1;
                            current_block = 10249009913728301645;
                        }
                        17919980485942902313 => {
                            if MEM[p as usize].b32.s1 == TEX_NULL {
                                t = 12i32 as small_number
                            } else {
                                t = MEM[MEM[p as usize].b32.s1 as usize].b16.s1 as small_number
                            }
                            if t as i32 == 10i32 {
                                pi = 0i32;
                                current_block = 9007357115414505193;
                            } else {
                                current_block = 11492179201936201469;
                            }
                        }
                        9310447521173000071 => {
                            if MEM[p as usize].b16.s0 as i32 == 43
                                || MEM[p as usize].b16.s0 as i32 == 44
                            {
                                active_width[1] =
                                    active_width[1] + prev_dp + MEM[(p + 3) as usize].b32.s1;
                                prev_dp = MEM[(p + 2) as usize].b32.s1
                            }
                            current_block = 10249009913728301645;
                        }
                        17538459923738996256 => {
                            pi = MEM[(p + 1) as usize].b32.s1;
                            current_block = 9007357115414505193;
                        }
                        _ => {
                            if is_non_discardable_node(prev_p) {
                                pi = 0i32;
                                current_block = 9007357115414505193;
                            } else {
                                current_block = 11492179201936201469;
                            }
                        }
                    }
                }
                8 => {
                    if MEM[p as usize].b16.s0 as i32 == 43 || MEM[p as usize].b16.s0 as i32 == 44 {
                        active_width[1] = active_width[1] + prev_dp + MEM[(p + 3) as usize].b32.s1;
                        prev_dp = MEM[(p + 2) as usize].b32.s1
                    }
                    current_block = 10249009913728301645;
                }
                10 => {
                    if is_non_discardable_node(prev_p) {
                        pi = 0i32;
                        current_block = 9007357115414505193;
                    } else {
                        current_block = 11492179201936201469;
                    }
                }
                11 => {
                    if MEM[p as usize].b32.s1 == TEX_NULL {
                        t = 12i32 as small_number
                    } else {
                        t = MEM[MEM[p as usize].b32.s1 as usize].b16.s1 as small_number
                    }
                    if t as i32 == 10i32 {
                        pi = 0i32;
                        current_block = 9007357115414505193;
                    } else {
                        current_block = 11492179201936201469;
                    }
                }
                12 => {
                    pi = MEM[(p + 1) as usize].b32.s1;
                    current_block = 9007357115414505193;
                }
                4 | 3 => current_block = 10249009913728301645,
                _ => {
                    current_block = 5335814873276400744;
                    confusion(b"vertbreak");
                }
            }
        }
        match current_block {
            9007357115414505193 => {
                if pi < 10000i32 {
                    if active_width[1] < h {
                        if active_width[3] != 0i32
                            || active_width[4] != 0i32
                            || active_width[5] != 0i32
                        {
                            b = 0i32
                        } else {
                            b = badness(h - active_width[1], active_width[2])
                        }
                    } else if active_width[1] - h > active_width[6] {
                        b = 0x3fffffffi32
                    } else {
                        b = badness(active_width[1] - h, active_width[6])
                    }
                    if b < 0x3fffffffi32 {
                        if pi <= -10000i32 {
                            b = pi
                        } else if b < 10000i32 {
                            b = b + pi
                        } else {
                            b = 100000i64 as i32
                        }
                    }
                    if b <= least_cost {
                        best_place = p;
                        least_cost = b;
                        best_height_plus_depth = active_width[1] + prev_dp
                    }
                    if b == 0x3fffffffi32 || pi <= -10000i32 {
                        break;
                    }
                }
                if (MEM[p as usize].b16.s1 as i32) < 10 || MEM[p as usize].b16.s1 as i32 > 11 {
                    current_block = 10249009913728301645;
                } else {
                    current_block = 11492179201936201469;
                }
            }
            _ => {}
        }
        match current_block {
            11492179201936201469 => {
                /*update_heights *//*1011: */
                if MEM[p as usize].b16.s1 as i32 == 11 {
                    q = p
                } else {
                    q = MEM[(p + 1) as usize].b32.s0; /*:1011 */
                    active_width[(2i32 + MEM[q as usize].b16.s1 as i32) as usize] = active_width
                        [(2i32 + MEM[q as usize].b16.s1 as i32) as usize]
                        + MEM[(q + 2) as usize].b32.s1; /*:1014*/
                    active_width[6] = active_width[6] + MEM[(q + 3) as usize].b32.s1;
                    if MEM[q as usize].b16.s0 as i32 != 0 && MEM[(q + 3) as usize].b32.s1 != 0 {
                        if file_line_error_style_p != 0 {
                            print_file_line();
                        } else {
                            print_nl_cstr(b"! ");
                        }
                        print_cstr(b"Infinite glue shrinkage found in box being split");
                        help_ptr = 4_u8;
                        help_line[3] = b"The box you are \\vsplitting contains some infinitely";
                        help_line[2] =
                            b"shrinkable glue, e.g., `\\vss\' or `\\vskip 0pt minus 1fil\'.";
                        help_line[1] =
                            b"Such glue doesn\'t belong there; but you can safely proceed,";
                        help_line[0] = b"since the offensive shrinkability has been made finite.";
                        error();
                        r = new_spec(q);
                        MEM[r as usize].b16.s0 = 0_u16;
                        delete_glue_ref(q);
                        MEM[(p + 1) as usize].b32.s0 = r;
                        q = r
                    }
                }
                active_width[1] = active_width[1] + prev_dp + MEM[(q + 1) as usize].b32.s1;
                prev_dp = 0i32
            }
            _ => {}
        }
        if prev_dp > d {
            active_width[1] = active_width[1] + prev_dp - d;
            prev_dp = d
        }
        prev_p = p;
        p = MEM[prev_p as usize].b32.s1
    }
    best_place
}
pub(crate) unsafe fn vsplit(mut n: i32, mut h: scaled_t) -> i32 {
    let mut v: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    cur_val = n;
    if cur_val < 256i32 {
        v = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
    } else {
        find_sa_element(4i32 as small_number, cur_val, false);
        if cur_ptr == TEX_NULL {
            v = TEX_NULL
        } else {
            v = MEM[(cur_ptr + 1) as usize].b32.s1
        }
    }
    flush_node_list(disc_ptr[3]);
    disc_ptr[3] = TEX_NULL;
    if sa_root[7] != TEX_NULL {
        if do_marks(0i32 as small_number, 0i32 as small_number, sa_root[7]) {
            sa_root[7] = TEX_NULL
        }
    }
    if cur_mark[3] != TEX_NULL {
        delete_token_ref(cur_mark[3]);
        cur_mark[3] = TEX_NULL;
        delete_token_ref(cur_mark[4]);
        cur_mark[4] = TEX_NULL
    }
    if v == TEX_NULL {
        return TEX_NULL;
    }
    if MEM[v as usize].b16.s1 as i32 != 1 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"");
        print_esc_cstr(b"vsplit");
        print_cstr(b" needs a ");
        print_esc_cstr(b"vbox");
        help_ptr = 2_u8;
        help_line[1] = b"The box you are trying to split is an \\hbox.";
        help_line[0] = b"I can\'t split such a box, so I\'ll leave it alone.";
        error();
        return TEX_NULL;
    }
    q = vert_break(
        MEM[(v + 5) as usize].b32.s1,
        h,
        EQTB[(DIMEN_BASE + 6i32) as usize].b32.s1,
    );
    p = MEM[(v + 5) as usize].b32.s1;
    if p == q {
        MEM[(v + 5) as usize].b32.s1 = TEX_NULL
    } else {
        loop {
            if MEM[p as usize].b16.s1 as i32 == 4 {
                if MEM[(p + 1) as usize].b32.s0 != 0 {
                    /*1615: */
                    find_sa_element(7i32 as small_number, MEM[(p + 1) as usize].b32.s0, true);
                    if MEM[(cur_ptr + 2) as usize].b32.s1 == TEX_NULL {
                        MEM[(cur_ptr + 2) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1;
                        MEM[MEM[(p + 1) as usize].b32.s1 as usize].b32.s0 += 1
                    } else {
                        delete_token_ref(MEM[(cur_ptr + 3) as usize].b32.s0);
                    }
                    MEM[(cur_ptr + 3) as usize].b32.s0 = MEM[(p + 1) as usize].b32.s1;
                    MEM[MEM[(p + 1) as usize].b32.s1 as usize].b32.s0 += 1;
                } else if cur_mark[3] == TEX_NULL {
                    cur_mark[3] = MEM[(p + 1) as usize].b32.s1;
                    cur_mark[4] = cur_mark[3];
                    MEM[cur_mark[3] as usize].b32.s0 = MEM[cur_mark[3] as usize].b32.s0 + 2
                } else {
                    delete_token_ref(cur_mark[4]);
                    cur_mark[4] = MEM[(p + 1) as usize].b32.s1;
                    MEM[cur_mark[4] as usize].b32.s0 += 1;
                }
            }
            if MEM[p as usize].b32.s1 == q {
                MEM[p as usize].b32.s1 = TEX_NULL;
                break;
            } else {
                p = MEM[p as usize].b32.s1
            }
        }
    }
    q = prune_page_top(q, EQTB[(INT_BASE + 65i32) as usize].b32.s1 > 0i32);
    p = MEM[(v + 5) as usize].b32.s1;
    free_node(v, 8i32);
    if q != TEX_NULL {
        q = vpackage(q, 0i32, 1i32 as small_number, 0x3fffffffi32)
    }
    if cur_val < 256i32 {
        EQTB[(BOX_BASE + cur_val) as usize].b32.s1 = q
    } else {
        find_sa_element(4i32 as small_number, cur_val, false);
        if cur_ptr != TEX_NULL {
            MEM[(cur_ptr + 1) as usize].b32.s1 = q;
            MEM[(cur_ptr + 1) as usize].b32.s0 += 1;
            delete_sa_ref(cur_ptr);
        }
    }
    vpackage(
        p,
        h,
        0i32 as small_number,
        EQTB[(DIMEN_BASE + 6i32) as usize].b32.s1,
    )
}
pub(crate) unsafe fn print_totals() {
    print_scaled(page_so_far[1]);
    if page_so_far[2] != 0i32 {
        print_cstr(b" plus ");
        print_scaled(page_so_far[2]);
        print_cstr(b"");
    }
    if page_so_far[3] != 0i32 {
        print_cstr(b" plus ");
        print_scaled(page_so_far[3]);
        print_cstr(b"fil");
    }
    if page_so_far[4] != 0i32 {
        print_cstr(b" plus ");
        print_scaled(page_so_far[4]);
        print_cstr(b"fill");
    }
    if page_so_far[5] != 0i32 {
        print_cstr(b" plus ");
        print_scaled(page_so_far[5]);
        print_cstr(b"filll");
    }
    if page_so_far[6] != 0i32 {
        print_cstr(b" minus ");
        print_scaled(page_so_far[6]);
    };
}
pub(crate) unsafe fn box_error(mut n: eight_bits) {
    error();
    begin_diagnostic();
    print_nl_cstr(b"The following box has been deleted:");
    show_box(EQTB[(BOX_BASE + n as i32) as usize].b32.s1);
    end_diagnostic(1i32 != 0);
    flush_node_list(EQTB[(BOX_BASE + n as i32) as usize].b32.s1);
    EQTB[(BOX_BASE + n as i32) as usize].b32.s1 = TEX_NULL;
}
pub(crate) unsafe fn app_space() {
    let mut q: i32 = 0;
    if cur_list.aux.b32.s0 >= 2000i32 && EQTB[(GLUE_BASE + 13i32) as usize].b32.s1 != 0i32 {
        q = new_param_glue(13i32 as small_number)
    } else {
        if EQTB[(GLUE_BASE + 12i32) as usize].b32.s1 != 0i32 {
            main_p = EQTB[(GLUE_BASE + 12i32) as usize].b32.s1
        } else {
            /*1077: */
            main_p = FONT_GLUE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize]; /*:1079 */
            if main_p == TEX_NULL {
                main_p = new_spec(0i32);
                main_k = PARAM_BASE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] + 2;
                MEM[(main_p + 1) as usize].b32.s1 = FONT_INFO[main_k as usize].b32.s1;
                MEM[(main_p + 2) as usize].b32.s1 = FONT_INFO[(main_k + 1i32) as usize].b32.s1;
                MEM[(main_p + 3) as usize].b32.s1 = FONT_INFO[(main_k + 2i32) as usize].b32.s1;
                FONT_GLUE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] = main_p
            }
        }
        main_p = new_spec(main_p);
        if cur_list.aux.b32.s0 >= 2000i32 {
            MEM[(main_p + 1) as usize].b32.s1 = MEM[(main_p + 1) as usize].b32.s1
                + FONT_INFO
                    [(7 + PARAM_BASE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize]) as usize]
                    .b32
                    .s1
        }
        MEM[(main_p + 2) as usize].b32.s1 = xn_over_d(
            MEM[(main_p + 2) as usize].b32.s1,
            cur_list.aux.b32.s0,
            1000i32,
        );
        MEM[(main_p + 3) as usize].b32.s1 = xn_over_d(
            MEM[(main_p + 3) as usize].b32.s1,
            1000i32,
            cur_list.aux.b32.s0,
        );
        q = new_glue(main_p);
        MEM[main_p as usize].b32.s1 = TEX_NULL
    }
    MEM[cur_list.tail as usize].b32.s1 = q;
    cur_list.tail = q;
}
pub(crate) unsafe fn insert_dollar_sign() {
    back_input();
    cur_tok = 0x600000i32 + 36i32;
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Missing $ inserted");
    help_ptr = 2_u8;
    help_line[1] = b"I\'ve inserted a begin-math/end-math symbol since I think";
    help_line[0] = b"you left one out. Proceed, with fingers crossed.";
    ins_error();
}
pub(crate) unsafe fn you_cant() {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"You can\'t use `");
    print_cmd_chr(cur_cmd as u16, cur_chr);
    print_in_mode(cur_list.mode as i32);
}
pub(crate) unsafe fn report_illegal_case() {
    you_cant();
    help_ptr = 4_u8;
    help_line[3] = b"Sorry, but I\'m not programmed to handle this case;";
    help_line[2] = b"I\'ll just pretend that you didn\'t ask for it.";
    help_line[1] = b"If you\'re in the wrong mode, you might be able to";
    help_line[0] = b"return to the right one by typing `I}\' or `I$\' or `I\\par\'.";
    error();
}
pub(crate) unsafe fn privileged() -> bool {
    if cur_list.mode as i32 > 0i32 {
        true
    } else {
        report_illegal_case();
        false
    }
}
pub(crate) unsafe fn its_all_over() -> bool {
    if privileged() {
        if 4999999i32 - 2i32 == page_tail && cur_list.head == cur_list.tail && dead_cycles == 0i32 {
            return true;
        }
        back_input();
        MEM[cur_list.tail as usize].b32.s1 = new_null_box();
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[(cur_list.tail + 1) as usize].b32.s1 = EQTB[(DIMEN_BASE + 3i32) as usize].b32.s1;
        MEM[cur_list.tail as usize].b32.s1 = new_glue(8);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[cur_list.tail as usize].b32.s1 = new_penalty(-0x40000000);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        build_page();
    }
    false
}
pub(crate) unsafe fn append_glue() {
    let mut s: small_number = 0;
    s = cur_chr as small_number;
    match s as i32 {
        0 => cur_val = 4i32,
        1 => cur_val = 8i32,
        2 => cur_val = 12i32,
        3 => cur_val = 16i32,
        4 => scan_glue(2i32 as small_number),
        5 => scan_glue(3i32 as small_number),
        _ => {}
    }
    MEM[cur_list.tail as usize].b32.s1 = new_glue(cur_val);
    cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
    if s as i32 >= 4i32 {
        MEM[cur_val as usize].b32.s1 -= 1;
        if s as i32 > 4i32 {
            MEM[cur_list.tail as usize].b16.s0 = 99_u16
        }
    };
}
pub(crate) unsafe fn append_kern() {
    let mut s: u16 = 0;
    s = cur_chr as u16;
    scan_dimen(s as i32 == 99i32, false, false);
    MEM[cur_list.tail as usize].b32.s1 = new_kern(cur_val);
    cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
    MEM[cur_list.tail as usize].b16.s0 = s;
}
pub(crate) unsafe fn off_save() {
    let mut p: i32 = 0;
    if cur_group as i32 == 0i32 {
        /*1101:*/
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Extra ");
        print_cmd_chr(cur_cmd as u16, cur_chr);
        help_ptr = 1_u8;
        help_line[0] = b"Things are pretty mixed up, but I think the worst is over.";
        error();
    } else {
        back_input();
        p = get_avail();
        MEM[(4999999 - 3) as usize].b32.s1 = p;
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Missing ");
        match cur_group as i32 {
            14 => {
                MEM[p as usize].b32.s0 = 0x1ffffff + (FROZEN_CONTROL_SEQUENCE + 2i32);
                print_esc_cstr(b"endgroup");
            }
            15 => {
                MEM[p as usize].b32.s0 = 0x600000 + '$' as i32;
                print_char('$' as i32);
            }
            16 => {
                MEM[p as usize].b32.s0 = 0x1ffffff + (FROZEN_CONTROL_SEQUENCE + 3i32);
                MEM[p as usize].b32.s1 = get_avail();
                p = MEM[p as usize].b32.s1;
                MEM[p as usize].b32.s0 = 0x1800000 + '.' as i32;
                print_esc_cstr(b"right.");
            }
            _ => {
                MEM[p as usize].b32.s0 = 0x400000 + '}' as i32;
                print_char('}' as i32);
            }
        }
        print_cstr(b" inserted");
        begin_token_list(MEM[(4999999 - 3) as usize].b32.s1, 5_u16);
        help_ptr = 5_u8;
        help_line[4] = b"I\'ve inserted something that you may have forgotten.";
        help_line[3] = b"(See the <inserted text> above.)";
        help_line[2] = b"With luck, this will get me unwedged. But if you";
        help_line[1] = b"really didn\'t forget anything, try typing `2\' now; then";
        help_line[0] = b"my insertion and my current dilemma will both disappear.";
        error();
    };
}
pub(crate) unsafe fn extra_right_brace() {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Extra }, or forgotten ");
    match cur_group as i32 {
        14 => print_esc_cstr(b"endgroup"),
        15 => print_char('$' as i32),
        16 => print_esc_cstr(b"right"),
        _ => {}
    }
    help_ptr = 5_u8;
    help_line[4] = b"I\'ve deleted a group-closing symbol because it seems to be";
    help_line[3] = b"spurious, as in `$x}$\'. But perhaps the } is legitimate and";
    help_line[2] = b"you forgot something else, as in `\\hbox{$x}\'. In such cases";
    help_line[1] = b"the way to recover is to insert both the forgotten and the";
    help_line[0] = b"deleted material, e.g., by typing `I$}\'.";
    error();
    align_state += 1;
}
pub(crate) unsafe fn normal_paragraph() {
    if EQTB[(INT_BASE + 19i32) as usize].b32.s1 != 0i32 {
        eq_word_define(INT_BASE + 19i32, 0i32);
    }
    if EQTB[(DIMEN_BASE + 17i32) as usize].b32.s1 != 0i32 {
        eq_word_define(DIMEN_BASE + 17i32, 0i32);
    }
    if EQTB[(INT_BASE + 41i32) as usize].b32.s1 != 1i32 {
        eq_word_define(INT_BASE + 41i32, 1i32);
    }
    if EQTB[(LOCAL_BASE + 0i32) as usize].b32.s1 != TEX_NULL {
        eq_define(
            1i32 + (0x10ffffi32 + 1i32)
                + (0x10ffffi32 + 1i32)
                + 1i32
                + 15000i32
                + 12i32
                + 9000i32
                + 1i32
                + 1i32
                + 19i32
                + 256i32
                + 256i32
                + 0i32,
            120_u16,
            TEX_NULL,
        );
    }
    if EQTB[(ETEX_PEN_BASE + 0i32) as usize].b32.s1 != TEX_NULL {
        eq_define(
            1i32 + (0x10ffffi32 + 1i32)
                + (0x10ffffi32 + 1i32)
                + 1i32
                + 15000i32
                + 12i32
                + 9000i32
                + 1i32
                + 1i32
                + 19i32
                + 256i32
                + 256i32
                + 13i32
                + 256i32
                + 0i32,
            120_u16,
            TEX_NULL,
        );
    };
}
/*1110: "The box_end procedure does the right thing with cur_box, if
 * box_context represents the context as explained [as follows]." The
 * box_context is one of (1) a signed shift amount; (2) BOX_FLAG+N, signifying
 * a `\setbox<N>`; (3) GLOBAL_BOX_FLAG+N, signifying `\global\setbox<N>`; (4)
 * SHIP_OUT_FLAG, signifying `\shipout`; or (5) LEADER_FLAG+k, signifying (in
 * order) `\leaders`, `\cleaders`, or `\xleaders`. */
pub(crate) unsafe fn box_end(mut box_context: i32) {
    let mut p: i32 = 0;
    let mut a: small_number = 0;
    if box_context < 0x40000000i32 {
        /*1111:*/
        if cur_box != TEX_NULL {
            MEM[(cur_box + 4) as usize].b32.s1 = box_context;
            if (cur_list.mode as i32).abs() == 1i32 {
                if pre_adjust_tail != TEX_NULL {
                    if 4999999i32 - 14i32 != pre_adjust_tail {
                        MEM[cur_list.tail as usize].b32.s1 = MEM[(4999999 - 14) as usize].b32.s1;
                        cur_list.tail = pre_adjust_tail
                    }
                    pre_adjust_tail = TEX_NULL
                }
                append_to_vlist(cur_box);
                if adjust_tail != TEX_NULL {
                    if 4999999i32 - 5i32 != adjust_tail {
                        MEM[cur_list.tail as usize].b32.s1 = MEM[(4999999 - 5) as usize].b32.s1;
                        cur_list.tail = adjust_tail
                    }
                    adjust_tail = TEX_NULL
                }
                if cur_list.mode as i32 > 0i32 {
                    build_page();
                }
            } else {
                if (cur_list.mode as i32).abs() == 104i32 {
                    cur_list.aux.b32.s0 = 1000i32
                } else {
                    p = new_noad();
                    MEM[(p + 1) as usize].b32.s1 = 2;
                    MEM[(p + 1) as usize].b32.s0 = cur_box;
                    cur_box = p
                }
                MEM[cur_list.tail as usize].b32.s1 = cur_box;
                cur_list.tail = cur_box
            }
        }
    } else if box_context < 0x40010000i32 {
        /*1112:*/
        if box_context < 0x40008000i32 {
            cur_val = box_context - 0x40000000i32;
            a = 0i32 as small_number
        } else {
            cur_val = box_context - 0x40008000i32;
            a = 4i32 as small_number
        }
        if cur_val < 256i32 {
            if a as i32 >= 4i32 {
                geq_define(
                    1i32 + (0x10ffffi32 + 1i32)
                        + (0x10ffffi32 + 1i32)
                        + 1i32
                        + 15000i32
                        + 12i32
                        + 9000i32
                        + 1i32
                        + 1i32
                        + 19i32
                        + 256i32
                        + 256i32
                        + 13i32
                        + 256i32
                        + 4i32
                        + cur_val,
                    121_u16,
                    cur_box,
                );
            } else {
                eq_define(
                    1i32 + (0x10ffffi32 + 1i32)
                        + (0x10ffffi32 + 1i32)
                        + 1i32
                        + 15000i32
                        + 12i32
                        + 9000i32
                        + 1i32
                        + 1i32
                        + 19i32
                        + 256i32
                        + 256i32
                        + 13i32
                        + 256i32
                        + 4i32
                        + cur_val,
                    121_u16,
                    cur_box,
                );
            }
        } else {
            find_sa_element(4i32 as small_number, cur_val, true);
            if a as i32 >= 4i32 {
                gsa_def(cur_ptr, cur_box);
            } else {
                sa_def(cur_ptr, cur_box);
            }
        }
    } else if cur_box != TEX_NULL {
        if box_context > 0x40010000i32 {
            loop
            /*1113:*/
            {
                get_x_token();
                if !(cur_cmd as i32 == 10i32 || cur_cmd as i32 == 0i32) {
                    break;
                }
            }
            if cur_cmd as i32 == 26i32 && (cur_list.mode as i32).abs() != 1i32
                || cur_cmd as i32 == 27i32 && (cur_list.mode as i32).abs() == 1i32
            {
                append_glue();
                MEM[cur_list.tail as usize].b16.s0 =
                    (box_context - (0x40010001i32 - 100i32)) as u16;
                MEM[(cur_list.tail + 1) as usize].b32.s1 = cur_box
            } else {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Leaders not followed by proper glue");
                help_ptr = 3_u8;
                help_line[2] = b"You should say `\\leaders <box or rule><hskip or vskip>\'.";
                help_line[1] = b"I found the <box or rule>, but there\'s no suitable";
                help_line[0] = b"<hskip or vskip>, so I\'m ignoring these leaders.";
                back_error();
                flush_node_list(cur_box);
            }
        } else {
            ship_out(cur_box);
        }
    };
}
pub(crate) unsafe fn begin_box(mut box_context: i32) {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut fm: bool = false;
    let mut tx: i32 = 0;
    let mut m: u16 = 0;
    let mut k: i32 = 0;
    let mut n: i32 = 0;
    match cur_chr {
        0 => {
            scan_register_num();
            if cur_val < 256i32 {
                cur_box = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr == TEX_NULL {
                    cur_box = TEX_NULL
                } else {
                    cur_box = MEM[(cur_ptr + 1) as usize].b32.s1
                }
            }
            if cur_val < 256i32 {
                EQTB[(BOX_BASE + cur_val) as usize].b32.s1 = TEX_NULL
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr != TEX_NULL {
                    MEM[(cur_ptr + 1) as usize].b32.s1 = TEX_NULL;
                    MEM[(cur_ptr + 1) as usize].b32.s0 += 1;
                    delete_sa_ref(cur_ptr);
                }
            }
        }
        1 => {
            scan_register_num();
            if cur_val < 256i32 {
                q = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr == TEX_NULL {
                    q = TEX_NULL
                } else {
                    q = MEM[(cur_ptr + 1) as usize].b32.s1
                }
            }
            cur_box = copy_node_list(q)
        }
        2 => {
            cur_box = TEX_NULL;
            if (cur_list.mode as i32).abs() == 207i32 {
                you_cant();
                help_ptr = 1_u8;
                help_line[0] = b"Sorry; this \\lastbox will be void.";
                error();
            } else if cur_list.mode as i32 == 1i32 && cur_list.head == cur_list.tail {
                you_cant();
                help_ptr = 2_u8;
                help_line[1] = b"Sorry...I usually can\'t take things from the current page.";
                help_line[0] = b"This \\lastbox will therefore be void.";
                error();
            } else {
                let mut current_block_79: u64;
                tx = cur_list.tail;
                if tx < hi_mem_min {
                    if MEM[tx as usize].b16.s1 as i32 == 9 && MEM[tx as usize].b16.s0 as i32 == 3 {
                        r = cur_list.head;
                        loop {
                            q = r;
                            r = MEM[q as usize].b32.s1;
                            if !(r != tx) {
                                break;
                            }
                        }
                        tx = q
                    }
                }
                if tx < hi_mem_min {
                    if MEM[tx as usize].b16.s1 as i32 == 0 || MEM[tx as usize].b16.s1 as i32 == 1 {
                        /*1116:*/
                        q = cur_list.head;
                        p = TEX_NULL;
                        loop {
                            r = p;
                            p = q;
                            fm = false;
                            if q < hi_mem_min {
                                if MEM[q as usize].b16.s1 as i32 == 7 {
                                    m = 1_u16;
                                    while m as i32 <= MEM[q as usize].b16.s0 as i32 {
                                        p = MEM[p as usize].b32.s1;
                                        m = m.wrapping_add(1)
                                    }
                                    if p == tx {
                                        current_block_79 = 1209030638129645089;
                                        break;
                                    }
                                } else if MEM[q as usize].b16.s1 as i32 == 9
                                    && MEM[q as usize].b16.s0 as i32 == 2
                                {
                                    fm = true
                                }
                            }
                            q = MEM[p as usize].b32.s1;
                            if !(q != tx) {
                                current_block_79 = 12961834331865314435;
                                break;
                            }
                        }
                        match current_block_79 {
                            1209030638129645089 => {}
                            _ => {
                                q = MEM[tx as usize].b32.s1;
                                MEM[p as usize].b32.s1 = q;
                                MEM[tx as usize].b32.s1 = TEX_NULL;
                                if q == TEX_NULL {
                                    if fm {
                                        confusion(b"tail1");
                                    } else {
                                        cur_list.tail = p
                                    }
                                } else if fm {
                                    cur_list.tail = r;
                                    MEM[r as usize].b32.s1 = TEX_NULL;
                                    flush_node_list(p);
                                }
                                cur_box = tx;
                                MEM[(cur_box + 4) as usize].b32.s1 = 0
                            }
                        }
                    }
                }
            }
        }
        3 => {
            scan_register_num();
            n = cur_val;
            if !scan_keyword(b"to") {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Missing `to\' inserted");
                help_ptr = 2_u8;
                help_line[1] = b"I\'m working on `\\vsplit<box number> to <dimen>\';";
                help_line[0] = b"will look for the <dimen> next.";
                error();
            }
            scan_dimen(false, false, false);
            cur_box = vsplit(n, cur_val)
        }
        _ => {
            k = cur_chr - 4i32;
            SAVE_STACK[SAVE_PTR + 0].b32.s1 = box_context;
            if k == 104i32 {
                if box_context < 0x40000000i32 && (cur_list.mode as i32).abs() == 1i32 {
                    scan_spec(3i32 as group_code, true);
                } else {
                    scan_spec(2i32 as group_code, true);
                }
            } else {
                if k == 1i32 {
                    scan_spec(4i32 as group_code, true);
                } else {
                    scan_spec(5i32 as group_code, true);
                    k = 1i32
                }
                normal_paragraph();
            }
            push_nest();
            cur_list.mode = -k as i16;
            if k == 1i32 {
                cur_list.aux.b32.s1 = -65536000i32;
                if EQTB[(LOCAL_BASE + 6i32) as usize].b32.s1 != TEX_NULL {
                    begin_token_list(EQTB[(LOCAL_BASE + 6i32) as usize].b32.s1, 12_u16);
                }
            } else {
                cur_list.aux.b32.s0 = 1000i32;
                if EQTB[(LOCAL_BASE + 5i32) as usize].b32.s1 != TEX_NULL {
                    begin_token_list(EQTB[(LOCAL_BASE + 5i32) as usize].b32.s1, 11_u16);
                }
            }
            return;
        }
    }
    box_end(box_context);
}
pub(crate) unsafe fn scan_box(mut box_context: i32) {
    loop {
        get_x_token();
        if !(cur_cmd as i32 == 10i32 || cur_cmd as i32 == 0i32) {
            break;
        }
    }
    if cur_cmd as i32 == 20i32 {
        begin_box(box_context);
    } else if box_context >= 0x40010001i32 && (cur_cmd as i32 == 36i32 || cur_cmd as i32 == 35i32) {
        cur_box = scan_rule_spec();
        box_end(box_context);
    } else {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"A <box> was supposed to be here");
        help_ptr = 3_u8;
        help_line[2] = b"I was expecting to see \\hbox or \\vbox or \\copy or \\box or";
        help_line[1] = b"something like that. So you might find something missing in";
        help_line[0] = b"your output. But keep trying; you can fix this later.";
        back_error();
    };
}
pub(crate) unsafe fn package(mut c: small_number) {
    let mut h: scaled_t = 0;
    let mut p: i32 = 0;
    let mut d: scaled_t = 0;
    let mut u: i32 = 0;
    let mut v: i32 = 0;
    d = EQTB[(DIMEN_BASE + 7i32) as usize].b32.s1;
    u = EQTB[(INT_BASE + 73i32) as usize].b32.s1;
    unsave();
    SAVE_PTR -= 3;
    v = EQTB[(INT_BASE + 73i32) as usize].b32.s1;
    EQTB[(INT_BASE + 73i32) as usize].b32.s1 = u;
    if cur_list.mode as i32 == -104i32 {
        cur_box = hpack(
            MEM[cur_list.head as usize].b32.s1,
            SAVE_STACK[SAVE_PTR + 2].b32.s1,
            SAVE_STACK[SAVE_PTR + 1].b32.s1 as small_number,
        )
    } else {
        cur_box = vpackage(
            MEM[cur_list.head as usize].b32.s1,
            SAVE_STACK[SAVE_PTR + 2].b32.s1,
            SAVE_STACK[SAVE_PTR + 1].b32.s1 as small_number,
            d,
        );
        if c as i32 == 4i32 {
            /*1122: */
            h = 0i32;
            p = MEM[(cur_box + 5) as usize].b32.s1;
            if p != TEX_NULL {
                if MEM[p as usize].b16.s1 as i32 <= 2 {
                    h = MEM[(p + 3) as usize].b32.s1
                }
            }
            MEM[(cur_box + 2) as usize].b32.s1 =
                MEM[(cur_box + 2) as usize].b32.s1 - h + MEM[(cur_box + 3) as usize].b32.s1;
            MEM[(cur_box + 3) as usize].b32.s1 = h
        }
    }
    EQTB[(INT_BASE + 73i32) as usize].b32.s1 = v;
    pop_nest();
    box_end(SAVE_STACK[SAVE_PTR + 0].b32.s1);
}
pub(crate) unsafe fn norm_min(mut h: i32) -> small_number {
    (if h <= 0 {
        1
    } else if h >= 63i32 {
        63
    } else {
        h
    }) as small_number
}
pub(crate) unsafe fn new_graf(mut indented: bool) {
    cur_list.prev_graf = 0i32;
    if cur_list.mode as i32 == 1i32 || cur_list.head != cur_list.tail {
        MEM[cur_list.tail as usize].b32.s1 = new_param_glue(2 as small_number);
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1
    }
    push_nest();
    cur_list.mode = 104_i16;
    cur_list.aux.b32.s0 = 1000i32;
    if EQTB[(INT_BASE + 50i32) as usize].b32.s1 <= 0i32 {
        cur_lang = 0_u8
    } else if EQTB[(INT_BASE + 50i32) as usize].b32.s1 > 255i32 {
        cur_lang = 0_u8
    } else {
        cur_lang = EQTB[(INT_BASE + 50i32) as usize].b32.s1 as u8
    }
    cur_list.aux.b32.s1 = cur_lang as i32;
    cur_list.prev_graf = ((norm_min(EQTB[(INT_BASE + 51i32) as usize].b32.s1) as i32 * 64i32
        + norm_min(EQTB[(INT_BASE + 52i32) as usize].b32.s1) as i32)
        as i64
        * 65536
        + cur_lang as i64) as i32;
    if indented {
        cur_list.tail = new_null_box();
        MEM[cur_list.head as usize].b32.s1 = cur_list.tail;
        MEM[(cur_list.tail + 1) as usize].b32.s1 = EQTB[(DIMEN_BASE) as usize].b32.s1;
        if insert_src_special_every_par {
            insert_src_special();
        }
    }
    if EQTB[(LOCAL_BASE + 2i32) as usize].b32.s1 != TEX_NULL {
        begin_token_list(EQTB[(LOCAL_BASE + 2i32) as usize].b32.s1, 8_u16);
    }
    if nest_ptr == 1i32 {
        build_page();
    };
}
pub(crate) unsafe fn indent_in_hmode() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    if cur_chr > 0i32 {
        p = new_null_box();
        MEM[(p + 1) as usize].b32.s1 = EQTB[(DIMEN_BASE) as usize].b32.s1;
        if (cur_list.mode as i32).abs() == 104i32 {
            cur_list.aux.b32.s0 = 1000i32
        } else {
            q = new_noad();
            MEM[(q + 1) as usize].b32.s1 = 2;
            MEM[(q + 1) as usize].b32.s0 = p;
            p = q
        }
        MEM[cur_list.tail as usize].b32.s1 = p;
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1
    };
}
pub(crate) unsafe fn head_for_vmode() {
    if (cur_list.mode as i32) < 0i32 {
        if cur_cmd as i32 != 36i32 {
            off_save();
        } else {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"You can\'t use `");
            print_esc_cstr(b"hrule");
            print_cstr(b"\' here except with leaders");
            help_ptr = 2_u8;
            help_line[1] = b"To put a horizontal rule in an hbox or an alignment,";
            help_line[0] = b"you should use \\leaders or \\hrulefill (see The TeXbook).";
            error();
        }
    } else {
        back_input();
        cur_tok = par_token;
        back_input();
        cur_input.index = 5_u16
    };
}
pub(crate) unsafe fn end_graf() {
    if cur_list.mode as i32 == 104i32 {
        if cur_list.head == cur_list.tail {
            pop_nest();
        } else {
            line_break(false);
        }
        if cur_list.eTeX_aux != TEX_NULL {
            flush_list(cur_list.eTeX_aux);
            cur_list.eTeX_aux = TEX_NULL
        }
        normal_paragraph();
        error_count = 0_i8
    };
}
pub(crate) unsafe fn begin_insert_or_adjust() {
    if cur_cmd as i32 == 38i32 {
        cur_val = 255i32
    } else {
        scan_eight_bit_int();
        if cur_val == 255i32 {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"You can\'t ");
            print_esc_cstr(b"insert");
            print_int(255i32);
            help_ptr = 1_u8;
            help_line[0] = b"I\'m changing to \\insert0; box 255 is special.";
            error();
            cur_val = 0i32
        }
    }
    SAVE_STACK[SAVE_PTR + 0].b32.s1 = cur_val;
    if cur_cmd as i32 == 38i32 && scan_keyword(b"pre") {
        SAVE_STACK[SAVE_PTR + 1].b32.s1 = 1
    } else {
        SAVE_STACK[SAVE_PTR + 1].b32.s1 = 0
    }
    SAVE_PTR += 2;
    new_save_level(11i32 as group_code);
    scan_left_brace();
    normal_paragraph();
    push_nest();
    cur_list.mode = -1_i16;
    cur_list.aux.b32.s1 = -65536000i32;
}
pub(crate) unsafe fn make_mark() {
    let mut p: i32 = 0;
    let mut c: i32 = 0;
    if cur_chr == 0i32 {
        c = 0i32
    } else {
        scan_register_num();
        c = cur_val
    }
    p = scan_toks(false, true);
    p = get_node(2i32);
    MEM[(p + 1) as usize].b32.s0 = c;
    MEM[p as usize].b16.s1 = 4_u16;
    MEM[p as usize].b16.s0 = 0_u16;
    MEM[(p + 1) as usize].b32.s1 = def_ref;
    MEM[cur_list.tail as usize].b32.s1 = p;
    cur_list.tail = p;
}
pub(crate) unsafe fn append_penalty() {
    scan_int();
    MEM[cur_list.tail as usize].b32.s1 = new_penalty(cur_val);
    cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
    if cur_list.mode as i32 == 1i32 {
        build_page();
    };
}
pub(crate) unsafe fn delete_last() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut fm: bool = false;
    let mut tx: i32 = 0;
    let mut m: u16 = 0;
    if cur_list.mode as i32 == 1i32 && cur_list.tail == cur_list.head {
        /*1141: */
        if cur_chr != 10i32 || last_glue != 0x3fffffffi32 {
            you_cant();
            help_ptr = 2_u8;
            help_line[1] = b"Sorry...I usually can\'t take things from the current page.";
            help_line[0] = b"Try `I\\vskip-\\lastskip\' instead.";
            if cur_chr == 11i32 {
                help_line[0] = b"Try `I\\kern-\\lastkern\' instead."
            } else if cur_chr != 10i32 {
                help_line[0] = b"Perhaps you can make the output routine do it."
            }
            error();
        }
    } else {
        tx = cur_list.tail;
        if !is_char_node(tx) {
            if MEM[tx as usize].b16.s1 as i32 == 9 && MEM[tx as usize].b16.s0 as i32 == 3 {
                r = cur_list.head;
                loop {
                    q = r;
                    r = MEM[q as usize].b32.s1;
                    if r == tx {
                        break;
                    }
                }
                tx = q
            }
        }
        if !is_char_node(tx) {
            if MEM[tx as usize].b16.s1 as i32 == cur_chr {
                q = cur_list.head;
                p = TEX_NULL;
                loop {
                    r = p;
                    p = q;
                    fm = false;
                    if !is_char_node(q) {
                        if MEM[q as usize].b16.s1 as i32 == 7 {
                            let mut for_end: i32 = 0;
                            m = 1_u16;
                            for_end = MEM[q as usize].b16.s0 as i32;
                            if m as i32 <= for_end {
                                loop {
                                    p = MEM[p as usize].b32.s1;
                                    let fresh77 = m;
                                    m = m.wrapping_add(1);
                                    if !((fresh77 as i32) < for_end) {
                                        break;
                                    }
                                }
                            }
                            if p == tx {
                                return;
                            }
                        } else if MEM[q as usize].b16.s1 as i32 == 9
                            && MEM[q as usize].b16.s0 as i32 == 2
                        {
                            fm = true
                        }
                    }
                    q = MEM[p as usize].b32.s1;
                    if q == tx {
                        break;
                    }
                }
                q = MEM[tx as usize].b32.s1;
                MEM[p as usize].b32.s1 = q;
                MEM[tx as usize].b32.s1 = TEX_NULL;
                if q == TEX_NULL {
                    if fm {
                        confusion(b"tail1");
                    } else {
                        cur_list.tail = p
                    }
                } else if fm {
                    cur_list.tail = r;
                    MEM[r as usize].b32.s1 = TEX_NULL;
                    flush_node_list(p);
                }
                flush_node_list(tx);
            }
        }
    };
}
pub(crate) unsafe fn unpackage() {
    let mut p: i32 = 0;
    let mut r: i32 = 0;
    let mut c: u8 = 0;
    if cur_chr > 1i32 {
        /*1651: */
        MEM[cur_list.tail as usize].b32.s1 = disc_ptr[cur_chr as usize]; /*:1156 */
        disc_ptr[cur_chr as usize] = TEX_NULL
    } else {
        c = cur_chr as u8;
        scan_register_num();
        if cur_val < 256i32 {
            p = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
        } else {
            find_sa_element(4i32 as small_number, cur_val, false);
            if cur_ptr == TEX_NULL {
                p = TEX_NULL
            } else {
                p = MEM[(cur_ptr + 1) as usize].b32.s1
            }
        }
        if p == TEX_NULL {
            return;
        }
        if (cur_list.mode as i32).abs() == 207i32
            || (cur_list.mode as i32).abs() == 1i32 && MEM[p as usize].b16.s1 as i32 != 1
            || (cur_list.mode as i32).abs() == 104i32 && MEM[p as usize].b16.s1 as i32 != 0
        {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Incompatible list can\'t be unboxed");
            help_ptr = 3_u8;
            help_line[2] = b"Sorry, Pandora. (You sneaky devil.)";
            help_line[1] = b"I refuse to unbox an \\hbox in vertical mode or vice versa.";
            help_line[0] = b"And I can\'t open any boxes in math mode.";
            error();
            return;
        }
        if c as i32 == 1i32 {
            MEM[cur_list.tail as usize].b32.s1 = copy_node_list(MEM[(p + 5) as usize].b32.s1)
        } else {
            MEM[cur_list.tail as usize].b32.s1 = MEM[(p + 5) as usize].b32.s1;
            if cur_val < 256i32 {
                EQTB[(BOX_BASE + cur_val) as usize].b32.s1 = TEX_NULL
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr != TEX_NULL {
                    MEM[(cur_ptr + 1) as usize].b32.s1 = TEX_NULL;
                    MEM[(cur_ptr + 1) as usize].b32.s0 += 1;
                    delete_sa_ref(cur_ptr);
                }
            }
            free_node(p, 8i32);
        }
    }
    while MEM[cur_list.tail as usize].b32.s1 != TEX_NULL {
        r = MEM[cur_list.tail as usize].b32.s1;
        if !is_char_node(r) && MEM[r as usize].b16.s1 as i32 == 40 {
            MEM[cur_list.tail as usize].b32.s1 = MEM[r as usize].b32.s1;
            free_node(r, 3i32);
        }
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1
    }
}
pub(crate) unsafe fn append_italic_correction() {
    let mut p: i32 = 0;
    let mut f: internal_font_number = 0;
    if cur_list.tail != cur_list.head {
        if is_char_node(cur_list.tail) {
            p = cur_list.tail
        } else if MEM[cur_list.tail as usize].b16.s1 as i32 == 6 {
            p = cur_list.tail + 1i32
        } else if MEM[cur_list.tail as usize].b16.s1 as i32 == 8 {
            if MEM[cur_list.tail as usize].b16.s0 as i32 == 40
                || MEM[cur_list.tail as usize].b16.s0 as i32 == 41
            {
                MEM[cur_list.tail as usize].b32.s1 = new_kern(real_get_native_italic_correction(
                    &mut MEM[cur_list.tail as usize] as *mut memory_word as *mut libc::c_void,
                ));
                cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                MEM[cur_list.tail as usize].b16.s0 = 1_u16
            } else if MEM[cur_list.tail as usize].b16.s0 as i32 == 42 {
                MEM[cur_list.tail as usize].b32.s1 =
                    new_kern(real_get_native_glyph_italic_correction(
                        &mut MEM[cur_list.tail as usize] as *mut memory_word as *mut libc::c_void,
                    ));
                cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                MEM[cur_list.tail as usize].b16.s0 = 1_u16
            }
            return;
        } else {
            return;
        }
        f = MEM[p as usize].b16.s1 as internal_font_number;
        MEM[cur_list.tail as usize].b32.s1 = new_kern(
            FONT_INFO[(ITALIC_BASE[f as usize]
                + FONT_INFO[(CHAR_BASE[f as usize]
                    + effective_char(1i32 != 0, f, MEM[p as usize].b16.s0))
                    as usize]
                    .b16
                    .s1 as i32
                    / 4i32) as usize]
                .b32
                .s1,
        );
        cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
        MEM[cur_list.tail as usize].b16.s0 = 1_u16
    };
}
pub(crate) unsafe fn append_discretionary() {
    let mut c: i32 = 0;
    MEM[cur_list.tail as usize].b32.s1 = new_disc();
    cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
    if cur_chr == 1i32 {
        c = HYPHEN_CHAR[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize];
        if c >= 0i32 {
            if c <= 0xffffi32 {
                MEM[(cur_list.tail + 1) as usize].b32.s0 =
                    new_character(EQTB[(CUR_FONT_LOC) as usize].b32.s1, c as UTF16_code)
            }
        }
    } else {
        SAVE_PTR += 1;
        SAVE_STACK[SAVE_PTR - 1].b32.s1 = 0;
        new_save_level(10i32 as group_code);
        scan_left_brace();
        push_nest();
        cur_list.mode = -104_i16;
        cur_list.aux.b32.s0 = 1000i32
    };
}
pub(crate) unsafe fn build_discretionary() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut n: i32 = 0;
    unsave();
    q = cur_list.head;
    p = MEM[q as usize].b32.s1;
    n = 0i32;
    while p != TEX_NULL {
        if !is_char_node(p) {
            if MEM[p as usize].b16.s1 as i32 > 2 {
                if MEM[p as usize].b16.s1 as i32 != 11 {
                    if MEM[p as usize].b16.s1 as i32 != 6 {
                        if MEM[p as usize].b16.s1 as i32 != 8
                            || MEM[p as usize].b16.s0 as i32 != 40
                                && MEM[p as usize].b16.s0 as i32 != 41
                                && MEM[p as usize].b16.s0 as i32 != 42
                        {
                            if file_line_error_style_p != 0 {
                                print_file_line();
                            } else {
                                print_nl_cstr(b"! ");
                            }
                            print_cstr(b"Improper discretionary list");
                            help_ptr = 1_u8;
                            help_line[0] =
                                b"Discretionary lists must contain only boxes and kerns.";
                            error();
                            begin_diagnostic();
                            print_nl_cstr(b"The following discretionary sublist has been deleted:");
                            show_box(p);
                            end_diagnostic(1i32 != 0);
                            flush_node_list(p);
                            MEM[q as usize].b32.s1 = TEX_NULL;
                            break;
                        }
                    }
                }
            }
        }
        q = p;
        p = MEM[q as usize].b32.s1;
        n += 1
    }
    p = MEM[cur_list.head as usize].b32.s1;
    pop_nest();
    match SAVE_STACK[SAVE_PTR - 1].b32.s1 {
        0 => MEM[(cur_list.tail + 1) as usize].b32.s0 = p,
        1 => MEM[(cur_list.tail + 1) as usize].b32.s1 = p,
        2 => {
            if n > 0i32 && (cur_list.mode as i32).abs() == 207i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Illegal math ");
                print_esc_cstr(b"discretionary");
                help_ptr = 2_u8;
                help_line[1] = b"Sorry: The third part of a discretionary break must be";
                help_line[0] = b"empty, in math formulas. I had to delete your third part.";
                flush_node_list(p);
                n = 0i32;
                error();
            } else {
                MEM[cur_list.tail as usize].b32.s1 = p
            }
            if n <= 65535i32 {
                MEM[cur_list.tail as usize].b16.s0 = n as u16
            } else {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Discretionary list is too long");
                help_ptr = 2_u8;
                help_line[1] = b"Wow---I never thought anybody would tweak me here.";
                help_line[0] = b"You can\'t seriously need such a huge discretionary list?";
                error();
            }
            if n > 0i32 {
                cur_list.tail = q
            }
            SAVE_PTR -= 1;
            return;
        }
        _ => {}
    }
    SAVE_STACK[SAVE_PTR - 1].b32.s1 += 1;
    new_save_level(10i32 as group_code);
    scan_left_brace();
    push_nest();
    cur_list.mode = -104_i16;
    cur_list.aux.b32.s0 = 1000i32;
}
pub(crate) unsafe fn make_accent() {
    let mut s: f64 = 0.;
    let mut t: f64 = 0.;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut f: internal_font_number = 0;
    let mut a: scaled_t = 0;
    let mut h: scaled_t = 0;
    let mut x: scaled_t = 0;
    let mut w: scaled_t = 0;
    let mut delta: scaled_t = 0;
    let mut lsb: scaled_t = 0;
    let mut rsb: scaled_t = 0;
    let mut i: b16x4 = b16x4 {
        s0: 0,
        s1: 0,
        s2: 0,
        s3: 0,
    };
    scan_char_num();
    f = EQTB[(CUR_FONT_LOC) as usize].b32.s1;
    p = new_character(f, cur_val as UTF16_code);
    if p != TEX_NULL {
        x = FONT_INFO[(5i32 + PARAM_BASE[f as usize]) as usize].b32.s1;
        s = FONT_INFO[(1i32 + PARAM_BASE[f as usize]) as usize].b32.s1 as f64 / 65536.0f64;
        if FONT_AREA[f as usize] as u32 == 0xffffu32 || FONT_AREA[f as usize] as u32 == 0xfffeu32 {
            a = MEM[(p + 1) as usize].b32.s1;
            if a == 0i32 {
                get_native_char_sidebearings(f, cur_val, &mut lsb, &mut rsb);
            }
        } else {
            a = FONT_INFO[(WIDTH_BASE[f as usize]
                + FONT_INFO[(CHAR_BASE[f as usize]
                    + effective_char(1i32 != 0, f, MEM[p as usize].b16.s0))
                    as usize]
                    .b16
                    .s3 as i32) as usize]
                .b32
                .s1
        }
        do_assignments();
        q = TEX_NULL;
        f = EQTB[(CUR_FONT_LOC) as usize].b32.s1;
        if cur_cmd as i32 == 11i32 || cur_cmd as i32 == 12i32 || cur_cmd as i32 == 68i32 {
            q = new_character(f, cur_chr as UTF16_code);
            cur_val = cur_chr
        } else if cur_cmd as i32 == 16i32 {
            scan_char_num();
            q = new_character(f, cur_val as UTF16_code)
        } else {
            back_input();
        }
        if q != TEX_NULL {
            /*1160: */
            t = FONT_INFO[(1 + PARAM_BASE[f as usize]) as usize].b32.s1 as f64 / 65536.0f64;
            if FONT_AREA[f as usize] as u32 == 0xffffu32
                || FONT_AREA[f as usize] as u32 == 0xfffeu32
            {
                w = MEM[(q + 1) as usize].b32.s1;
                get_native_char_height_depth(f, cur_val, &mut h, &mut delta);
            } else {
                i = FONT_INFO[(CHAR_BASE[f as usize]
                    + effective_char(1i32 != 0, f, MEM[q as usize].b16.s0))
                    as usize]
                    .b16;
                w = FONT_INFO[(WIDTH_BASE[f as usize] + i.s3 as i32) as usize]
                    .b32
                    .s1;
                h = FONT_INFO[(HEIGHT_BASE[f as usize] + i.s2 as i32 / 16i32) as usize]
                    .b32
                    .s1
            }
            if h != x {
                p = hpack(p, 0i32, 1i32 as small_number);
                MEM[(p + 4) as usize].b32.s1 = x - h
            }
            if (FONT_AREA[f as usize] as u32 == 0xffffu32
                || FONT_AREA[f as usize] as u32 == 0xfffeu32)
                && a == 0i32
            {
                delta = tex_round((w - lsb + rsb) as f64 / 2.0f64 + h as f64 * t - x as f64 * s)
            } else {
                delta = tex_round((w - a) as f64 / 2.0f64 + h as f64 * t - x as f64 * s)
            }
            r = new_kern(delta);
            MEM[r as usize].b16.s0 = 2_u16;
            MEM[cur_list.tail as usize].b32.s1 = r;
            MEM[r as usize].b32.s1 = p;
            cur_list.tail = new_kern(-a - delta);
            MEM[cur_list.tail as usize].b16.s0 = 2_u16;
            MEM[p as usize].b32.s1 = cur_list.tail;
            p = q
        }
        MEM[cur_list.tail as usize].b32.s1 = p;
        cur_list.tail = p;
        cur_list.aux.b32.s0 = 1000i32
    };
}
pub(crate) unsafe fn align_error() {
    if align_state.abs() > 2i32 {
        /*1163: */
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Misplaced ");
        print_cmd_chr(cur_cmd as u16, cur_chr);
        if cur_tok == 0x800000i32 + 38i32 {
            help_ptr = 6_u8;
            help_line[5] = b"I can\'t figure out why you would want to use a tab mark";
            help_line[4] = b"here. If you just want an ampersand, the remedy is";
            help_line[3] = b"simple: Just type `I\\&\' now. But if some right brace";
            help_line[2] = b"up above has ended a previous alignment prematurely,";
            help_line[1] = b"you\'re probably due for more error messages, and you";
            help_line[0] = b"might try typing `S\' now just to see what is salvageable."
        } else {
            help_ptr = 5_u8;
            help_line[4] = b"I can\'t figure out why you would want to use a tab mark";
            help_line[3] = b"or \\cr or \\span just now. If something like a right brace";
            help_line[2] = b"up above has ended a previous alignment prematurely,";
            help_line[1] = b"you\'re probably due for more error messages, and you";
            help_line[0] = b"might try typing `S\' now just to see what is salvageable."
        }
        error();
    } else {
        back_input();
        if align_state < 0i32 {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Missing { inserted");
            align_state += 1;
            cur_tok = 0x200000i32 + 123i32
        } else {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Missing } inserted");
            align_state -= 1;
            cur_tok = 0x400000i32 + 125i32
        }
        help_ptr = 3_u8;
        help_line[2] = b"I\'ve put in what seems to be necessary to fix";
        help_line[1] = b"the current column of the current alignment.";
        help_line[0] = b"Try to go on, since this might almost work.";
        ins_error();
    };
}
pub(crate) unsafe fn no_align_error() {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Misplaced ");
    print_esc_cstr(b"noalign");
    help_ptr = 2_u8;
    help_line[1] = b"I expect to see \\noalign only after the \\cr of";
    help_line[0] = b"an alignment. Proceed, and I\'ll ignore this case.";
    error();
}
pub(crate) unsafe fn omit_error() {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Misplaced ");
    print_esc_cstr(b"omit");
    help_ptr = 2_u8;
    help_line[1] = b"I expect to see \\omit only after tab marks or the \\cr of";
    help_line[0] = b"an alignment. Proceed, and I\'ll ignore this case.";
    error();
}
pub(crate) unsafe fn do_endv() {
    BASE_PTR = INPUT_PTR;
    INPUT_STACK[BASE_PTR] = cur_input;
    while INPUT_STACK[BASE_PTR].index as i32 != 2i32
        && INPUT_STACK[BASE_PTR].loc == TEX_NULL
        && INPUT_STACK[BASE_PTR].state as i32 == 0i32
    {
        BASE_PTR -= 1
    }
    if INPUT_STACK[BASE_PTR].index as i32 != 2i32
        || INPUT_STACK[BASE_PTR].loc != TEX_NULL
        || INPUT_STACK[BASE_PTR].state as i32 != 0i32
    {
        fatal_error(b"(interwoven alignment preambles are not allowed)");
    }
    if cur_group as i32 == 6i32 {
        end_graf();
        if fin_col() {
            fin_row();
        }
    } else {
        off_save();
    };
}
pub(crate) unsafe fn cs_error() {
    if file_line_error_style_p != 0 {
        print_file_line();
    } else {
        print_nl_cstr(b"! ");
    }
    print_cstr(b"Extra ");
    print_esc_cstr(b"endcsname");
    help_ptr = 1_u8;
    help_line[0] = b"I\'m ignoring this, since I wasn\'t doing a \\csname.";
    error();
}
pub(crate) unsafe fn push_math(mut c: group_code) {
    push_nest();
    cur_list.mode = -207_i16;
    cur_list.aux.b32.s1 = TEX_NULL;
    new_save_level(c);
}
pub(crate) unsafe fn just_copy(mut p: i32, mut h: i32, mut t: i32) {
    let mut r: i32 = 0;
    let mut words: u8 = 0;
    while p != TEX_NULL {
        let mut current_block_50: u64;
        words = 1_u8;
        if is_char_node(p) {
            r = get_avail();
            current_block_50 = 2500484646272006982;
        } else {
            match MEM[p as usize].b16.s1 as i32 {
                0 | 1 => {
                    r = get_node(8i32);
                    MEM[(r + 8 - 1) as usize].b32.s0 = MEM[(p + 8 - 1) as usize].b32.s0;
                    MEM[(r + 8 - 1) as usize].b32.s1 = MEM[(p + 8 - 1) as usize].b32.s1;
                    MEM[(r + 6) as usize] = MEM[(p + 6) as usize];
                    MEM[(r + 5) as usize] = MEM[(p + 5) as usize];
                    words = 5_u8;
                    MEM[(r + 5) as usize].b32.s1 = TEX_NULL;
                    current_block_50 = 2500484646272006982;
                }
                2 => {
                    r = get_node(5i32);
                    words = 5_u8;
                    current_block_50 = 2500484646272006982;
                }
                6 => {
                    r = get_avail();
                    MEM[r as usize] = MEM[(p + 1) as usize];
                    current_block_50 = 1668590571950580537;
                }
                11 | 9 => {
                    words = 3_u8;
                    r = get_node(words as i32);
                    current_block_50 = 2500484646272006982;
                }
                10 => {
                    r = get_node(3i32);
                    MEM[MEM[(p + 1) as usize].b32.s0 as usize].b32.s1 += 1;
                    MEM[(r + 3 - 1) as usize].b32.s0 = MEM[(p + 3 - 1) as usize].b32.s0;
                    MEM[(r + 3 - 1) as usize].b32.s1 = MEM[(p + 3 - 1) as usize].b32.s1;
                    MEM[(r + 1) as usize].b32.s0 = MEM[(p + 1) as usize].b32.s0;
                    MEM[(r + 1) as usize].b32.s1 = TEX_NULL;
                    current_block_50 = 2500484646272006982;
                }
                8 => {
                    match MEM[p as usize].b16.s0 as i32 {
                        0 => {
                            r = get_node(3i32);
                            words = 3_u8
                        }
                        1 | 3 => {
                            r = get_node(2i32);
                            MEM[MEM[(p + 1) as usize].b32.s1 as usize].b32.s0 += 1;
                            words = 2_u8
                        }
                        2 | 4 => {
                            r = get_node(2i32);
                            words = 2_u8
                        }
                        40 | 41 => {
                            words = MEM[(p + 4) as usize].b16.s3 as u8;
                            r = get_node(words as i32);
                            while words as i32 > 0i32 {
                                words = words.wrapping_sub(1);
                                MEM[(r + words as i32) as usize] = MEM[(p + words as i32) as usize]
                            }
                            MEM[(r + 5) as usize].ptr = 0 as *mut libc::c_void;
                            MEM[(r + 4) as usize].b16.s0 = 0_u16;
                            copy_native_glyph_info(p, r);
                        }
                        42 => {
                            r = get_node(5i32);
                            words = 5_u8
                        }
                        43 | 44 => {
                            words = (9i32 as u64).wrapping_add(
                                (MEM[(p + 4) as usize].b16.s1 as u64)
                                    .wrapping_add(::std::mem::size_of::<memory_word>() as u64)
                                    .wrapping_sub(1i32 as u64)
                                    .wrapping_div(::std::mem::size_of::<memory_word>() as u64),
                            ) as u8;
                            r = get_node(words as i32)
                        }
                        6 => r = get_node(2i32),
                        _ => confusion(b"ext2"),
                    }
                    current_block_50 = 2500484646272006982;
                }
                _ => current_block_50 = 17768496421797376910,
            }
        }
        match current_block_50 {
            2500484646272006982 => {
                while words as i32 > 0i32 {
                    words = words.wrapping_sub(1);
                    MEM[(r + words as i32) as usize] = MEM[(p + words as i32) as usize]
                }
                current_block_50 = 1668590571950580537;
            }
            _ => {}
        }
        match current_block_50 {
            1668590571950580537 => {
                MEM[h as usize].b32.s1 = r;
                h = r
            }
            _ => {}
        }
        p = MEM[p as usize].b32.s1
    }
    MEM[h as usize].b32.s1 = t;
}
pub(crate) unsafe fn just_reverse(mut p: i32) {
    let mut l: i32 = 0;
    let mut t: i32 = 0;
    let mut q: i32 = 0;
    let mut m: i32 = 0;
    let mut n: i32 = 0;
    m = TEX_NULL;
    n = TEX_NULL;
    if MEM[(4999999 - 3) as usize].b32.s1 == TEX_NULL {
        just_copy(MEM[p as usize].b32.s1, 4999999 - 3, TEX_NULL);
        q = MEM[(4999999 - 3) as usize].b32.s1
    } else {
        q = MEM[p as usize].b32.s1;
        MEM[p as usize].b32.s1 = TEX_NULL;
        flush_node_list(MEM[(4999999 - 3) as usize].b32.s1);
    }
    t = new_edge(cur_dir, 0i32);
    l = t;
    cur_dir = (1i32 - cur_dir as i32) as small_number;
    while q != TEX_NULL {
        if is_char_node(q) {
            loop {
                p = q;
                q = MEM[p as usize].b32.s1;
                MEM[p as usize].b32.s1 = l;
                l = p;
                if !is_char_node(q) {
                    break;
                }
            }
        } else {
            p = q;
            q = MEM[p as usize].b32.s1;
            if MEM[p as usize].b16.s1 as i32 == 9 {
                /*1527: */
                if MEM[p as usize].b16.s0 as i32 & 1 != 0 {
                    if MEM[LR_ptr as usize].b32.s0 != 4 * (MEM[p as usize].b16.s0 as i32 / 4) + 3 {
                        MEM[p as usize].b16.s1 = 11;
                        LR_problems += 1
                    } else {
                        temp_ptr = LR_ptr;
                        LR_ptr = MEM[temp_ptr as usize].b32.s1;
                        MEM[temp_ptr as usize].b32.s1 = avail;
                        avail = temp_ptr;
                        if n > TEX_NULL {
                            n -= 1;
                            MEM[p as usize].b16.s0 -= 1;
                        } else if m > TEX_NULL {
                            m -= 1;
                            MEM[p as usize].b16.s1 = 11
                        } else {
                            MEM[(t + 1) as usize].b32.s1 = MEM[(p + 1) as usize].b32.s1;
                            MEM[t as usize].b32.s1 = q;
                            free_node(p, 3i32);
                            break;
                        }
                    }
                } else {
                    temp_ptr = get_avail();
                    MEM[temp_ptr as usize].b32.s0 = 4 * (MEM[p as usize].b16.s0 as i32 / 4) + 3;
                    MEM[temp_ptr as usize].b32.s1 = LR_ptr;
                    LR_ptr = temp_ptr;
                    if n > TEX_NULL || MEM[p as usize].b16.s0 as i32 / 8 != cur_dir as i32 {
                        n += 1;
                        MEM[p as usize].b16.s0 += 1;
                    } else {
                        MEM[p as usize].b16.s1 = 11_u16;
                        m += 1
                    }
                }
            }
            MEM[p as usize].b32.s1 = l;
            l = p
        }
    }
    MEM[(4999999 - 3) as usize].b32.s1 = l;
}
pub(crate) unsafe fn get_r_token() {
    loop {
        loop {
            get_token();
            if !(cur_tok == 0x1400020i32) {
                break;
            }
        }
        if !(cur_cs == 0i32
            || cur_cs > EQTB_TOP as i32
            || cur_cs > FROZEN_CONTROL_SEQUENCE && cur_cs <= DIMEN_BASE + 23i32 + 256i32 - 1i32)
        {
            break;
        }
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Missing control sequence inserted");
        help_ptr = 5_u8;
        help_line[4] = b"Please don\'t say `\\def cs{...}\', say `\\def\\cs{...}\'.";
        help_line[3] = b"I\'ve inserted an inaccessible control sequence so that your";
        help_line[2] = b"definition will be completed without mixing me up too badly.";
        help_line[1] = b"You can recover graciously from this error, if you\'re";
        help_line[0] = b"careful; see exercise 27.2 in The TeXbook.";
        if cur_cs == 0i32 {
            back_input();
        }
        cur_tok = 0x1ffffffi32 + (FROZEN_CONTROL_SEQUENCE + 0i32);
        ins_error();
    }
}
pub(crate) unsafe fn trap_zero_glue() {
    if MEM[(cur_val + 1) as usize].b32.s1 == 0
        && MEM[(cur_val + 2) as usize].b32.s1 == 0
        && MEM[(cur_val + 3) as usize].b32.s1 == 0
    {
        MEM[0].b32.s1 += 1;
        delete_glue_ref(cur_val);
        cur_val = 0i32
    };
}
pub(crate) unsafe fn do_register_command(mut a: small_number) {
    let mut current_block: u64;
    let mut l: i32 = TEX_NULL;
    let mut q: i32 = 0;
    let mut r: i32 = 0;
    let mut s: i32 = TEX_NULL;
    let mut p: u8 = 0;
    let mut e: bool = false;
    let mut w: i32 = 0i32;
    q = cur_cmd as i32;
    e = false;
    if q != 91i32 {
        get_x_token();
        if cur_cmd as i32 >= 74i32 && cur_cmd as i32 <= 77i32 {
            l = cur_chr;
            p = (cur_cmd as i32 - 74i32) as u8;
            current_block = 16534065480145571271;
        } else {
            if cur_cmd as i32 != 91i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"You can\'t use `");
                print_cmd_chr(cur_cmd as u16, cur_chr);
                print_cstr(b"\' after ");
                print_cmd_chr(q as u16, 0i32);
                help_ptr = 1_u8;
                help_line[0] = b"I\'m forgetting what you said and not changing anything.";
                error();
                return;
            }
            current_block = 4808432441040389987;
        }
    } else {
        current_block = 4808432441040389987;
    }
    match current_block {
        4808432441040389987 => {
            if cur_chr < 0i32 || cur_chr > 19i32 {
                /*lo_mem_stat_max*/
                l = cur_chr;
                p = (MEM[l as usize].b16.s1 as i32 / 64) as u8;
                e = true
            } else {
                p = cur_chr as u8;
                scan_register_num();
                if cur_val > 255i32 {
                    find_sa_element(p as small_number, cur_val, true);
                    l = cur_ptr;
                    e = true
                } else {
                    match p as i32 {
                        0 => l = cur_val + (COUNT_BASE),
                        1 => l = cur_val + (DIMEN_BASE + 23i32),
                        2 => {
                            l = cur_val
                                + (1i32
                                    + (0x10ffffi32 + 1i32)
                                    + (0x10ffffi32 + 1i32)
                                    + 1i32
                                    + 15000i32
                                    + 12i32
                                    + 9000i32
                                    + 1i32
                                    + 1i32
                                    + 19i32)
                        }
                        3 => {
                            l = cur_val
                                + (1i32
                                    + (0x10ffffi32 + 1i32)
                                    + (0x10ffffi32 + 1i32)
                                    + 1i32
                                    + 15000i32
                                    + 12i32
                                    + 9000i32
                                    + 1i32
                                    + 1i32
                                    + 19i32
                                    + 256i32)
                        }
                        _ => {}
                    }
                }
            }
        }
        _ => {}
    }
    if (p as i32) < 2i32 {
        if e {
            w = MEM[(l + 2) as usize].b32.s1
        } else {
            w = EQTB[l as usize].b32.s1
        }
    } else if e {
        s = MEM[(l + 1) as usize].b32.s1
    } else {
        s = EQTB[l as usize].b32.s1
        /*:1272*/
    } /*1275:*/
    if q == 91i32 {
        scan_optional_equals();
    } else {
        scan_keyword(b"by");
    }
    arith_error = false;
    if q < 93i32 {
        /*1273:*/
        if (p as i32) < 2i32 {
            if p as i32 == 0i32 {
                scan_int();
            } else {
                scan_dimen(false, false, false);
            }
            if q == 92i32 {
                cur_val = cur_val + w
            }
        } else {
            scan_glue(p as small_number);
            if q == 92i32 {
                /*1274:*/
                q = new_spec(cur_val);
                r = s;
                delete_glue_ref(cur_val);
                MEM[(q + 1) as usize].b32.s1 =
                    MEM[(q + 1) as usize].b32.s1 + MEM[(r + 1) as usize].b32.s1;
                if MEM[(q + 2) as usize].b32.s1 == 0 {
                    MEM[q as usize].b16.s1 = 0_u16
                }
                if MEM[q as usize].b16.s1 as i32 == MEM[r as usize].b16.s1 as i32 {
                    MEM[(q + 2) as usize].b32.s1 =
                        MEM[(q + 2) as usize].b32.s1 + MEM[(r + 2) as usize].b32.s1
                } else if (MEM[q as usize].b16.s1 as i32) < MEM[r as usize].b16.s1 as i32
                    && MEM[(r + 2) as usize].b32.s1 != 0
                {
                    MEM[(q + 2) as usize].b32.s1 = MEM[(r + 2) as usize].b32.s1;
                    MEM[q as usize].b16.s1 = MEM[r as usize].b16.s1
                }
                if MEM[(q + 3) as usize].b32.s1 == 0 {
                    MEM[q as usize].b16.s0 = 0_u16
                }
                if MEM[q as usize].b16.s0 as i32 == MEM[r as usize].b16.s0 as i32 {
                    MEM[(q + 3) as usize].b32.s1 =
                        MEM[(q + 3) as usize].b32.s1 + MEM[(r + 3) as usize].b32.s1
                } else if (MEM[q as usize].b16.s0 as i32) < MEM[r as usize].b16.s0 as i32
                    && MEM[(r + 3) as usize].b32.s1 != 0
                {
                    MEM[(q + 3) as usize].b32.s1 = MEM[(r + 3) as usize].b32.s1;
                    MEM[q as usize].b16.s0 = MEM[r as usize].b16.s0
                }
                cur_val = q
            }
        }
    } else {
        scan_int();
        if (p as i32) < 2i32 {
            if q == 93i32 {
                if p as i32 == 0i32 {
                    cur_val = mult_and_add(w, cur_val, 0i32, 0x7fffffffi32)
                } else {
                    cur_val = mult_and_add(w, cur_val, 0i32, 0x3fffffffi32)
                }
            } else {
                cur_val = x_over_n(w, cur_val)
            }
        } else {
            r = new_spec(s);
            if q == 93i32 {
                MEM[(r + 1) as usize].b32.s1 =
                    mult_and_add(MEM[(s + 1) as usize].b32.s1, cur_val, 0, 0x3fffffff);
                MEM[(r + 2) as usize].b32.s1 =
                    mult_and_add(MEM[(s + 2) as usize].b32.s1, cur_val, 0, 0x3fffffff);
                MEM[(r + 3) as usize].b32.s1 =
                    mult_and_add(MEM[(s + 3) as usize].b32.s1, cur_val, 0, 0x3fffffff)
            } else {
                MEM[(r + 1) as usize].b32.s1 = x_over_n(MEM[(s + 1) as usize].b32.s1, cur_val);
                MEM[(r + 2) as usize].b32.s1 = x_over_n(MEM[(s + 2) as usize].b32.s1, cur_val);
                MEM[(r + 3) as usize].b32.s1 = x_over_n(MEM[(s + 3) as usize].b32.s1, cur_val)
            }
            cur_val = r
        }
    }
    if arith_error {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Arithmetic overflow");
        help_ptr = 2_u8;
        help_line[1] = b"I can\'t carry out that multiplication or division,";
        help_line[0] = b"since the result is out of range.";
        if p as i32 >= 2i32 {
            delete_glue_ref(cur_val);
        }
        error();
        return;
    }
    if (p as i32) < 2i32 {
        if e {
            if a as i32 >= 4i32 {
                gsa_w_def(l, cur_val);
            } else {
                sa_w_def(l, cur_val);
            }
        } else if a as i32 >= 4i32 {
            geq_word_define(l, cur_val);
        } else {
            eq_word_define(l, cur_val);
        }
    } else {
        trap_zero_glue();
        if e {
            if a as i32 >= 4i32 {
                gsa_def(l, cur_val);
            } else {
                sa_def(l, cur_val);
            }
        } else if a as i32 >= 4i32 {
            geq_define(l, 119_u16, cur_val);
        } else {
            eq_define(l, 119_u16, cur_val);
        }
    };
}
pub(crate) unsafe fn alter_aux() {
    let mut c: i32 = 0;
    if cur_chr != (cur_list.mode as i32).abs() {
        report_illegal_case();
    } else {
        c = cur_chr;
        scan_optional_equals();
        if c == 1i32 {
            scan_dimen(false, false, false);
            cur_list.aux.b32.s1 = cur_val
        } else {
            scan_int();
            if cur_val <= 0i32 || cur_val > 32767i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Bad space factor");
                help_ptr = 1_u8;
                help_line[0] = b"I allow only values in the range 1..32767 here.";
                int_error(cur_val);
            } else {
                cur_list.aux.b32.s0 = cur_val
            }
        }
    };
}
pub(crate) unsafe fn alter_prev_graf() {
    let mut p: i32 = 0;
    *nest.offset(nest_ptr as isize) = cur_list;
    p = nest_ptr;
    while ((*nest.offset(p as isize)).mode as i32).abs() != 1i32 {
        p -= 1
    }
    scan_optional_equals();
    scan_int();
    if cur_val < 0i32 {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"Bad ");
        print_esc_cstr(b"prevgraf");
        help_ptr = 1_u8;
        help_line[0] = b"I allow only nonnegative values here.";
        int_error(cur_val);
    } else {
        (*nest.offset(p as isize)).prev_graf = cur_val;
        cur_list = *nest.offset(nest_ptr as isize)
    };
}
pub(crate) unsafe fn alter_page_so_far() {
    let mut c: u8 = 0;
    c = cur_chr as u8;
    scan_optional_equals();
    scan_dimen(false, false, false);
    page_so_far[c as usize] = cur_val;
}
pub(crate) unsafe fn alter_integer() {
    let mut c: small_number = 0;
    c = cur_chr as small_number;
    scan_optional_equals();
    scan_int();
    if c as i32 == 0i32 {
        dead_cycles = cur_val
    } else if c as i32 == 2i32 {
        if cur_val < 0i32 || cur_val > 3i32 {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Bad interaction mode");
            help_ptr = 2_u8;
            help_line[1] = b"Modes are 0=batch, 1=nonstop, 2=scroll, and";
            help_line[0] = b"3=errorstop. Proceed, and I\'ll ignore this case.";
            int_error(cur_val);
        } else {
            cur_chr = cur_val;
            new_interaction();
        }
    } else {
        insert_penalties = cur_val
    };
}
pub(crate) unsafe fn alter_box_dimen() {
    let mut c: small_number = 0;
    let mut b: i32 = 0;
    c = cur_chr as small_number;
    scan_register_num();
    if cur_val < 256i32 {
        b = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
    } else {
        find_sa_element(4i32 as small_number, cur_val, false);
        if cur_ptr == TEX_NULL {
            b = TEX_NULL
        } else {
            b = MEM[(cur_ptr + 1) as usize].b32.s1
        }
    }
    scan_optional_equals();
    scan_dimen(false, false, false);
    if b != TEX_NULL {
        MEM[(b + c as i32) as usize].b32.s1 = cur_val
    };
}
pub(crate) unsafe fn new_font(mut a: small_number) {
    let mut current_block: u64;
    let mut u: i32 = 0;
    let mut s: scaled_t = 0;
    let mut f: internal_font_number = 0;
    let mut t: str_number = 0;
    if job_name == 0i32 {
        open_log_file();
    }
    get_r_token();
    u = cur_cs;
    if u >= 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) + 1i32 {
        t = (*hash.offset(u as isize)).s1
    } else if u >= 1i32 + (0x10ffffi32 + 1i32) {
        if u == 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) {
            t = maketexstring(b"FONT")
        } else {
            t = u - (1i32 + (0x10ffffi32 + 1i32))
        }
    } else {
        let old_setting_0 = selector;
        selector = Selector::NEW_STRING;
        print_cstr(b"FONT");
        print(u - 1i32);
        selector = old_setting_0;
        if pool_ptr + 1i32 > pool_size {
            overflow(b"pool size", pool_size - init_pool_ptr);
        }
        t = make_string()
    }
    if a as i32 >= 4i32 {
        geq_define(u, 89_u16, 0i32);
    } else {
        eq_define(u, 89_u16, 0i32);
    }
    scan_optional_equals();
    scan_file_name();
    name_in_progress = true;
    if scan_keyword(b"at") {
        /*1294: */
        scan_dimen(false, false, false); /*:1293 */
        s = cur_val; /*:79 */
        if s <= 0i32 || s >= 0x8000000i32 {
            if file_line_error_style_p != 0 {
                print_file_line(); /*1318: */
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Improper `at\' size (");
            print_scaled(s);
            print_cstr(b"pt), replaced by 10pt");
            help_ptr = 2_u8;
            help_line[1] = b"I can only handle fonts at positive sizes that are";
            help_line[0] = b"less than 2048pt, so I\'ve changed what you said to 10pt.";
            error();
            s = (10i32 as i64 * 65536) as scaled_t
        }
    } else if scan_keyword(b"scaled") {
        scan_int();
        s = -cur_val;
        if cur_val <= 0i32 || cur_val as i64 > 32768 {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Illegal magnification has been changed to 1000");
            help_ptr = 1_u8;
            help_line[0] = b"The magnification ratio must be between 1 and 32768.";
            int_error(cur_val);
            s = -1000i32
        }
    } else {
        s = -1000i32
    }
    name_in_progress = false;
    let mut for_end: i32 = 0;
    f = 0i32 + 1i32;
    for_end = font_ptr;
    if f <= for_end {
        current_block = 17075014677070940716;
    } else {
        current_block = 6838274324784804404;
    }
    loop {
        match current_block {
            6838274324784804404 => {
                f = read_font_info(u, cur_name, cur_area, s);
                break;
            }
            _ => {
                if str_eq_str(FONT_NAME[f as usize], cur_name) as i32 != 0
                    && (length(cur_area) == 0i32
                        && (FONT_AREA[f as usize] as u32 == 0xffffu32
                            || FONT_AREA[f as usize] as u32 == 0xfffeu32)
                        || str_eq_str(FONT_AREA[f as usize], cur_area) as i32 != 0)
                {
                    if s > 0i32 {
                        if s == FONT_SIZE[f as usize] {
                            break;
                        }
                    } else if FONT_SIZE[f as usize]
                        == xn_over_d(FONT_DSIZE[f as usize], -s, 1000i32)
                    {
                        break;
                    }
                }
                append_str(cur_area);
                append_str(cur_name);
                append_str(cur_ext);
                if str_eq_str(FONT_NAME[f as usize], make_string()) {
                    str_ptr -= 1;
                    pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize);
                    if FONT_AREA[f as usize] as u32 == 0xffffu32
                        || FONT_AREA[f as usize] as u32 == 0xfffeu32
                    {
                        if s > 0i32 {
                            if s == FONT_SIZE[f as usize] {
                                break;
                            }
                        } else if FONT_SIZE[f as usize]
                            == xn_over_d(FONT_DSIZE[f as usize], -s, 1000i32)
                        {
                            break;
                        }
                    }
                } else {
                    str_ptr -= 1;
                    pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize)
                }
                let fresh86 = f;
                f = f + 1;
                if fresh86 < for_end {
                    current_block = 17075014677070940716;
                } else {
                    current_block = 6838274324784804404;
                }
            }
        }
    }
    if a as i32 >= 4i32 {
        geq_define(u, 89_u16, f);
    } else {
        eq_define(u, 89_u16, f);
    }
    EQTB[(FROZEN_CONTROL_SEQUENCE + 12i32 + f) as usize] = EQTB[u as usize];
    (*hash.offset((FROZEN_CONTROL_SEQUENCE + 12i32 + f) as isize)).s1 = t;
}
pub(crate) unsafe fn new_interaction() {
    print_ln();
    interaction = cur_chr as u8;
    if interaction as i32 == 0i32 {
        selector = Selector::NO_PRINT
    } else {
        selector = Selector::TERM_ONLY
    }
    if log_opened {
        selector = (u8::from(selector)).wrapping_add(2).into()
    };
}
pub(crate) unsafe fn issue_message() {
    let mut c: u8 = 0;
    let mut s: str_number = 0;
    c = cur_chr as u8;
    MEM[(4999999 - 12) as usize].b32.s1 = scan_toks(false, true);
    let old_setting_0 = selector;
    selector = Selector::NEW_STRING;
    token_show(def_ref);
    selector = old_setting_0;
    flush_list(def_ref);
    if pool_ptr + 1i32 > pool_size {
        overflow(b"pool size", pool_size - init_pool_ptr);
    }
    s = make_string();
    if c as i32 == 0i32 {
        /*1315: */
        if term_offset + length(s) > max_print_line - 2i32 {
            print_ln();
        } else if term_offset > 0i32 || file_offset > 0i32 {
            print_char(' ' as i32);
        }
        print(s);
        rust_stdout.as_mut().unwrap().flush().unwrap();
    } else {
        if file_line_error_style_p != 0 {
            print_file_line();
        } else {
            print_nl_cstr(b"! ");
        }
        print_cstr(b"");
        print(s);
        if EQTB[(1i32
            + (0x10ffffi32 + 1i32)
            + (0x10ffffi32 + 1i32)
            + 1i32
            + 15000i32
            + 12i32
            + 9000i32
            + 1i32
            + 1i32
            + 19i32
            + 256i32
            + 256i32
            + 9i32) as usize]
            .b32
            .s1
            != TEX_NULL
        {
            use_err_help = true
        } else if long_help_seen {
            help_ptr = 1_u8;
            help_line[0] = b"(That was another \\errmessage.)"
        } else {
            if (interaction as i32) < 3i32 {
                long_help_seen = true
            }
            help_ptr = 4_u8;
            help_line[3] = b"This error message was generated by an \\errmessage";
            help_line[2] = b"command, so I can\'t give any explicit help.";
            help_line[1] = b"Pretend that you\'re Hercule Poirot: Examine all clues,";
            help_line[0] = b"and deduce the truth by order and method."
        }
        error();
        use_err_help = false
    }
    str_ptr -= 1;
    pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize);
}
pub(crate) unsafe fn shift_case() {
    let mut b: i32 = 0;
    let mut p: i32 = 0;
    let mut t: i32 = 0;
    let mut c: i32 = 0;
    b = cur_chr;
    p = scan_toks(false, false);
    p = MEM[def_ref as usize].b32.s1;
    while p != TEX_NULL {
        t = MEM[p as usize].b32.s0;
        if t < 0x1ffffffi32 + (1i32 + (0x10ffffi32 + 1i32)) {
            c = t % 0x200000i32;
            if EQTB[(b + c) as usize].b32.s1 != 0i32 {
                MEM[p as usize].b32.s0 = t - c + EQTB[(b + c) as usize].b32.s1
            }
        }
        p = MEM[p as usize].b32.s1
    }
    begin_token_list(MEM[def_ref as usize].b32.s1, 3_u16);
    MEM[def_ref as usize].b32.s1 = avail;
    avail = def_ref;
}
pub(crate) unsafe fn show_whatever() {
    let mut current_block: u64;
    let mut p: i32 = 0;
    let mut t: small_number = 0;
    let mut m: u8 = 0;
    let mut l: i32 = 0;
    let mut n: i32 = 0;
    match cur_chr {
        3 => {
            begin_diagnostic();
            show_activities();
            current_block = 7330218953828964527;
        }
        1 => {
            scan_register_num();
            if cur_val < 256i32 {
                p = EQTB[(BOX_BASE + cur_val) as usize].b32.s1
            } else {
                find_sa_element(4i32 as small_number, cur_val, false);
                if cur_ptr == TEX_NULL {
                    p = TEX_NULL
                } else {
                    p = MEM[(cur_ptr + 1) as usize].b32.s1
                }
            }
            begin_diagnostic();
            print_nl_cstr(b"> \\box");
            print_int(cur_val);
            print_char('=' as i32);
            if p == TEX_NULL {
                print_cstr(b"void");
            } else {
                show_box(p);
            }
            current_block = 7330218953828964527;
        }
        0 => {
            get_token();
            print_nl_cstr(b"> ");
            if cur_cs != 0i32 {
                sprint_cs(cur_cs);
                print_char('=' as i32);
            }
            print_meaning();
            current_block = 6249296489108783913;
        }
        4 => {
            begin_diagnostic();
            show_save_groups();
            current_block = 7330218953828964527;
        }
        6 => {
            begin_diagnostic();
            print_nl_cstr(b"");
            print_ln();
            if cond_ptr == TEX_NULL {
                print_nl_cstr(b"### ");
                print_cstr(b"no active conditionals");
            } else {
                p = cond_ptr;
                n = 0i32;
                loop {
                    n += 1;
                    p = MEM[p as usize].b32.s1;
                    if p == TEX_NULL {
                        break;
                    }
                }
                p = cond_ptr;
                t = cur_if;
                l = if_line;
                m = if_limit;
                loop {
                    print_nl_cstr(b"### level ");
                    print_int(n);
                    print_cstr(b": ");
                    print_cmd_chr(107_u16, t as i32);
                    if m as i32 == 2i32 {
                        print_esc_cstr(b"else");
                    }
                    if l != 0i32 {
                        print_cstr(b" entered on line ");
                        print_int(l);
                    }
                    n -= 1;
                    t = MEM[p as usize].b16.s0 as small_number;
                    l = MEM[(p + 1) as usize].b32.s1;
                    m = MEM[p as usize].b16.s1 as u8;
                    p = MEM[p as usize].b32.s1;
                    if p == TEX_NULL {
                        break;
                    }
                }
            }
            current_block = 7330218953828964527;
        }
        _ => {
            p = the_toks();
            print_nl_cstr(b"> ");
            token_show(4999999i32 - 3i32);
            flush_list(MEM[(4999999 - 3) as usize].b32.s1);
            current_block = 6249296489108783913;
        }
    }
    match current_block {
        7330218953828964527 => {
            end_diagnostic(1i32 != 0);
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"OK");
            if selector == Selector::TERM_AND_LOG {
                if EQTB[(INT_BASE + 29i32) as usize].b32.s1 <= 0i32 {
                    selector = Selector::TERM_ONLY;
                    print_cstr(b" (see the transcript file)");
                    selector = Selector::TERM_AND_LOG
                }
            }
        }
        _ => {}
    }
    if (interaction as i32) < 3i32 {
        help_ptr = 0_u8;
        error_count -= 1
    } else if EQTB[(INT_BASE + 29i32) as usize].b32.s1 > 0i32 {
        help_ptr = 3_u8;
        help_line[2] = b"This isn\'t an error message; I\'m just \\showing something.";
        help_line[1] = b"Type `I\\show...\' to show more (e.g., \\show\\cs,";
        help_line[0] = b"\\showthe\\count10, \\showbox255, \\showlists)."
    } else {
        help_ptr = 5_u8;
        help_line[4] = b"This isn\'t an error message; I\'m just \\showing something.";
        help_line[3] = b"Type `I\\show...\' to show more (e.g., \\show\\cs,";
        help_line[2] = b"\\showthe\\count10, \\showbox255, \\showlists).";
        help_line[1] = b"And type `I\\tracingonline=1\\show...\' to show boxes and";
        help_line[0] = b"lists on your terminal as well as in the transcript file."
    }
    error();
}
pub(crate) unsafe fn new_write_whatsit(mut w: small_number) {
    new_whatsit(cur_chr as small_number, w);
    if w as i32 != 2i32 {
        scan_four_bit_int();
    } else {
        scan_int();
        if cur_val < 0i32 {
            cur_val = 17i32
        } else if cur_val > 15i32 && cur_val != 18i32 {
            cur_val = 16i32
        }
    }
    MEM[(cur_list.tail + 1) as usize].b32.s0 = cur_val;
}
pub(crate) unsafe fn scan_and_pack_name() {
    scan_file_name();
    pack_file_name(cur_name, cur_area, cur_ext);
}
pub(crate) unsafe fn do_extension() {
    let mut i: i32 = 0;
    let mut j: i32 = 0;
    let mut k: i32 = 0;
    let mut p: i32 = 0;
    match cur_chr {
        0 => {
            new_write_whatsit(3i32 as small_number);
            scan_optional_equals();
            scan_file_name();
            MEM[(cur_list.tail + 1) as usize].b32.s1 = cur_name;
            MEM[(cur_list.tail + 2) as usize].b32.s0 = cur_area;
            MEM[(cur_list.tail + 2) as usize].b32.s1 = cur_ext
        }
        1 => {
            k = cur_cs;
            new_write_whatsit(2i32 as small_number);
            cur_cs = k;
            p = scan_toks(false, false);
            MEM[(cur_list.tail + 1) as usize].b32.s1 = def_ref
        }
        2 => {
            new_write_whatsit(2i32 as small_number);
            MEM[(cur_list.tail + 1) as usize].b32.s1 = TEX_NULL
        }
        3 => {
            new_whatsit(3i32 as small_number, 2i32 as small_number);
            MEM[(cur_list.tail + 1) as usize].b32.s0 = TEX_NULL;
            p = scan_toks(false, true);
            MEM[(cur_list.tail + 1) as usize].b32.s1 = def_ref
        }
        4 => {
            get_x_token();
            if cur_cmd as i32 == 59i32 && cur_chr <= 2i32 {
                p = cur_list.tail;
                do_extension();
                out_what(cur_list.tail);
                flush_node_list(cur_list.tail);
                cur_list.tail = p;
                MEM[p as usize].b32.s1 = TEX_NULL
            } else {
                back_input();
            }
        }
        5 => {
            if (cur_list.mode as i32).abs() != 104i32 {
                report_illegal_case();
            } else {
                new_whatsit(4i32 as small_number, 2i32 as small_number);
                scan_int();
                if cur_val <= 0i32 {
                    cur_list.aux.b32.s1 = 0i32
                } else if cur_val > 255i32 {
                    cur_list.aux.b32.s1 = 0i32
                } else {
                    cur_list.aux.b32.s1 = cur_val
                }
                MEM[(cur_list.tail + 1) as usize].b32.s1 = cur_list.aux.b32.s1;
                MEM[(cur_list.tail + 1) as usize].b16.s1 =
                    norm_min(EQTB[(INT_BASE + 51i32) as usize].b32.s1) as u16;
                MEM[(cur_list.tail + 1) as usize].b16.s0 =
                    norm_min(EQTB[(INT_BASE + 52i32) as usize].b32.s1) as u16
            }
        }
        41 => {
            if (cur_list.mode as i32).abs() == 207i32 {
                report_illegal_case();
            } else {
                load_picture(false);
            }
        }
        42 => {
            if (cur_list.mode as i32).abs() == 207i32 {
                report_illegal_case();
            } else {
                load_picture(1i32 != 0);
            }
        }
        43 => {
            if (cur_list.mode as i32).abs() == 1i32 {
                back_input();
                new_graf(1i32 != 0);
            } else if (cur_list.mode as i32).abs() == 207i32 {
                report_illegal_case();
            } else if FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32 == 0xffffu32
                || FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32 == 0xfffeu32
            {
                new_whatsit(42i32 as small_number, 5i32 as small_number);
                scan_int();
                if cur_val < 0i32 || cur_val as i64 > 65535 {
                    if file_line_error_style_p != 0 {
                        print_file_line();
                    } else {
                        print_nl_cstr(b"! ");
                    }
                    print_cstr(b"Bad glyph number");
                    help_ptr = 2_u8;
                    help_line[1] = b"A glyph number must be between 0 and 65535.";
                    help_line[0] = b"I changed this one to zero.";
                    int_error(cur_val);
                    cur_val = 0i32
                }
                MEM[(cur_list.tail + 4) as usize].b16.s2 =
                    EQTB[(CUR_FONT_LOC) as usize].b32.s1 as u16;
                MEM[(cur_list.tail + 4) as usize].b16.s1 = cur_val as u16;
                measure_native_glyph(
                    &mut MEM[cur_list.tail as usize] as *mut memory_word as *mut libc::c_void,
                    (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
                );
            } else {
                not_native_font_error(59i32, 43i32, EQTB[(CUR_FONT_LOC) as usize].b32.s1);
            }
        }
        44 => {
            scan_and_pack_name();
            i = get_encoding_mode_and_info(&mut j);
            if i == 0i32 {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Encoding mode `auto\' is not valid for \\XeTeXinputencoding");
                help_ptr = 2_u8;
                help_line[1] =
                    b"You can\'t use `auto\' encoding here, only for \\XeTeXdefaultencoding.";
                help_line[0] = b"I\'ll ignore this and leave the current encoding unchanged.";
                error();
            } else {
                set_input_file_encoding(INPUT_FILE[IN_OPEN], i, j);
            }
        }
        45 => {
            scan_and_pack_name();
            i = get_encoding_mode_and_info(&mut j);
            EQTB[(INT_BASE + 77i32) as usize].b32.s1 = i;
            EQTB[(INT_BASE + 78i32) as usize].b32.s1 = j
        }
        46 => {
            scan_file_name();
            if length(cur_name) == 0i32 {
                EQTB[(INT_BASE + 68i32) as usize].b32.s1 = 0i32
            } else {
                EQTB[(INT_BASE + 68i32) as usize].b32.s1 = cur_name
            }
        }
        6 => new_whatsit(6i32 as small_number, 2i32 as small_number),
        _ => confusion(b"ext1"),
    };
}
pub(crate) unsafe fn fix_language() {
    let mut l: UTF16_code = 0;
    if EQTB[(INT_BASE + 50i32) as usize].b32.s1 <= 0i32 {
        l = 0i32 as UTF16_code
    } else if EQTB[(INT_BASE + 50i32) as usize].b32.s1 > 255i32 {
        l = 0i32 as UTF16_code
    } else {
        l = EQTB[(INT_BASE + 50i32) as usize].b32.s1 as UTF16_code
    }
    if l as i32 != cur_list.aux.b32.s1 {
        new_whatsit(4i32 as small_number, 2i32 as small_number);
        MEM[(cur_list.tail + 1) as usize].b32.s1 = l as i32;
        cur_list.aux.b32.s1 = l as i32;
        MEM[(cur_list.tail + 1) as usize].b16.s1 =
            norm_min(EQTB[(INT_BASE + 51i32) as usize].b32.s1) as u16;
        MEM[(cur_list.tail + 1) as usize].b16.s0 =
            norm_min(EQTB[(INT_BASE + 52i32) as usize].b32.s1) as u16
    };
}
pub(crate) unsafe fn insert_src_special() {
    let mut toklist: i32 = 0;
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    if SOURCE_FILENAME_STACK[IN_OPEN] > 0i32
        && is_new_source(SOURCE_FILENAME_STACK[IN_OPEN], line) as i32 != 0
    {
        toklist = get_avail();
        p = toklist;
        MEM[p as usize].b32.s0 = 0x1ffffff + (FROZEN_CONTROL_SEQUENCE + 10i32);
        MEM[p as usize].b32.s1 = get_avail();
        p = MEM[p as usize].b32.s1;
        MEM[p as usize].b32.s0 = 0x200000 + '{' as i32;
        q = str_toks(make_src_special(SOURCE_FILENAME_STACK[IN_OPEN], line));
        MEM[p as usize].b32.s1 = MEM[(4999999 - 3) as usize].b32.s1;
        p = q;
        MEM[p as usize].b32.s1 = get_avail();
        p = MEM[p as usize].b32.s1;
        MEM[p as usize].b32.s0 = 0x400000 + '}' as i32;
        begin_token_list(toklist, 5_u16);
        remember_source_info(SOURCE_FILENAME_STACK[IN_OPEN], line);
    };
}
pub(crate) unsafe fn append_src_special() {
    if SOURCE_FILENAME_STACK[IN_OPEN] > 0
        && is_new_source(SOURCE_FILENAME_STACK[IN_OPEN], line) as i32 != 0
    {
        new_whatsit(3i32 as small_number, 2i32 as small_number);
        MEM[(cur_list.tail + 1) as usize].b32.s0 = 0;
        def_ref = get_avail();
        MEM[def_ref as usize].b32.s0 = TEX_NULL;
        str_toks(make_src_special(SOURCE_FILENAME_STACK[IN_OPEN], line));
        MEM[def_ref as usize].b32.s1 = MEM[(4999999 - 3) as usize].b32.s1;
        MEM[(cur_list.tail + 1) as usize].b32.s1 = def_ref;
        remember_source_info(SOURCE_FILENAME_STACK[IN_OPEN], line);
    };
}
pub(crate) unsafe fn handle_right_brace() {
    let mut p: i32 = 0;
    let mut q: i32 = 0;
    let mut d: scaled_t = 0;
    let mut f: i32 = 0;
    match cur_group as i32 {
        1 => unsave(),
        0 => {
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Too many }\'s");
            help_ptr = 2_u8;
            help_line[1] = b"You\'ve closed more groups than you opened.";
            help_line[0] = b"Such booboos are generally harmless, so keep going.";
            error();
        }
        14 | 15 | 16 => extra_right_brace(),
        2 => package(0i32 as small_number),
        3 => {
            adjust_tail = 4999999i32 - 5i32;
            pre_adjust_tail = 4999999i32 - 14i32;
            package(0i32 as small_number);
        }
        4 => {
            end_graf();
            package(0i32 as small_number);
        }
        5 => {
            end_graf();
            package(4i32 as small_number);
        }
        11 => {
            end_graf();
            q = EQTB[(GLUE_BASE + 10i32) as usize].b32.s1;
            MEM[q as usize].b32.s1 += 1;
            d = EQTB[(DIMEN_BASE + 6i32) as usize].b32.s1;
            f = EQTB[(INT_BASE + 42i32) as usize].b32.s1;
            unsave();
            SAVE_PTR -= 2;
            p = vpackage(
                MEM[cur_list.head as usize].b32.s1,
                0i32,
                1i32 as small_number,
                0x3fffffffi32,
            );
            pop_nest();
            if SAVE_STACK[SAVE_PTR + 0].b32.s1 < 255 {
                MEM[cur_list.tail as usize].b32.s1 = get_node(5);
                cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                MEM[cur_list.tail as usize].b16.s1 = 3_u16;
                MEM[cur_list.tail as usize].b16.s0 = SAVE_STACK[SAVE_PTR + 0].b32.s1 as u16;
                MEM[(cur_list.tail + 3) as usize].b32.s1 =
                    MEM[(p + 3) as usize].b32.s1 + MEM[(p + 2) as usize].b32.s1;
                MEM[(cur_list.tail + 4) as usize].b32.s0 = MEM[(p + 5) as usize].b32.s1;
                MEM[(cur_list.tail + 4) as usize].b32.s1 = q;
                MEM[(cur_list.tail + 2) as usize].b32.s1 = d;
                MEM[(cur_list.tail + 1) as usize].b32.s1 = f
            } else {
                MEM[cur_list.tail as usize].b32.s1 = get_node(2);
                cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                MEM[cur_list.tail as usize].b16.s1 = 5_u16;
                MEM[cur_list.tail as usize].b16.s0 = SAVE_STACK[SAVE_PTR + 1].b32.s1 as u16;
                MEM[(cur_list.tail + 1) as usize].b32.s1 = MEM[(p + 5) as usize].b32.s1;
                delete_glue_ref(q);
            }
            free_node(p, 8i32);
            if nest_ptr == 0i32 {
                build_page();
            }
        }
        8 => {
            /*1062:*/
            if cur_input.loc != TEX_NULL
                || cur_input.index as i32 != 7i32 && cur_input.index as i32 != 3i32
            {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Unbalanced output routine");
                help_ptr = 2_u8;
                help_line[1] = b"Your sneaky output routine has problematic {\'s and/or }\'s.";
                help_line[0] = b"I can\'t handle that very well; good luck.";
                error();
                loop {
                    get_token();
                    if !(cur_input.loc != TEX_NULL) {
                        break;
                    }
                }
            }
            end_token_list();
            end_graf();
            unsave();
            output_active = false;
            insert_penalties = 0i32;
            if EQTB[(BOX_BASE + 255i32) as usize].b32.s1 != TEX_NULL {
                if file_line_error_style_p != 0 {
                    print_file_line();
                } else {
                    print_nl_cstr(b"! ");
                }
                print_cstr(b"Output routine didn\'t use all of ");
                print_esc_cstr(b"box");
                print_int(255i32);
                help_ptr = 3_u8;
                help_line[2] = b"Your \\output commands should empty \\box255,";
                help_line[1] = b"e.g., by saying `\\shipout\\box255\'.";
                help_line[0] = b"Proceed; I\'ll discard its present contents.";
                box_error(255i32 as eight_bits);
            }
            if cur_list.tail != cur_list.head {
                MEM[page_tail as usize].b32.s1 = MEM[cur_list.head as usize].b32.s1;
                page_tail = cur_list.tail
            }
            if MEM[(4999999 - 2) as usize].b32.s1 != TEX_NULL {
                if MEM[(4999999 - 1) as usize].b32.s1 == TEX_NULL {
                    (*nest.offset(0)).tail = page_tail
                }
                MEM[page_tail as usize].b32.s1 = MEM[(4999999 - 1) as usize].b32.s1;
                MEM[(4999999 - 1) as usize].b32.s1 = MEM[(4999999 - 2) as usize].b32.s1;
                MEM[(4999999 - 2) as usize].b32.s1 = TEX_NULL;
                page_tail = 4999999i32 - 2i32
            }
            flush_node_list(disc_ptr[2]);
            disc_ptr[2] = TEX_NULL;
            pop_nest();
            build_page();
        }
        10 => build_discretionary(),
        6 => {
            back_input();
            cur_tok = 0x1ffffffi32 + (FROZEN_CONTROL_SEQUENCE + 1i32);
            if file_line_error_style_p != 0 {
                print_file_line();
            } else {
                print_nl_cstr(b"! ");
            }
            print_cstr(b"Missing ");
            print_esc_cstr(b"cr");
            print_cstr(b" inserted");
            help_ptr = 1_u8;
            help_line[0] = b"I\'m guessing that you meant to end an alignment here.";
            ins_error();
        }
        7 => {
            end_graf();
            unsave();
            align_peek();
        }
        12 => {
            end_graf();
            unsave();
            SAVE_PTR -= 2;
            p = vpackage(
                MEM[cur_list.head as usize].b32.s1,
                SAVE_STACK[SAVE_PTR + 1].b32.s1,
                SAVE_STACK[SAVE_PTR + 0].b32.s1 as small_number,
                0x3fffffffi32,
            );
            pop_nest();
            MEM[cur_list.tail as usize].b32.s1 = new_noad();
            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
            MEM[cur_list.tail as usize].b16.s1 = 29_u16;
            MEM[(cur_list.tail + 1) as usize].b32.s1 = 2;
            MEM[(cur_list.tail + 1) as usize].b32.s0 = p
        }
        13 => build_choices(),
        9 => {
            unsave();
            SAVE_PTR -= 1;
            MEM[SAVE_STACK[SAVE_PTR + 0].b32.s1 as usize].b32.s1 = 3i32;
            p = fin_mlist(TEX_NULL);
            MEM[SAVE_STACK[SAVE_PTR + 0].b32.s1 as usize].b32.s0 = p;
            if p != TEX_NULL {
                if MEM[p as usize].b32.s1 == TEX_NULL {
                    if MEM[p as usize].b16.s1 as i32 == 16 {
                        if MEM[(p + 3) as usize].b32.s1 == 0 {
                            if MEM[(p + 2) as usize].b32.s1 == 0 {
                                MEM[SAVE_STACK[SAVE_PTR + 0].b32.s1 as usize].b32 =
                                    MEM[(p + 1) as usize].b32;
                                free_node(p, 4i32);
                            }
                        }
                    } else if MEM[p as usize].b16.s1 as i32 == 28 {
                        if SAVE_STACK[SAVE_PTR + 0].b32.s1 == cur_list.tail + 1i32 {
                            if MEM[cur_list.tail as usize].b16.s1 as i32 == 16 {
                                /*1222:*/
                                q = cur_list.head;
                                while MEM[q as usize].b32.s1 != cur_list.tail {
                                    q = MEM[q as usize].b32.s1
                                }
                                MEM[q as usize].b32.s1 = p;
                                free_node(cur_list.tail, 4i32);
                                cur_list.tail = p
                            }
                        }
                    }
                }
            }
        }
        _ => confusion(b"rightbrace"),
    };
}
pub(crate) unsafe fn main_control() {
    let mut current_block: u64;
    let mut t: i32 = 0;
    if EQTB[(LOCAL_BASE + 7i32) as usize].b32.s1 != TEX_NULL {
        begin_token_list(EQTB[(LOCAL_BASE + 7i32) as usize].b32.s1, 13_u16);
    }
    'c_125208: loop {
        /* big_switch */
        get_x_token();
        loop {
            /*1066: */
            if EQTB[(INT_BASE + 36i32) as usize].b32.s1 > 0i32 {
                show_cur_cmd_chr(); /*:1490 */
            }
            match (cur_list.mode as i32).abs() + cur_cmd as i32 {
                115 | 116 | 172 => {}
                120 => {
                    scan_usv_num();
                    cur_chr = cur_val
                }
                169 => {
                    get_x_token();
                    if cur_cmd as i32 == 11i32
                        || cur_cmd as i32 == 12i32
                        || cur_cmd as i32 == 68i32
                        || cur_cmd as i32 == 16i32
                    {
                        cancel_boundary = true
                    }
                    continue;
                }
                _ => {
                    if (cur_list.mode as i32).abs() == 104i32 {
                        if EQTB[(INT_BASE + 75i32) as usize].b32.s1 > 0i32
                            && space_class != 4096i32
                            && prev_class != 4096i32 - 1i32
                        {
                            prev_class = 4096i32 - 1i32;
                            find_sa_element(
                                6i32 as small_number,
                                space_class * 4096i32 + (4096i32 - 1i32),
                                false,
                            );
                            if cur_ptr != TEX_NULL {
                                if cur_cs == 0i32 {
                                    if cur_cmd as i32 == 16i32 {
                                        cur_cmd = 12i32 as eight_bits
                                    }
                                    cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr
                                } else {
                                    cur_tok = 0x1ffffffi32 + cur_cs
                                }
                                back_input();
                                begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                                continue 'c_125208;
                            }
                        }
                    }
                    match (cur_list.mode as i32).abs() + cur_cmd as i32 {
                        114 => {
                            if cur_list.aux.b32.s0 == 1000i32 {
                                current_block = 1496671425652391013;
                                break;
                            } else {
                                current_block = 11459959175219260272;
                                break;
                            }
                        }
                        168 | 271 => {
                            current_block = 1496671425652391013;
                            break;
                        }
                        40 | 143 | 246 => {
                            if cur_chr == 0i32 {
                                loop {
                                    get_x_token();
                                    if !(cur_cmd as i32 == 10i32) {
                                        break;
                                    }
                                }
                                continue;
                            } else {
                                t = scanner_status as i32;
                                scanner_status = 0_u8;
                                get_next();
                                scanner_status = t as u8;
                                if cur_cs
                                    < 1i32 + (0x10ffffi32 + 1i32) + (0x10ffffi32 + 1i32) + 1i32
                                {
                                    cur_cs = prim_lookup(cur_cs - (1i32 + (0x10ffffi32 + 1i32)))
                                } else {
                                    cur_cs = prim_lookup((*hash.offset(cur_cs as isize)).s1)
                                }
                                if !(cur_cs != 0i32) {
                                    continue 'c_125208;
                                }
                                cur_cmd = prim_eqtb[cur_cs as usize].b16.s1 as eight_bits;
                                cur_chr = prim_eqtb[cur_cs as usize].b32.s1;
                                continue;
                            }
                        }
                        15 => {
                            if its_all_over() {
                                return;
                            }
                            continue 'c_125208;
                        }
                        23 | 125 | 228 | 72 | 175 | 278 | 39 | 45 | 49 | 152 | 7 | 110 | 213 => {
                            report_illegal_case();
                            continue 'c_125208;
                        }
                        8 | 111 | 9 | 112 | 18 | 121 | 70 | 173 | 71 | 174 | 51 | 154 | 16
                        | 119 | 50 | 153 | 53 | 156 | 67 | 170 | 54 | 157 | 55 | 158 | 57 | 160
                        | 56 | 159 | 31 | 134 | 52 | 155 | 29 | 132 | 47 | 150 | 216 | 220
                        | 221 | 234 | 231 | 240 | 243 => {
                            insert_dollar_sign();
                            continue 'c_125208;
                        }
                        37 | 139 | 242 => {
                            MEM[cur_list.tail as usize].b32.s1 = scan_rule_spec();
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            if (cur_list.mode as i32).abs() == 1i32 {
                                cur_list.aux.b32.s1 = -65536000i32
                            } else if (cur_list.mode as i32).abs() == 104i32 {
                                cur_list.aux.b32.s0 = 1000i32
                            }
                            continue 'c_125208;
                        }
                        28 | 130 | 233 | 235 => {
                            append_glue();
                            continue 'c_125208;
                        }
                        30 | 133 | 236 | 237 => {
                            append_kern();
                            continue 'c_125208;
                        }
                        2 | 105 => {
                            new_save_level(1i32 as group_code);
                            continue 'c_125208;
                        }
                        62 | 165 | 268 => {
                            new_save_level(14i32 as group_code);
                            continue 'c_125208;
                        }
                        63 | 166 | 269 => {
                            if cur_group as i32 == 14i32 {
                                unsave();
                            } else {
                                off_save();
                            }
                            continue 'c_125208;
                        }
                        3 | 106 | 209 => {
                            handle_right_brace();
                            continue 'c_125208;
                        }
                        22 | 126 | 229 => {
                            t = cur_chr;
                            scan_dimen(false, false, false);
                            if t == 0i32 {
                                scan_box(cur_val);
                            } else {
                                scan_box(-cur_val);
                            }
                            continue 'c_125208;
                        }
                        32 | 135 | 238 => {
                            scan_box(0x40010001i32 - 100i32 + cur_chr);
                            continue 'c_125208;
                        }
                        21 | 124 | 227 => {
                            begin_box(0i32);
                            continue 'c_125208;
                        }
                        44 => {
                            new_graf(cur_chr > 0i32);
                            continue 'c_125208;
                        }
                        12 | 13 | 17 | 69 | 4 | 24 | 36 | 46 | 48 | 27 | 34 | 65 | 66 => {
                            back_input();
                            new_graf(1i32 != 0);
                            continue 'c_125208;
                        }
                        147 | 250 => {
                            indent_in_hmode();
                            continue 'c_125208;
                        }
                        14 => {
                            normal_paragraph();
                            if cur_list.mode as i32 > 0i32 {
                                build_page();
                            }
                            continue 'c_125208;
                        }
                        117 => {
                            if align_state < 0i32 {
                                off_save();
                            }
                            end_graf();
                            if cur_list.mode as i32 == 1i32 {
                                build_page();
                            }
                            continue 'c_125208;
                        }
                        118 | 131 | 140 | 128 | 136 => {
                            head_for_vmode();
                            continue 'c_125208;
                        }
                        38 | 141 | 244 | 142 | 245 => {
                            begin_insert_or_adjust();
                            continue 'c_125208;
                        }
                        19 | 122 | 225 => {
                            make_mark();
                            continue 'c_125208;
                        }
                        43 | 146 | 249 => {
                            append_penalty();
                            continue 'c_125208;
                        }
                        26 | 129 | 232 => {
                            delete_last();
                            continue 'c_125208;
                        }
                        25 | 127 | 230 => {
                            unpackage();
                            continue 'c_125208;
                        }
                        148 => {
                            append_italic_correction();
                            continue 'c_125208;
                        }
                        251 => {
                            MEM[cur_list.tail as usize].b32.s1 = new_kern(0);
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            continue 'c_125208;
                        }
                        151 | 254 => {
                            append_discretionary();
                            continue 'c_125208;
                        }
                        149 => {
                            make_accent();
                            continue 'c_125208;
                        }
                        6 | 109 | 212 | 5 | 108 | 211 => {
                            align_error();
                            continue 'c_125208;
                        }
                        35 | 138 | 241 => {
                            no_align_error();
                            continue 'c_125208;
                        }
                        64 | 167 | 270 => {
                            omit_error();
                            continue 'c_125208;
                        }
                        33 => {
                            init_align();
                            continue 'c_125208;
                        }
                        137 => {
                            if cur_chr > 0i32 {
                                if eTeX_enabled(
                                    EQTB[(INT_BASE + 71i32) as usize].b32.s1 > 0i32,
                                    cur_cmd as u16,
                                    cur_chr,
                                ) {
                                    MEM[cur_list.tail as usize].b32.s1 =
                                        new_math(0i32, cur_chr as small_number);
                                    cur_list.tail = MEM[cur_list.tail as usize].b32.s1
                                }
                            } else {
                                init_align();
                            }
                            continue 'c_125208;
                        }
                        239 => {
                            if privileged() {
                                if cur_group as i32 == 15i32 {
                                    init_align();
                                } else {
                                    off_save();
                                }
                            }
                            continue 'c_125208;
                        }
                        10 | 113 => {
                            do_endv();
                            continue 'c_125208;
                        }
                        68 | 171 | 274 => {
                            cs_error();
                            continue 'c_125208;
                        }
                        107 => {
                            init_math();
                            continue 'c_125208;
                        }
                        255 => {
                            if privileged() {
                                if cur_group as i32 == 15i32 {
                                    start_eq_no();
                                } else {
                                    off_save();
                                }
                            }
                            continue 'c_125208;
                        }
                        208 => {
                            MEM[cur_list.tail as usize].b32.s1 = new_noad();
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            back_input();
                            scan_math(cur_list.tail + 1i32);
                            continue 'c_125208;
                        }
                        218 | 219 | 275 => {
                            set_math_char(EQTB[(MATH_CODE_BASE + cur_chr) as usize].b32.s1);
                            continue 'c_125208;
                        }
                        223 => {
                            scan_char_num();
                            cur_chr = cur_val;
                            set_math_char(EQTB[(MATH_CODE_BASE + cur_chr) as usize].b32.s1);
                            continue 'c_125208;
                        }
                        224 => {
                            if cur_chr == 2i32 {
                                scan_math_class_int();
                                t = ((cur_val as u32 & 0x7_u32) << 21i32) as i32;
                                scan_math_fam_int();
                                t = (t as u32).wrapping_add((cur_val as u32 & 0xff_u32) << 24i32)
                                    as i32;
                                scan_usv_num();
                                t = t + cur_val;
                                set_math_char(t);
                            } else if cur_chr == 1i32 {
                                scan_xetex_math_char_int();
                                set_math_char(cur_val);
                            } else {
                                scan_fifteen_bit_int();
                                set_math_char(
                                    (((cur_val / 4096i32) as u32 & 0x7_u32) << 21i32)
                                        .wrapping_add(
                                            ((cur_val % 4096i32 / 256i32) as u32 & 0xff_u32)
                                                << 24i32,
                                        )
                                        .wrapping_add((cur_val % 256i32) as u32)
                                        as i32,
                                );
                            }
                            continue 'c_125208;
                        }
                        276 => {
                            set_math_char(
                                (((cur_chr / 4096i32) as u32 & 0x7_u32) << 21i32)
                                    .wrapping_add(
                                        ((cur_chr % 4096i32 / 256i32) as u32 & 0xff_u32) << 24i32,
                                    )
                                    .wrapping_add((cur_chr % 256i32) as u32)
                                    as i32,
                            );
                            continue 'c_125208;
                        }
                        277 => {
                            set_math_char(cur_chr);
                            continue 'c_125208;
                        }
                        222 => {
                            if cur_chr == 1i32 {
                                scan_math_class_int();
                                t = ((cur_val as u32 & 0x7_u32) << 21i32) as i32;
                                scan_math_fam_int();
                                t = (t as u32).wrapping_add((cur_val as u32 & 0xff_u32) << 24i32)
                                    as i32;
                                scan_usv_num();
                                t = t + cur_val;
                                set_math_char(t);
                            } else {
                                scan_delimiter_int();
                                cur_val = cur_val / 4096i32;
                                set_math_char(
                                    (((cur_val / 4096i32) as u32 & 0x7_u32) << 21i32)
                                        .wrapping_add(
                                            ((cur_val % 4096i32 / 256i32) as u32 & 0xff_u32)
                                                << 24i32,
                                        )
                                        .wrapping_add((cur_val % 256i32) as u32)
                                        as i32,
                                );
                            }
                            continue 'c_125208;
                        }
                        257 => {
                            MEM[cur_list.tail as usize].b32.s1 = new_noad();
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            MEM[cur_list.tail as usize].b16.s1 = cur_chr as u16;
                            scan_math(cur_list.tail + 1i32);
                            continue 'c_125208;
                        }
                        258 => {
                            math_limit_switch();
                            continue 'c_125208;
                        }
                        273 => {
                            math_radical();
                            continue 'c_125208;
                        }
                        252 | 253 => {
                            math_ac();
                            continue 'c_125208;
                        }
                        263 => {
                            scan_spec(12i32 as group_code, false);
                            normal_paragraph();
                            push_nest();
                            cur_list.mode = -1_i16;
                            cur_list.aux.b32.s1 = -65536000i32;
                            if insert_src_special_every_vbox {
                                insert_src_special();
                            }
                            if EQTB[(LOCAL_BASE + 6i32) as usize].b32.s1 != TEX_NULL {
                                begin_token_list(EQTB[(LOCAL_BASE + 6i32) as usize].b32.s1, 12_u16);
                            }
                            continue 'c_125208;
                        }
                        260 => {
                            MEM[cur_list.tail as usize].b32.s1 = new_style(cur_chr as small_number);
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            continue 'c_125208;
                        }
                        262 => {
                            MEM[cur_list.tail as usize].b32.s1 = new_glue(0);
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            MEM[cur_list.tail as usize].b16.s0 = 98_u16;
                            continue 'c_125208;
                        }
                        261 => {
                            append_choices();
                            continue 'c_125208;
                        }
                        215 | 214 => {
                            sub_sup();
                            continue 'c_125208;
                        }
                        259 => {
                            math_fraction();
                            continue 'c_125208;
                        }
                        256 => {
                            math_left_right();
                            continue 'c_125208;
                        }
                        210 => {
                            if cur_group as i32 == 15i32 {
                                after_math();
                            } else {
                                off_save();
                            }
                            continue 'c_125208;
                        }
                        73 | 176 | 279 | 74 | 177 | 280 | 75 | 178 | 281 | 76 | 179 | 282 | 77
                        | 180 | 283 | 78 | 181 | 284 | 79 | 182 | 285 | 80 | 183 | 286 | 81
                        | 184 | 287 | 82 | 185 | 288 | 83 | 186 | 289 | 84 | 187 | 290 | 85
                        | 188 | 291 | 86 | 189 | 292 | 87 | 190 | 293 | 88 | 191 | 294 | 89
                        | 192 | 295 | 90 | 193 | 296 | 91 | 194 | 297 | 92 | 195 | 298 | 93
                        | 196 | 299 | 94 | 197 | 300 | 95 | 198 | 301 | 96 | 199 | 302 | 97
                        | 200 | 303 | 98 | 201 | 304 | 99 | 202 | 305 | 100 | 203 | 306 | 101
                        | 204 | 307 | 102 | 205 | 308 | 103 | 206 | 309 => {
                            prefixed_command();
                            continue 'c_125208;
                        }
                        41 | 144 | 247 => {
                            get_token();
                            after_token = cur_tok;
                            continue 'c_125208;
                        }
                        42 | 145 | 248 => {
                            get_token();
                            save_for_after(cur_tok);
                            continue 'c_125208;
                        }
                        61 | 164 | 267 => {
                            open_or_close_in();
                            continue 'c_125208;
                        }
                        59 | 162 | 265 => {
                            issue_message();
                            continue 'c_125208;
                        }
                        58 | 161 | 264 => {
                            shift_case();
                            continue 'c_125208;
                        }
                        20 | 123 | 226 => {
                            show_whatever();
                            continue 'c_125208;
                        }
                        60 | 163 | 266 => {
                            do_extension();
                            continue 'c_125208;
                        }
                        1 | 104 | 207 | 11 | 217 | 272 | _ => continue 'c_125208,
                    }
                }
            }
            /*main_loop *//*1069: */
            if cur_list.head == cur_list.tail && cur_list.mode as i32 > 0i32 {
                if insert_src_special_auto {
                    append_src_special();
                }
            }
            prev_class = 4096i32 - 1i32;
            if FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32 == 0xffffu32
                || FONT_AREA[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] as u32 == 0xfffeu32
            {
                if cur_list.mode as i32 > 0i32 {
                    if EQTB[(INT_BASE + 50i32) as usize].b32.s1 != cur_list.aux.b32.s1 {
                        fix_language();
                    }
                }
                main_h = 0i32;
                main_f = EQTB[(CUR_FONT_LOC) as usize].b32.s1;
                native_len = 0i32;
                loop {
                    /*collect_native */
                    main_s = (EQTB[(SF_CODE_BASE + cur_chr) as usize].b32.s1 as i64 % 65536) as i32;
                    if main_s == 1000i32 {
                        cur_list.aux.b32.s0 = 1000i32
                    } else if main_s < 1000i32 {
                        if main_s > 0i32 {
                            cur_list.aux.b32.s0 = main_s
                        }
                    } else if cur_list.aux.b32.s0 < 1000i32 {
                        cur_list.aux.b32.s0 = 1000i32
                    } else {
                        cur_list.aux.b32.s0 = main_s
                    }
                    cur_ptr = TEX_NULL;
                    space_class =
                        (EQTB[(SF_CODE_BASE + cur_chr) as usize].b32.s1 as i64 / 65536) as i32;
                    if EQTB[(INT_BASE + 75i32) as usize].b32.s1 > 0i32 && space_class != 4096i32 {
                        if prev_class == 4096i32 - 1i32 {
                            if cur_input.state as i32 != 0i32 || cur_input.index as i32 != 4i32 {
                                find_sa_element(
                                    6i32 as small_number,
                                    (4096i32 - 1i32) * 4096i32 + space_class,
                                    false,
                                );
                                if cur_ptr != TEX_NULL {
                                    if cur_cmd as i32 != 11i32 {
                                        cur_cmd = 12i32 as eight_bits
                                    }
                                    cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr;
                                    back_input();
                                    cur_input.index = 4_u16;
                                    begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                                    continue 'c_125208;
                                }
                            }
                        } else {
                            find_sa_element(
                                6i32 as small_number,
                                prev_class * 4096i32 + space_class,
                                false,
                            );
                            if cur_ptr != TEX_NULL {
                                if cur_cmd as i32 != 11i32 {
                                    cur_cmd = 12i32 as eight_bits
                                }
                                cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr;
                                back_input();
                                cur_input.index = 4_u16;
                                begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                                prev_class = 4096i32 - 1i32;
                                current_block = 9706274459985797855;
                                break;
                            }
                        }
                        prev_class = space_class
                    }
                    if cur_chr as i64 > 65535 {
                        while native_text_size <= native_len + 2i32 {
                            native_text_size = native_text_size + 128i32;
                            native_text = xrealloc(
                                native_text as *mut libc::c_void,
                                (native_text_size as u64).wrapping_mul(::std::mem::size_of::<
                                    UTF16_code,
                                >(
                                )
                                    as u64) as _,
                            ) as *mut UTF16_code
                        }
                        *native_text.offset(native_len as isize) =
                            ((cur_chr as i64 - 65536) / 1024i32 as i64 + 0xd800i32 as i64)
                                as UTF16_code;
                        native_len += 1;
                        *native_text.offset(native_len as isize) =
                            ((cur_chr as i64 - 65536) % 1024i32 as i64 + 0xdc00i32 as i64)
                                as UTF16_code;
                        native_len += 1
                    } else {
                        while native_text_size <= native_len + 1i32 {
                            native_text_size = native_text_size + 128i32;
                            native_text = xrealloc(
                                native_text as *mut libc::c_void,
                                (native_text_size as u64).wrapping_mul(::std::mem::size_of::<
                                    UTF16_code,
                                >(
                                )
                                    as u64) as _,
                            ) as *mut UTF16_code
                        }
                        *native_text.offset(native_len as isize) = cur_chr as UTF16_code;
                        native_len += 1
                    }
                    is_hyph = cur_chr == HYPHEN_CHAR[main_f as usize]
                        || EQTB[(INT_BASE + 72i32) as usize].b32.s1 > 0i32
                            && (cur_chr == 8212i32 || cur_chr == 8211i32);
                    if main_h == 0i32 && is_hyph as i32 != 0 {
                        main_h = native_len
                    }
                    get_next();
                    if cur_cmd as i32 == 11i32 || cur_cmd as i32 == 12i32 || cur_cmd as i32 == 68i32
                    {
                        continue;
                    }
                    x_token();
                    if cur_cmd as i32 == 11i32 || cur_cmd as i32 == 12i32 || cur_cmd as i32 == 68i32
                    {
                        continue;
                    }
                    if cur_cmd as i32 == 16i32 {
                        scan_usv_num();
                        cur_chr = cur_val
                    } else if EQTB[(INT_BASE + 75i32) as usize].b32.s1 > 0i32
                        && space_class != 4096i32
                        && prev_class != 4096i32 - 1i32
                    {
                        current_block = 14170946608255986518;
                        break;
                    } else {
                        current_block = 9706274459985797855;
                        break;
                    }
                }
                match current_block {
                    14170946608255986518 => {
                        prev_class = 4096i32 - 1i32;
                        find_sa_element(
                            6i32 as small_number,
                            space_class * 4096i32 + (4096i32 - 1i32),
                            false,
                        );
                        if cur_ptr != TEX_NULL {
                            if cur_cs == 0i32 {
                                if cur_cmd as i32 == 16i32 {
                                    cur_cmd = 12i32 as eight_bits
                                }
                                cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr
                            } else {
                                cur_tok = 0x1ffffffi32 + cur_cs
                            }
                            back_input();
                            begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                        }
                    }
                    _ => {}
                }
                /*collected */
                if !(FONT_MAPPING[main_f as usize]).is_null() {
                    main_k = apply_mapping(FONT_MAPPING[main_f as usize], native_text, native_len);
                    native_len = 0i32;
                    while native_text_size <= native_len + main_k {
                        native_text_size = native_text_size + 128i32;
                        native_text = xrealloc(
                            native_text as *mut libc::c_void,
                            (native_text_size as u64)
                                .wrapping_mul(::std::mem::size_of::<UTF16_code>() as u64)
                                as _,
                        ) as *mut UTF16_code
                    }
                    main_h = 0i32;
                    let mut for_end: i32 = 0;
                    main_p = 0i32;
                    for_end = main_k - 1i32;
                    if main_p <= for_end {
                        loop {
                            *native_text.offset(native_len as isize) =
                                *mapped_text.offset(main_p as isize);
                            native_len += 1;
                            if main_h == 0i32
                                && (*mapped_text.offset(main_p as isize) as i32
                                    == HYPHEN_CHAR[main_f as usize]
                                    || EQTB[(INT_BASE + 72i32) as usize].b32.s1 > 0i32
                                        && (*mapped_text.offset(main_p as isize) as i32 == 8212i32
                                            || *mapped_text.offset(main_p as isize) as i32
                                                == 8211i32))
                            {
                                main_h = native_len
                            }
                            let fresh88 = main_p;
                            main_p = main_p + 1;
                            if !(fresh88 < for_end) {
                                break;
                            }
                        }
                    }
                }
                if EQTB[(INT_BASE + 35i32) as usize].b32.s1 > 0i32 {
                    temp_ptr = 0i32;
                    while temp_ptr < native_len {
                        main_k = *native_text.offset(temp_ptr as isize) as font_index;
                        temp_ptr += 1;
                        if main_k >= 0xd800i32 && main_k < 0xdc00i32 {
                            main_k =
                                (65536 + ((main_k - 0xd800i32) * 1024i32) as i64) as font_index;
                            main_k =
                                main_k + *native_text.offset(temp_ptr as isize) as i32 - 0xdc00i32;
                            temp_ptr += 1
                        }
                        if map_char_to_glyph(main_f, main_k) == 0i32 {
                            char_warning(main_f, main_k);
                        }
                    }
                }
                main_k = native_len;
                main_pp = cur_list.tail;
                if cur_list.mode as i32 == 104i32 {
                    main_ppp = cur_list.head;
                    if main_ppp != main_pp {
                        while MEM[main_ppp as usize].b32.s1 != main_pp {
                            if !is_char_node(main_ppp) && MEM[main_ppp as usize].b16.s1 as i32 == 7
                            {
                                temp_ptr = main_ppp;
                                let mut for_end_0: i32 = 0;
                                main_p = 1i32;
                                for_end_0 = MEM[temp_ptr as usize].b16.s0 as i32;
                                if main_p <= for_end_0 {
                                    loop {
                                        main_ppp = MEM[main_ppp as usize].b32.s1;
                                        let fresh89 = main_p;
                                        main_p = main_p + 1;
                                        if !(fresh89 < for_end_0) {
                                            break;
                                        }
                                    }
                                }
                            }
                            if main_ppp != main_pp {
                                main_ppp = MEM[main_ppp as usize].b32.s1
                            }
                        }
                    }
                    temp_ptr = 0i32;
                    loop {
                        if main_h == 0i32 {
                            main_h = main_k
                        }
                        if main_pp != TEX_NULL
                            && !is_char_node(main_pp)
                            && MEM[main_pp as usize].b16.s1 as i32 == 8
                            && (MEM[main_pp as usize].b16.s0 as i32 == 40
                                || MEM[main_pp as usize].b16.s0 as i32 == 41)
                            && MEM[(main_pp + 4) as usize].b16.s2 as i32 == main_f
                            && main_ppp != main_pp
                            && !is_char_node(main_ppp)
                            && MEM[main_ppp as usize].b16.s1 as i32 != 7
                        {
                            main_k = main_h + MEM[(main_pp + 4) as usize].b16.s1 as i32;
                            while native_text_size <= native_len + main_k {
                                native_text_size = native_text_size + 128i32;
                                native_text = xrealloc(
                                    native_text as *mut libc::c_void,
                                    (native_text_size as u64).wrapping_mul(::std::mem::size_of::<
                                        UTF16_code,
                                    >(
                                    )
                                        as u64) as _,
                                ) as *mut UTF16_code
                            }
                            save_native_len = native_len;
                            let mut for_end_1: i32 = 0;
                            main_p = 0i32;
                            for_end_1 = MEM[(main_pp + 4) as usize].b16.s1 as i32 - 1;
                            if main_p <= for_end_1 {
                                loop {
                                    *native_text.offset(native_len as isize) =
                                        *(&mut MEM[(main_pp + 6) as usize] as *mut memory_word
                                            as *mut u16)
                                            .offset(main_p as isize);
                                    native_len += 1;
                                    let fresh90 = main_p;
                                    main_p = main_p + 1;
                                    if !(fresh90 < for_end_1) {
                                        break;
                                    }
                                }
                            }
                            let mut for_end_2: i32 = 0;
                            main_p = 0i32;
                            for_end_2 = main_h - 1i32;
                            if main_p <= for_end_2 {
                                loop {
                                    *native_text.offset(native_len as isize) =
                                        *native_text.offset((temp_ptr + main_p) as isize);
                                    native_len += 1;
                                    let fresh91 = main_p;
                                    main_p = main_p + 1;
                                    if !(fresh91 < for_end_2) {
                                        break;
                                    }
                                }
                            }
                            do_locale_linebreaks(save_native_len, main_k);
                            native_len = save_native_len;
                            main_k = native_len - main_h - temp_ptr;
                            temp_ptr = main_h;
                            main_h = 0i32;
                            while main_h < main_k
                                && *native_text.offset((temp_ptr + main_h) as isize) as i32
                                    != HYPHEN_CHAR[main_f as usize]
                                && (!(EQTB[(INT_BASE + 72i32) as usize].b32.s1 > 0i32)
                                    || *native_text.offset((temp_ptr + main_h) as isize) as i32
                                        != 8212i32
                                        && *native_text.offset((temp_ptr + main_h) as isize) as i32
                                            != 8211i32)
                            {
                                main_h += 1
                            }
                            if main_h < main_k {
                                main_h += 1
                            }
                            MEM[main_ppp as usize].b32.s1 = MEM[main_pp as usize].b32.s1;
                            MEM[main_pp as usize].b32.s1 = TEX_NULL;
                            flush_node_list(main_pp);
                            main_pp = cur_list.tail;
                            while MEM[main_ppp as usize].b32.s1 != main_pp {
                                main_ppp = MEM[main_ppp as usize].b32.s1
                            }
                        } else {
                            do_locale_linebreaks(temp_ptr, main_h);
                            temp_ptr = temp_ptr + main_h;
                            main_k = main_k - main_h;
                            main_h = 0i32;
                            while main_h < main_k
                                && *native_text.offset((temp_ptr + main_h) as isize) as i32
                                    != HYPHEN_CHAR[main_f as usize]
                                && (!(EQTB[(INT_BASE + 72i32) as usize].b32.s1 > 0i32)
                                    || *native_text.offset((temp_ptr + main_h) as isize) as i32
                                        != 8212i32
                                        && *native_text.offset((temp_ptr + main_h) as isize) as i32
                                            != 8211i32)
                            {
                                main_h += 1
                            }
                            if main_h < main_k {
                                main_h += 1
                            }
                        }
                        if main_k > 0i32 || is_hyph as i32 != 0 {
                            MEM[cur_list.tail as usize].b32.s1 = new_disc();
                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                            main_pp = cur_list.tail
                        }
                        if main_k == 0i32 {
                            break;
                        }
                    }
                } else {
                    main_ppp = cur_list.head;
                    if main_ppp != main_pp {
                        while MEM[main_ppp as usize].b32.s1 != main_pp {
                            if !is_char_node(main_ppp) && MEM[main_ppp as usize].b16.s1 as i32 == 7
                            {
                                temp_ptr = main_ppp;
                                let mut for_end_3: i32 = 0;
                                main_p = 1i32;
                                for_end_3 = MEM[temp_ptr as usize].b16.s0 as i32;
                                if main_p <= for_end_3 {
                                    loop {
                                        main_ppp = MEM[main_ppp as usize].b32.s1;
                                        let fresh92 = main_p;
                                        main_p = main_p + 1;
                                        if !(fresh92 < for_end_3) {
                                            break;
                                        }
                                    }
                                }
                            }
                            if main_ppp != main_pp {
                                main_ppp = MEM[main_ppp as usize].b32.s1
                            }
                        }
                    }
                    if main_pp != TEX_NULL
                        && !is_char_node(main_pp)
                        && MEM[main_pp as usize].b16.s1 as i32 == 8
                        && (MEM[main_pp as usize].b16.s0 as i32 == 40
                            || MEM[main_pp as usize].b16.s0 as i32 == 41)
                        && MEM[(main_pp + 4) as usize].b16.s2 as i32 == main_f
                        && main_ppp != main_pp
                        && !is_char_node(main_ppp)
                        && MEM[main_ppp as usize].b16.s1 as i32 != 7
                    {
                        MEM[main_pp as usize].b32.s1 = new_native_word_node(
                            main_f,
                            main_k + MEM[(main_pp + 4) as usize].b16.s1 as i32,
                        );
                        cur_list.tail = MEM[main_pp as usize].b32.s1;
                        let mut for_end_4: i32 = 0;
                        main_p = 0i32;
                        for_end_4 = MEM[(main_pp + 4) as usize].b16.s1 as i32 - 1;
                        if main_p <= for_end_4 {
                            loop {
                                *(&mut MEM[(cur_list.tail + 6) as usize] as *mut memory_word
                                    as *mut u16)
                                    .offset(main_p as isize) = *(&mut MEM[(main_pp + 6) as usize]
                                    as *mut memory_word
                                    as *mut u16)
                                    .offset(main_p as isize);
                                let fresh93 = main_p;
                                main_p = main_p + 1;
                                if !(fresh93 < for_end_4) {
                                    break;
                                }
                            }
                        }
                        let mut for_end_5: i32 = 0;
                        main_p = 0i32;
                        for_end_5 = main_k - 1i32;
                        if main_p <= for_end_5 {
                            loop {
                                *(&mut MEM[(cur_list.tail + 6) as usize] as *mut memory_word
                                    as *mut u16)
                                    .offset(
                                        (main_p + MEM[(main_pp + 4) as usize].b16.s1 as i32)
                                            as isize,
                                    ) = *native_text.offset(main_p as isize);
                                let fresh94 = main_p;
                                main_p = main_p + 1;
                                if !(fresh94 < for_end_5) {
                                    break;
                                }
                            }
                        }
                        measure_native_node(
                            &mut MEM[cur_list.tail as usize] as *mut memory_word
                                as *mut libc::c_void,
                            (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
                        );
                        main_p = cur_list.head;
                        if main_p != main_pp {
                            while MEM[main_p as usize].b32.s1 != main_pp {
                                main_p = MEM[main_p as usize].b32.s1
                            }
                        }
                        MEM[main_p as usize].b32.s1 = MEM[main_pp as usize].b32.s1;
                        MEM[main_pp as usize].b32.s1 = TEX_NULL;
                        flush_node_list(main_pp);
                    } else {
                        MEM[main_pp as usize].b32.s1 = new_native_word_node(main_f, main_k);
                        cur_list.tail = MEM[main_pp as usize].b32.s1;
                        let mut for_end_6: i32 = 0;
                        main_p = 0i32;
                        for_end_6 = main_k - 1i32;
                        if main_p <= for_end_6 {
                            loop {
                                *(&mut MEM[(cur_list.tail + 6) as usize] as *mut memory_word
                                    as *mut u16)
                                    .offset(main_p as isize) = *native_text.offset(main_p as isize);
                                let fresh95 = main_p;
                                main_p = main_p + 1;
                                if !(fresh95 < for_end_6) {
                                    break;
                                }
                            }
                        }
                        measure_native_node(
                            &mut MEM[cur_list.tail as usize] as *mut memory_word
                                as *mut libc::c_void,
                            (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
                        );
                    }
                }
                if EQTB[(INT_BASE + 80i32) as usize].b32.s1 > 0i32 {
                    main_p = cur_list.head;
                    main_pp = TEX_NULL;
                    while main_p != cur_list.tail {
                        if main_p != TEX_NULL
                            && !is_char_node(main_p)
                            && MEM[main_p as usize].b16.s1 as i32 == 8
                            && (MEM[main_p as usize].b16.s0 as i32 == 40
                                || MEM[main_p as usize].b16.s0 as i32 == 41)
                        {
                            main_pp = main_p
                        }
                        main_p = MEM[main_p as usize].b32.s1
                    }
                    if main_pp != TEX_NULL {
                        if MEM[(main_pp + 4) as usize].b16.s2 as i32 == main_f {
                            main_p = MEM[main_pp as usize].b32.s1;
                            while !is_char_node(main_p)
                                && (MEM[main_p as usize].b16.s1 as i32 == 12
                                    || MEM[main_p as usize].b16.s1 as i32 == 3
                                    || MEM[main_p as usize].b16.s1 as i32 == 4
                                    || MEM[main_p as usize].b16.s1 as i32 == 5
                                    || MEM[main_p as usize].b16.s1 as i32 == 8
                                        && MEM[main_p as usize].b16.s0 as i32 <= 4)
                            {
                                main_p = MEM[main_p as usize].b32.s1
                            }
                            if !is_char_node(main_p) && MEM[main_p as usize].b16.s1 as i32 == 10 {
                                main_ppp = MEM[main_p as usize].b32.s1;
                                while !is_char_node(main_ppp)
                                    && (MEM[main_ppp as usize].b16.s1 as i32 == 12
                                        || MEM[main_ppp as usize].b16.s1 as i32 == 3
                                        || MEM[main_ppp as usize].b16.s1 as i32 == 4
                                        || MEM[main_ppp as usize].b16.s1 as i32 == 5
                                        || MEM[main_ppp as usize].b16.s1 as i32 == 8
                                            && MEM[main_ppp as usize].b16.s0 as i32 <= 4)
                                {
                                    main_ppp = MEM[main_ppp as usize].b32.s1
                                }
                                if main_ppp == cur_list.tail {
                                    temp_ptr = new_native_word_node(
                                        main_f,
                                        MEM[(main_pp + 4) as usize].b16.s1 as i32
                                            + 1i32
                                            + MEM[(cur_list.tail + 4) as usize].b16.s1 as i32,
                                    );
                                    main_k = 0i32;
                                    let mut for_end_7: i32 = 0;
                                    t = 0i32;
                                    for_end_7 = MEM[(main_pp + 4) as usize].b16.s1 as i32 - 1;
                                    if t <= for_end_7 {
                                        loop {
                                            *(&mut MEM[(temp_ptr + 6) as usize]
                                                as *mut memory_word
                                                as *mut u16)
                                                .offset(main_k as isize) = *(&mut MEM
                                                [(main_pp + 6i32) as usize]
                                                as *mut memory_word
                                                as *mut u16)
                                                .offset(t as isize);
                                            main_k += 1;
                                            let fresh96 = t;
                                            t = t + 1;
                                            if !(fresh96 < for_end_7) {
                                                break;
                                            }
                                        }
                                    }
                                    *(&mut MEM[(temp_ptr + 6) as usize] as *mut memory_word
                                        as *mut u16)
                                        .offset(main_k as isize) = ' ' as i32 as u16;
                                    main_k += 1;
                                    let mut for_end_8: i32 = 0;
                                    t = 0i32;
                                    for_end_8 = MEM[(cur_list.tail + 4) as usize].b16.s1 as i32 - 1;
                                    if t <= for_end_8 {
                                        loop {
                                            *(&mut MEM[(temp_ptr + 6) as usize]
                                                as *mut memory_word
                                                as *mut u16)
                                                .offset(main_k as isize) = *(&mut MEM
                                                [(cur_list.tail + 6i32) as usize]
                                                as *mut memory_word
                                                as *mut u16)
                                                .offset(t as isize);
                                            main_k += 1;
                                            let fresh97 = t;
                                            t = t + 1;
                                            if !(fresh97 < for_end_8) {
                                                break;
                                            }
                                        }
                                    }
                                    measure_native_node(
                                        &mut MEM[temp_ptr as usize] as *mut memory_word
                                            as *mut libc::c_void,
                                        (EQTB[(INT_BASE + 74i32) as usize].b32.s1 > 0i32) as i32,
                                    );
                                    t = MEM[(temp_ptr + 1) as usize].b32.s1
                                        - MEM[(main_pp + 1) as usize].b32.s1
                                        - MEM[(cur_list.tail + 1) as usize].b32.s1;
                                    free_node(temp_ptr, MEM[(temp_ptr + 4) as usize].b16.s3 as i32);
                                    if t != MEM[(FONT_GLUE[main_f as usize] + 1i32) as usize].b32.s1
                                    {
                                        temp_ptr = new_kern(
                                            t - MEM[(FONT_GLUE[main_f as usize] + 1) as usize]
                                                .b32
                                                .s1,
                                        );
                                        MEM[temp_ptr as usize].b16.s0 = 3_u16;
                                        MEM[temp_ptr as usize].b32.s1 = MEM[main_p as usize].b32.s1;
                                        MEM[main_p as usize].b32.s1 = temp_ptr
                                    }
                                }
                            }
                        }
                    }
                }
                if cur_ptr != TEX_NULL {
                    continue 'c_125208;
                }
            } else {
                main_s = (EQTB[(SF_CODE_BASE + cur_chr) as usize].b32.s1 as i64 % 65536) as i32;
                if main_s == 1000i32 {
                    cur_list.aux.b32.s0 = 1000i32
                } else if main_s < 1000i32 {
                    if main_s > 0i32 {
                        cur_list.aux.b32.s0 = main_s
                    }
                } else if cur_list.aux.b32.s0 < 1000i32 {
                    cur_list.aux.b32.s0 = 1000i32
                } else {
                    cur_list.aux.b32.s0 = main_s
                }
                cur_ptr = TEX_NULL;
                space_class =
                    (EQTB[(SF_CODE_BASE + cur_chr) as usize].b32.s1 as i64 / 65536) as i32;
                if EQTB[(INT_BASE + 75i32) as usize].b32.s1 > 0i32 && space_class != 4096i32 {
                    if prev_class == 4096i32 - 1i32 {
                        if cur_input.state as i32 != 0i32 || cur_input.index as i32 != 4i32 {
                            find_sa_element(
                                6i32 as small_number,
                                (4096i32 - 1i32) * 4096i32 + space_class,
                                false,
                            );
                            if cur_ptr != TEX_NULL {
                                if cur_cmd as i32 != 11i32 {
                                    cur_cmd = 12i32 as eight_bits
                                }
                                cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr;
                                back_input();
                                cur_input.index = 4_u16;
                                begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                                continue 'c_125208;
                            }
                        }
                    } else {
                        find_sa_element(
                            6i32 as small_number,
                            prev_class * 4096i32 + space_class,
                            false,
                        );
                        if cur_ptr != TEX_NULL {
                            if cur_cmd as i32 != 11i32 {
                                cur_cmd = 12i32 as eight_bits
                            }
                            cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr;
                            back_input();
                            cur_input.index = 4_u16;
                            begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                            prev_class = 4096i32 - 1i32;
                            continue 'c_125208;
                        }
                    }
                    prev_class = space_class
                }
                main_f = EQTB[(CUR_FONT_LOC) as usize].b32.s1;
                bchar = FONT_BCHAR[main_f as usize];
                false_bchar = FONT_FALSE_BCHAR[main_f as usize];
                if cur_list.mode as i32 > 0i32 {
                    if EQTB[(INT_BASE + 50i32) as usize].b32.s1 != cur_list.aux.b32.s1 {
                        fix_language();
                    }
                }
                lig_stack = avail;
                if lig_stack == TEX_NULL {
                    lig_stack = get_avail()
                } else {
                    avail = MEM[lig_stack as usize].b32.s1;
                    MEM[lig_stack as usize].b32.s1 = TEX_NULL
                }
                MEM[lig_stack as usize].b16.s1 = main_f as u16;
                cur_l = cur_chr;
                MEM[lig_stack as usize].b16.s0 = cur_l as u16;
                cur_q = cur_list.tail;
                if cancel_boundary {
                    cancel_boundary = false;
                    main_k = 0i32
                } else {
                    main_k = BCHAR_LABEL[main_f as usize]
                }
                if main_k == 0i32 {
                    current_block = 249799543778823886;
                } else {
                    cur_r = cur_l;
                    cur_l = 65536i32;
                    current_block = 13962460947151495567;
                }
                'c_125239: loop {
                    match current_block {
                        13962460947151495567 => {
                            /*main_lig_loop 1 */
                            main_j = FONT_INFO[main_k as usize].b16;
                            current_block = 11331079115679122507;
                        }
                        _ =>
                        /*main_loop_move 2 */
                        {
                            if effective_char(false, main_f, cur_chr as u16)
                                > FONT_EC[main_f as usize] as i32
                                || effective_char(false, main_f, cur_chr as u16)
                                    < FONT_BC[main_f as usize] as i32
                            {
                                char_warning(main_f, cur_chr);
                                MEM[lig_stack as usize].b32.s1 = avail;
                                avail = lig_stack;
                                continue 'c_125208;
                            } else {
                                main_i = effective_char_info(main_f, cur_l as u16);
                                if !(main_i.s3 as i32 > 0i32) {
                                    char_warning(main_f, cur_chr);
                                    MEM[lig_stack as usize].b32.s1 = avail;
                                    avail = lig_stack;
                                    continue 'c_125208;
                                } else {
                                    MEM[cur_list.tail as usize].b32.s1 = lig_stack;
                                    cur_list.tail = lig_stack
                                }
                            }
                            current_block = 18270385712206273994;
                        }
                    }
                    'c_125244: loop {
                        match current_block {
                            11331079115679122507 =>
                            /*main_lig_loop 2 */
                            {
                                if main_j.s2 as i32 == cur_r {
                                    if main_j.s3 as i32 <= 128i32 {
                                        /*1075: */
                                        if main_j.s1 as i32 >= 128i32 {
                                            if cur_l < 65536i32 {
                                                if MEM[cur_q as usize].b32.s1 > TEX_NULL {
                                                    if MEM[cur_list.tail as usize].b16.s0 as i32
                                                        == HYPHEN_CHAR[main_f as usize]
                                                    {
                                                        ins_disc = true
                                                    }
                                                }
                                                if ligature_present {
                                                    main_p = new_ligature(
                                                        main_f,
                                                        cur_l as u16,
                                                        MEM[cur_q as usize].b32.s1,
                                                    );
                                                    if lft_hit {
                                                        MEM[main_p as usize].b16.s0 = 2_u16;
                                                        lft_hit = false
                                                    }
                                                    if rt_hit {
                                                        if lig_stack == TEX_NULL {
                                                            MEM[main_p as usize].b16.s0 += 1;
                                                            rt_hit = false
                                                        }
                                                    }
                                                    MEM[cur_q as usize].b32.s1 = main_p;
                                                    cur_list.tail = main_p;
                                                    ligature_present = false
                                                }
                                                if ins_disc {
                                                    ins_disc = false;
                                                    if cur_list.mode as i32 > 0i32 {
                                                        MEM[cur_list.tail as usize].b32.s1 =
                                                            new_disc();
                                                        cur_list.tail =
                                                            MEM[cur_list.tail as usize].b32.s1
                                                    }
                                                }
                                            }
                                            MEM[cur_list.tail as usize].b32.s1 = new_kern(
                                                FONT_INFO[(KERN_BASE[main_f as usize]
                                                    + 256i32 * main_j.s1 as i32
                                                    + main_j.s0 as i32)
                                                    as usize]
                                                    .b32
                                                    .s1,
                                            );
                                            cur_list.tail = MEM[cur_list.tail as usize].b32.s1;
                                            current_block = 2772858075894446251;
                                        } else {
                                            if cur_l == 65536i32 {
                                                lft_hit = true
                                            } else if lig_stack == TEX_NULL {
                                                rt_hit = true
                                            }
                                            match main_j.s1 as i32 {
                                                1 | 5 => {
                                                    cur_l = main_j.s0 as i32;
                                                    main_i = FONT_INFO[(CHAR_BASE[main_f as usize]
                                                        + effective_char(
                                                            true,
                                                            main_f,
                                                            cur_l as u16,
                                                        ))
                                                        as usize]
                                                        .b16;
                                                    ligature_present = true;
                                                    current_block = 5062343687657450649;
                                                }
                                                2 | 6 => {
                                                    cur_r = main_j.s0 as i32;
                                                    if lig_stack == TEX_NULL {
                                                        lig_stack = new_lig_item(cur_r as u16);
                                                        bchar = 65536i32
                                                    } else if is_char_node(lig_stack) {
                                                        main_p = lig_stack;
                                                        lig_stack = new_lig_item(cur_r as u16);
                                                        MEM[(lig_stack + 1) as usize].b32.s1 =
                                                            main_p
                                                    } else {
                                                        MEM[lig_stack as usize].b16.s0 =
                                                            cur_r as u16
                                                    }
                                                    current_block = 5062343687657450649;
                                                }
                                                3 => {
                                                    cur_r = main_j.s0 as i32;
                                                    main_p = lig_stack;
                                                    lig_stack = new_lig_item(cur_r as u16);
                                                    MEM[lig_stack as usize].b32.s1 = main_p;
                                                    current_block = 5062343687657450649;
                                                }
                                                7 | 11 => {
                                                    if cur_l < 65536i32 {
                                                        if MEM[cur_q as usize].b32.s1 > TEX_NULL {
                                                            if MEM[cur_list.tail as usize].b16.s0
                                                                as i32
                                                                == HYPHEN_CHAR[main_f as usize]
                                                            {
                                                                ins_disc = true
                                                            }
                                                        }
                                                        if ligature_present {
                                                            main_p = new_ligature(
                                                                main_f,
                                                                cur_l as u16,
                                                                MEM[cur_q as usize].b32.s1,
                                                            );
                                                            if lft_hit {
                                                                MEM[main_p as usize].b16.s0 = 2_u16;
                                                                lft_hit = false
                                                            }
                                                            MEM[cur_q as usize].b32.s1 = main_p;
                                                            cur_list.tail = main_p;
                                                            ligature_present = false
                                                        }
                                                        if ins_disc {
                                                            ins_disc = false;
                                                            if cur_list.mode as i32 > 0i32 {
                                                                MEM[cur_list.tail as usize]
                                                                    .b32
                                                                    .s1 = new_disc();
                                                                cur_list.tail = MEM
                                                                    [cur_list.tail as usize]
                                                                    .b32
                                                                    .s1
                                                            }
                                                        }
                                                    }
                                                    cur_q = cur_list.tail;
                                                    cur_l = main_j.s0 as i32;
                                                    main_i = FONT_INFO[(CHAR_BASE[main_f as usize]
                                                        + effective_char(
                                                            true,
                                                            main_f,
                                                            cur_l as u16,
                                                        ))
                                                        as usize]
                                                        .b16;
                                                    ligature_present = true;
                                                    current_block = 5062343687657450649;
                                                }
                                                _ => {
                                                    cur_l = main_j.s0 as i32;
                                                    ligature_present = true;
                                                    if lig_stack == TEX_NULL {
                                                        current_block = 7236688557761431611;
                                                    } else {
                                                        current_block = 4014385708774270501;
                                                    }
                                                }
                                            }
                                            match current_block {
                                                7236688557761431611 => {}
                                                4014385708774270501 => {}
                                                _ => {
                                                    if main_j.s1 as i32 > 4i32 {
                                                        if main_j.s1 as i32 != 7i32 {
                                                            current_block = 7236688557761431611;
                                                        } else {
                                                            current_block = 17785146416239343017;
                                                        }
                                                    } else {
                                                        current_block = 17785146416239343017;
                                                    }
                                                    match current_block {
                                                        7236688557761431611 => {}
                                                        _ => {
                                                            if cur_l < 65536i32 {
                                                                current_block = 4700797278417140031;
                                                            } else {
                                                                main_k =
                                                                    BCHAR_LABEL[main_f as usize];
                                                                current_block =
                                                                    13962460947151495567;
                                                                break;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        current_block = 17910696963991344696;
                                    }
                                } else {
                                    current_block = 17910696963991344696;
                                }
                                match current_block {
                                    2772858075894446251 => {}
                                    7236688557761431611 => {}
                                    4014385708774270501 => {}
                                    4700797278417140031 => {}
                                    _ => {
                                        if main_j.s3 as i32 == 0i32 {
                                            main_k += 1;
                                            current_block = 13962460947151495567;
                                            break;
                                        } else if !(main_j.s3 as i32 >= 128i32) {
                                            main_k = main_k + main_j.s3 as i32 + 1i32;
                                            current_block = 13962460947151495567;
                                            break;
                                        }
                                        current_block = 7236688557761431611;
                                    }
                                }
                            }
                            _ => {
                                /*main_loop_lookahead *//*1073: */
                                get_next();
                                if cur_cmd as i32 == 11i32 {
                                    current_block = 10120566026430170701;
                                } else if cur_cmd as i32 == 12i32 {
                                    current_block = 10120566026430170701;
                                } else if cur_cmd as i32 == 68i32 {
                                    current_block = 10120566026430170701;
                                } else {
                                    x_token();
                                    if cur_cmd as i32 == 11i32 {
                                        current_block = 10120566026430170701;
                                    } else if cur_cmd as i32 == 12i32 {
                                        current_block = 10120566026430170701;
                                    } else if cur_cmd as i32 == 68i32 {
                                        current_block = 10120566026430170701;
                                    } else if cur_cmd as i32 == 16i32 {
                                        scan_char_num();
                                        cur_chr = cur_val;
                                        current_block = 10120566026430170701;
                                    } else {
                                        if cur_cmd as i32 == 65i32 {
                                            bchar = 65536i32
                                        }
                                        cur_r = bchar;
                                        lig_stack = TEX_NULL;
                                        current_block = 4700797278417140031;
                                    }
                                }
                                match current_block {
                                    4700797278417140031 => {}
                                    _ => {
                                        /*main_loop_lookahead 1 */
                                        main_s = (EQTB[(SF_CODE_BASE + cur_chr) as usize].b32.s1
                                            as i64
                                            % 65536)
                                            as i32; /*:1073 */
                                        if main_s == 1000i32 {
                                            cur_list.aux.b32.s0 = 1000i32
                                        } else if main_s < 1000i32 {
                                            if main_s > 0i32 {
                                                cur_list.aux.b32.s0 = main_s
                                            }
                                        } else if cur_list.aux.b32.s0 < 1000i32 {
                                            cur_list.aux.b32.s0 = 1000i32
                                        } else {
                                            cur_list.aux.b32.s0 = main_s
                                        }
                                        cur_ptr = TEX_NULL;
                                        space_class =
                                            (EQTB[(SF_CODE_BASE + cur_chr) as usize].b32.s1 as i64
                                                / 65536)
                                                as i32;
                                        if EQTB[(INT_BASE + 75i32) as usize].b32.s1 > 0i32
                                            && space_class != 4096i32
                                        {
                                            if prev_class == 4096i32 - 1i32 {
                                                if cur_input.state as i32 != 0i32
                                                    || cur_input.index as i32 != 4i32
                                                {
                                                    find_sa_element(
                                                        6i32 as small_number,
                                                        (4096i32 - 1i32) * 4096i32 + space_class,
                                                        false,
                                                    );
                                                    if cur_ptr != TEX_NULL {
                                                        if cur_cmd as i32 != 11i32 {
                                                            cur_cmd = 12i32 as eight_bits
                                                        }
                                                        cur_tok =
                                                            cur_cmd as i32 * 0x200000i32 + cur_chr;
                                                        back_input();
                                                        cur_input.index = 4_u16;
                                                        begin_token_list(
                                                            MEM[(cur_ptr + 1) as usize].b32.s1,
                                                            17_u16,
                                                        );
                                                        continue 'c_125208;
                                                    }
                                                }
                                            } else {
                                                find_sa_element(
                                                    6i32 as small_number,
                                                    prev_class * 4096i32 + space_class,
                                                    false,
                                                );
                                                if cur_ptr != TEX_NULL {
                                                    if cur_cmd as i32 != 11i32 {
                                                        cur_cmd = 12i32 as eight_bits
                                                    }
                                                    cur_tok =
                                                        cur_cmd as i32 * 0x200000i32 + cur_chr;
                                                    back_input();
                                                    cur_input.index = 4_u16;
                                                    begin_token_list(
                                                        MEM[(cur_ptr + 1) as usize].b32.s1,
                                                        17_u16,
                                                    );
                                                    prev_class = 4096i32 - 1i32;
                                                    continue 'c_125208;
                                                }
                                            }
                                            prev_class = space_class
                                        }
                                        lig_stack = avail;
                                        if lig_stack == TEX_NULL {
                                            lig_stack = get_avail()
                                        } else {
                                            avail = MEM[lig_stack as usize].b32.s1;
                                            MEM[lig_stack as usize].b32.s1 = TEX_NULL
                                        }
                                        MEM[lig_stack as usize].b16.s1 = main_f as u16;
                                        cur_r = cur_chr;
                                        MEM[lig_stack as usize].b16.s0 = cur_r as u16;
                                        if cur_r == false_bchar {
                                            cur_r = 65536i32
                                        }
                                        current_block = 4700797278417140031;
                                    }
                                }
                            }
                        }
                        loop {
                            match current_block {
                                7236688557761431611 => {
                                    /*main_loop_wrapup *//*1070: */
                                    if cur_l < 65536i32 {
                                        if MEM[cur_q as usize].b32.s1 > TEX_NULL {
                                            if MEM[cur_list.tail as usize].b16.s0 as i32
                                                == HYPHEN_CHAR[main_f as usize]
                                            {
                                                ins_disc = true
                                            }
                                        }
                                        if ligature_present {
                                            main_p = new_ligature(
                                                main_f,
                                                cur_l as u16,
                                                MEM[cur_q as usize].b32.s1,
                                            );
                                            if lft_hit {
                                                MEM[main_p as usize].b16.s0 = 2_u16;
                                                lft_hit = false
                                            }
                                            if rt_hit {
                                                if lig_stack == TEX_NULL {
                                                    MEM[main_p as usize].b16.s0 += 1;
                                                    rt_hit = false
                                                }
                                            }
                                            MEM[cur_q as usize].b32.s1 = main_p;
                                            cur_list.tail = main_p;
                                            ligature_present = false
                                        }
                                        if ins_disc {
                                            ins_disc = false;
                                            if cur_list.mode as i32 > 0i32 {
                                                MEM[cur_list.tail as usize].b32.s1 = new_disc();
                                                cur_list.tail = MEM[cur_list.tail as usize].b32.s1
                                            }
                                        }
                                    }
                                    current_block = 2772858075894446251;
                                }
                                4700797278417140031 =>
                                /*main_lig_loop *//*1074: */
                                {
                                    if main_i.s1 as i32 % 4i32 != 1i32 {
                                        current_block = 7236688557761431611;
                                        continue;
                                    }
                                    if cur_r == 65536i32 {
                                        current_block = 7236688557761431611;
                                    } else {
                                        break;
                                    }
                                }
                                2772858075894446251 =>
                                /*main_loop_move *//*1071: */
                                {
                                    if lig_stack == TEX_NULL {
                                        break 'c_125239;
                                    }
                                    cur_q = cur_list.tail;
                                    cur_l = MEM[lig_stack as usize].b16.s0 as i32;
                                    current_block = 4014385708774270501;
                                }
                                _ =>
                                /*main_loop_move 1 */
                                {
                                    if is_char_node(lig_stack) {
                                        current_block = 249799543778823886;
                                        break 'c_125244;
                                    }
                                    /*main_loop_move_lig *//*1072: */
                                    main_p = MEM[(lig_stack + 1) as usize].b32.s1;
                                    if main_p > TEX_NULL {
                                        MEM[cur_list.tail as usize].b32.s1 = main_p;
                                        cur_list.tail = MEM[cur_list.tail as usize].b32.s1
                                    }
                                    temp_ptr = lig_stack;
                                    lig_stack = MEM[temp_ptr as usize].b32.s1;
                                    free_node(temp_ptr, 2i32);
                                    main_i = FONT_INFO[(CHAR_BASE[main_f as usize]
                                        + effective_char(1i32 != 0, main_f, cur_l as u16))
                                        as usize]
                                        .b16;
                                    ligature_present = true;
                                    if lig_stack == TEX_NULL {
                                        if main_p > TEX_NULL {
                                            current_block = 18270385712206273994;
                                            continue 'c_125244;
                                        }
                                        cur_r = bchar;
                                        current_block = 4700797278417140031;
                                    } else {
                                        cur_r = MEM[lig_stack as usize].b16.s0 as i32;
                                        current_block = 4700797278417140031;
                                    }
                                }
                            }
                        }
                        main_k = LIG_KERN_BASE[main_f as usize] + main_i.s0 as i32;
                        main_j = FONT_INFO[main_k as usize].b16;
                        if main_j.s3 as i32 <= 128i32 {
                            current_block = 11331079115679122507;
                            continue;
                        }
                        main_k = ((LIG_KERN_BASE[main_f as usize]
                            + 256i32 * main_j.s1 as i32
                            + main_j.s0 as i32) as i64
                            + 32768
                            - (256i32 * 128i32) as i64)
                            as font_index;
                        current_block = 13962460947151495567;
                        break;
                    }
                }
            }
        }
        match current_block {
            11459959175219260272 => app_space(),
            _ =>
            /*append_normal_space */
            {
                if EQTB[(INT_BASE + 75i32) as usize].b32.s1 > 0i32
                    && space_class != 4096i32
                    && prev_class != 4096i32 - 1i32
                {
                    prev_class = 4096i32 - 1i32;
                    find_sa_element(
                        6i32 as small_number,
                        space_class * 4096i32 + (4096i32 - 1i32),
                        false,
                    );
                    if cur_ptr != TEX_NULL {
                        if cur_cs == 0i32 {
                            if cur_cmd as i32 == 16i32 {
                                cur_cmd = 12i32 as eight_bits
                            }
                            cur_tok = cur_cmd as i32 * 0x200000i32 + cur_chr
                        } else {
                            cur_tok = 0x1ffffffi32 + cur_cs
                        }
                        back_input();
                        begin_token_list(MEM[(cur_ptr + 1) as usize].b32.s1, 17_u16);
                        continue;
                    }
                }
                if EQTB[(GLUE_BASE + 12i32) as usize].b32.s1 == 0i32 {
                    main_p = FONT_GLUE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize];
                    if main_p == TEX_NULL {
                        main_p = new_spec(0i32);
                        main_k = PARAM_BASE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] + 2;
                        MEM[(main_p + 1) as usize].b32.s1 = FONT_INFO[main_k as usize].b32.s1;
                        MEM[(main_p + 2) as usize].b32.s1 = FONT_INFO[(main_k + 1) as usize].b32.s1;
                        MEM[(main_p + 3) as usize].b32.s1 = FONT_INFO[(main_k + 2) as usize].b32.s1;
                        FONT_GLUE[EQTB[(CUR_FONT_LOC) as usize].b32.s1 as usize] = main_p
                    }
                    temp_ptr = new_glue(main_p)
                } else {
                    temp_ptr = new_param_glue(12i32 as small_number)
                }
                MEM[cur_list.tail as usize].b32.s1 = temp_ptr;
                cur_list.tail = temp_ptr
            }
        }
    }
}
pub(crate) unsafe fn give_err_help() {
    token_show(EQTB[(LOCAL_BASE + 9i32) as usize].b32.s1);
}
pub(crate) unsafe fn close_files_and_terminate() {
    let mut k: i32 = 0;
    terminate_font_manager();
    k = 0i32;
    while k <= 15i32 {
        if write_open[k as usize] {
            ttstub_output_close(write_file[k as usize].take().unwrap());
        }
        k += 1
    }
    finalize_dvi_file();
    synctex_terminate(log_opened);
    if log_opened {
        ttstub_output_putc(log_file.as_mut().unwrap(), '\n' as i32);
        ttstub_output_close(log_file.take().unwrap());
        log_file = None;
        selector = u8::from(selector).wrapping_sub(2).into();
        if selector == Selector::TERM_ONLY {
            print_nl_cstr(b"Transcript written on ");
            print(texmf_log_name);
            print_char('.' as i32);
        }
    }
    print_ln();
}
pub(crate) unsafe fn flush_str(mut s: str_number) {
    if s == str_ptr - 1i32 {
        str_ptr -= 1;
        pool_ptr = *str_start.offset((str_ptr - 65536i32) as isize)
    };
}
pub(crate) unsafe fn tokens_to_string(mut p: i32) -> str_number {
    if selector == Selector::NEW_STRING {
        pdf_error(
            b"tokens",
            b"tokens_to_string() called while selector = new_string",
        );
    }
    old_setting = selector;
    selector = Selector::NEW_STRING;
    show_token_list(MEM[p as usize].b32.s1, TEX_NULL, pool_size - pool_ptr);
    selector = old_setting;
    make_string()
}
pub(crate) unsafe fn scan_pdf_ext_toks() {
    scan_toks(false, true);
}
pub(crate) unsafe fn compare_strings() {
    let mut current_block: u64;
    let mut s1: str_number = 0;
    let mut s2: str_number = 0;
    let mut i1: pool_pointer = 0;
    let mut i2: pool_pointer = 0;
    let mut j1: pool_pointer = 0;
    let mut j2: pool_pointer = 0;
    scan_toks(false, true);
    s1 = tokens_to_string(def_ref);
    delete_token_ref(def_ref);
    scan_toks(false, true);
    s2 = tokens_to_string(def_ref);
    delete_token_ref(def_ref);
    i1 = *str_start.offset((s1 as i64 - 65536) as isize);
    j1 = *str_start.offset(((s1 + 1i32) as i64 - 65536) as isize);
    i2 = *str_start.offset((s2 as i64 - 65536) as isize);
    j2 = *str_start.offset(((s2 + 1i32) as i64 - 65536) as isize);
    loop {
        if !(i1 < j1 && i2 < j2) {
            current_block = 12124785117276362961;
            break;
        }
        if (*str_pool.offset(i1 as isize) as i32) < *str_pool.offset(i2 as isize) as i32 {
            cur_val = -1i32;
            current_block = 11833780966967478830;
            break;
        } else if *str_pool.offset(i1 as isize) as i32 > *str_pool.offset(i2 as isize) as i32 {
            cur_val = 1i32;
            current_block = 11833780966967478830;
            break;
        } else {
            i1 += 1;
            i2 += 1
        }
    }
    match current_block {
        12124785117276362961 => {
            if i1 == j1 && i2 == j2 {
                cur_val = 0i32
            } else if i1 < j1 {
                cur_val = 1i32
            } else {
                cur_val = -1i32
            }
        }
        _ => {}
    }
    flush_str(s2);
    flush_str(s1);
    cur_val_level = 0_u8;
}
pub(crate) unsafe fn prune_page_top(mut p: i32, mut s: bool) -> i32 {
    let mut prev_p: i32 = 0;
    let mut q: i32 = 0;
    let mut r: i32 = TEX_NULL;
    prev_p = 4999999i32 - 3i32;
    MEM[(4999999 - 3) as usize].b32.s1 = p;
    while p != TEX_NULL {
        match MEM[p as usize].b16.s1 as i32 {
            0 | 1 | 2 => {
                q = new_skip_param(10i32 as small_number);
                MEM[prev_p as usize].b32.s1 = q;
                MEM[q as usize].b32.s1 = p;
                if MEM[(temp_ptr + 1) as usize].b32.s1 > MEM[(p + 3) as usize].b32.s1 {
                    MEM[(temp_ptr + 1) as usize].b32.s1 =
                        MEM[(temp_ptr + 1) as usize].b32.s1 - MEM[(p + 3) as usize].b32.s1
                } else {
                    MEM[(temp_ptr + 1) as usize].b32.s1 = 0
                }
                p = TEX_NULL
            }
            8 | 4 | 3 => {
                prev_p = p;
                p = MEM[prev_p as usize].b32.s1
            }
            10 | 11 | 12 => {
                q = p;
                p = MEM[q as usize].b32.s1;
                MEM[q as usize].b32.s1 = TEX_NULL;
                MEM[prev_p as usize].b32.s1 = p;
                if s {
                    if disc_ptr[3] == TEX_NULL {
                        disc_ptr[3] = q
                    } else {
                        MEM[r as usize].b32.s1 = q
                    }
                    r = q
                } else {
                    flush_node_list(q);
                }
            }
            _ => confusion(b"pruning"),
        }
    }
    MEM[(4999999 - 3) as usize].b32.s1
}
pub(crate) unsafe fn do_marks(mut a: small_number, mut l: small_number, mut q: i32) -> bool {
    let mut i: small_number = 0;
    if (l as i32) < 4i32 {
        i = 0i32 as small_number;
        while i as i32 <= 15i32 {
            if i as i32 & 1i32 != 0 {
                cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s1
            } else {
                cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s0
            }
            if cur_ptr != TEX_NULL {
                if do_marks(a, (l as i32 + 1i32) as small_number, cur_ptr) {
                    if i as i32 & 1i32 != 0 {
                        MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = TEX_NULL
                    } else {
                        MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = TEX_NULL
                    }
                    MEM[q as usize].b16.s0 -= 1;
                }
            }
            i += 1
        }
        if MEM[q as usize].b16.s0 as i32 == 0 {
            free_node(q, 33i32);
            q = TEX_NULL
        }
    } else {
        match a as i32 {
            0 => {
                /*1614: */
                if MEM[(q + 2) as usize].b32.s1 != TEX_NULL {
                    delete_token_ref(MEM[(q + 2) as usize].b32.s1);
                    MEM[(q + 2) as usize].b32.s1 = TEX_NULL;
                    delete_token_ref(MEM[(q + 3) as usize].b32.s0);
                    MEM[(q + 3) as usize].b32.s0 = TEX_NULL
                }
            }
            1 => {
                if MEM[(q + 2) as usize].b32.s0 != TEX_NULL {
                    if MEM[(q + 1) as usize].b32.s0 != TEX_NULL {
                        delete_token_ref(MEM[(q + 1) as usize].b32.s0);
                    }
                    delete_token_ref(MEM[(q + 1) as usize].b32.s1);
                    MEM[(q + 1) as usize].b32.s1 = TEX_NULL;
                    if MEM[MEM[(q + 2) as usize].b32.s0 as usize].b32.s1 == TEX_NULL {
                        delete_token_ref(MEM[(q + 2) as usize].b32.s0);
                        MEM[(q + 2) as usize].b32.s0 = TEX_NULL
                    } else {
                        MEM[MEM[(q + 2) as usize].b32.s0 as usize].b32.s0 += 1;
                    }
                    MEM[(q + 1) as usize].b32.s0 = MEM[(q + 2) as usize].b32.s0
                }
            }
            2 => {
                if MEM[(q + 1) as usize].b32.s0 != TEX_NULL
                    && MEM[(q + 1) as usize].b32.s1 == TEX_NULL
                {
                    MEM[(q + 1) as usize].b32.s1 = MEM[(q + 1) as usize].b32.s0;
                    MEM[MEM[(q + 1) as usize].b32.s0 as usize].b32.s0 += 1;
                }
            }
            3 => {
                i = 0i32 as small_number;
                while i as i32 <= 4i32 {
                    if i as i32 & 1i32 != 0 {
                        cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s1
                    } else {
                        cur_ptr = MEM[(q + i as i32 / 2 + 1) as usize].b32.s0
                    }
                    if cur_ptr != TEX_NULL {
                        delete_token_ref(cur_ptr);
                        if i as i32 & 1i32 != 0 {
                            MEM[(q + i as i32 / 2 + 1) as usize].b32.s1 = TEX_NULL
                        } else {
                            MEM[(q + i as i32 / 2 + 1) as usize].b32.s0 = TEX_NULL
                        }
                    }
                    i += 1
                }
            }
            _ => {}
        }
        if MEM[(q + 2) as usize].b32.s0 == TEX_NULL {
            if MEM[(q + 3) as usize].b32.s0 == TEX_NULL {
                free_node(q, 4i32);
                q = TEX_NULL
            }
        }
    }
    q == TEX_NULL
}
pub(crate) unsafe fn do_assignments() {
    loop {
        loop {
            get_x_token();
            if !(cur_cmd as i32 == 10i32 || cur_cmd as i32 == 0i32) {
                break;
            }
        }
        if cur_cmd as i32 <= 71i32 {
            return;
        }
        set_box_allowed = false;
        prefixed_command();
        set_box_allowed = true
    }
}
/* the former xetexcoerce.h: */
pub(crate) unsafe fn new_whatsit(mut s: small_number, mut w: small_number) {
    let mut p: i32 = 0;
    p = get_node(w as i32);
    MEM[p as usize].b16.s1 = 8_u16;
    MEM[p as usize].b16.s0 = s as u16;
    MEM[cur_list.tail as usize].b32.s1 = p;
    cur_list.tail = p;
}
