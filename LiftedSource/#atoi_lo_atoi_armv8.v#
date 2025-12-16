(* Automatically generated with pcode2coq
arch: armv8
file: atoi.lo
function: atoi
*)

(* EDIT (11/17/2025): Changed `Picinae_armv8 to `Picinae_armv8_pcode` *)
Require Import Picinae_armv8_pcode.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition atoi_lo_atoi_armv8 : program := fun _ a => match a with

(* 0x00100000: mov x1,x0 *)
(*    1048576: mov x1,x0 *)
| 0x100000 => Some (4,
	(* (register, 0x4008, 8) COPY (register, 0x4000, 8) *)
	Move R_X1 (Var R_X0)
)

(* 0x00100004: ldrb w0,[x1] *)
(*    1048580: ldrb w0,[x1] *)
| 0x100004 => Some (4,
	(* (unique, 0x6680, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x6680) (Var R_X1) $;
	(* (unique, 0x25500, 1) LOAD (const, 0x1b1, 8) , (unique, 0x6680, 8) *)
	Move (V_TEMP 0x25500) (Load (Var V_MEM64) (Var (V_TEMP 0x6680)) LittleE 1) $;
	(* (register, 0x4000, 8) INT_ZEXT (unique, 0x25500, 1) *)
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25500)))
)

(* 0x00100008: sub w2,w0,#0x9 *)
(*    1048584: sub w2,w0,#0x9 *)
| 0x100008 => Some (4,
	(* (unique, 0x3d080, 4) INT_SUB (register, 0x4000, 4) , (const, 0x9, 4) *)
	Move (V_TEMP 0x3d080) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x9 32)) $;
	(* (register, 0x4010, 8) INT_ZEXT (unique, 0x3d080, 4) *)
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3d080)))
)

(* 0x0010000c: cmp w0,#0x20 *)
(*    1048588: cmp w0,#0x20 *)
| 0x10000c => Some (4,
	(* (unique, 0x1c980, 4) COPY (const, 0x20, 4) *)
	Move (V_TEMP 0x1c980) (Word 0x20 32) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (const, 0x20, 4) , (register, 0x4000, 4) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x20 32) (Extract 31 0 (Var R_X0)))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4000, 4) , (const, 0x20, 4) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x20 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (unique, 0x1ca80, 4) INT_SUB (register, 0x4000, 4) , (unique, 0x1c980, 4) *)
	Move (V_TEMP 0x1ca80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c980))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100010: ccmp w2,#0x4,#0x0,ne *)
(*    1048592: ccmp w2,#0x4,#0x0,ne *)
| 0x100010 => Some (4,
	(* (unique, 0x1680, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0x1680) (UnOp OP_NOT (Var R_ZR)) $;
	(* (unique, 0x19c80, 1) COPY (unique, 0x1680, 1) *)
	Move (V_TEMP 0x19c80) (Var (V_TEMP 0x1680)) $;
	(* (unique, 0x19d00, 1) COPY (const, 0x0, 1) *)
	Move (V_TEMP 0x19d00) (Word 0x0 8) $;
	(* (unique, 0xe780, 1) INT_AND (unique, 0x19d00, 1) , (const, 0x8, 1) *)
	Move (V_TEMP 0xe780) (BinOp OP_AND (Var (V_TEMP 0x19d00)) (Word 0x8 8)) $;
	(* (register, 0x100, 1) INT_EQUAL (unique, 0xe780, 1) , (const, 0x8, 1) *)
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe780)) (Word 0x8 8))) $;
	(* (unique, 0xe880, 1) INT_AND (unique, 0x19d00, 1) , (const, 0x4, 1) *)
	Move (V_TEMP 0xe880) (BinOp OP_AND (Var (V_TEMP 0x19d00)) (Word 0x4 8)) $;
	(* (register, 0x101, 1) INT_EQUAL (unique, 0xe880, 1) , (const, 0x4, 1) *)
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe880)) (Word 0x4 8))) $;
	(* (unique, 0xe980, 1) INT_AND (unique, 0x19d00, 1) , (const, 0x2, 1) *)
	Move (V_TEMP 0xe980) (BinOp OP_AND (Var (V_TEMP 0x19d00)) (Word 0x2 8)) $;
	(* (register, 0x102, 1) INT_EQUAL (unique, 0xe980, 1) , (const, 0x2, 1) *)
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe980)) (Word 0x2 8))) $;
	(* (unique, 0xea80, 1) INT_AND (unique, 0x19d00, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0xea80) (BinOp OP_AND (Var (V_TEMP 0x19d00)) (Word 0x1 8)) $;
	(* (register, 0x103, 1) INT_EQUAL (unique, 0xea80, 1) , (const, 0x1, 1) *)
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xea80)) (Word 0x1 8))) $;
	(* (unique, 0x19d80, 1) BOOL_NEGATE (unique, 0x19c80, 1) *)
	Move (V_TEMP 0x19d80) (UnOp OP_NOT (Var (V_TEMP 0x19c80))) $;
	(*  ---  CBRANCH (ram, 0x100014, 8) , (unique, 0x19d80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19d80))) (
		Jmp (Word 0x100014 64)
	) (* else *) (
		Nop
	) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (const, 0x4, 4) , (register, 0x4010, 4) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x4 32) (Extract 31 0 (Var R_X2)))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 4) , (const, 0x4, 4) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x4 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (unique, 0x19e80, 4) INT_SUB (register, 0x4010, 4) , (const, 0x4, 4) *)
	Move (V_TEMP 0x19e80) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x4 32)) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x19e80, 4) , (const, 0x0, 4) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19e80)) (Word 0x0 32))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x19e80, 4) , (const, 0x0, 4) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19e80)) (Word 0x0 32))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100014: b.ls 0x0010003c *)
(*    1048596: b.ls 0x0010003c *)
| 0x100014 => Some (4,
	(* (unique, 0xf00, 1) BOOL_NEGATE (register, 0x102, 1) *)
	Move (V_TEMP 0xf00) (UnOp OP_NOT (Var R_CY)) $;
	(* (unique, 0x1000, 1) BOOL_OR (unique, 0xf00, 1) , (register, 0x101, 1) *)
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	(*  ---  CBRANCH (ram, 0x10003c, 8) , (unique, 0x1000, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x10003c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100018: cmp w0,#0x2b *)
(*    1048600: cmp w0,#0x2b *)
| 0x100018 => Some (4,
	(* (unique, 0x1c980, 4) COPY (const, 0x2b, 4) *)
	Move (V_TEMP 0x1c980) (Word 0x2b 32) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (const, 0x2b, 4) , (register, 0x4000, 4) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x2b 32) (Extract 31 0 (Var R_X0)))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4000, 4) , (const, 0x2b, 4) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x2b 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x2b 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2b 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (unique, 0x1ca80, 4) INT_SUB (register, 0x4000, 4) , (unique, 0x1c980, 4) *)
	Move (V_TEMP 0x1ca80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c980))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x0010001c: b.eq 0x00100044 *)
(*    1048604: b.eq 0x00100044 *)
| 0x10001c => Some (4,
	(*  ---  CBRANCH (ram, 0x100044, 8) , (register, 0x101, 1) *)
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x100044 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100020: cmp w0,#0x2d *)
(*    1048608: cmp w0,#0x2d *)
| 0x100020 => Some (4,
	(* (unique, 0x1c980, 4) COPY (const, 0x2d, 4) *)
	Move (V_TEMP 0x1c980) (Word 0x2d 32) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (const, 0x2d, 4) , (register, 0x4000, 4) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x2d 32) (Extract 31 0 (Var R_X0)))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4000, 4) , (const, 0x2d, 4) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x2d 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x2d 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2d 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (unique, 0x1ca80, 4) INT_SUB (register, 0x4000, 4) , (unique, 0x1c980, 4) *)
	Move (V_TEMP 0x1ca80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c980))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100024: b.ne 0x00100074 *)
(*    1048612: b.ne 0x00100074 *)
| 0x100024 => Some (4,
	(* (unique, 0xa00, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	(*  ---  CBRANCH (ram, 0x100074, 8) , (unique, 0xa00, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x100074 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100028: mov w3,#0x1 *)
(*    1048616: mov w3,#0x1 *)
| 0x100028 => Some (4,
	(* (register, 0x4018, 8) COPY (const, 0x1, 8) *)
	Move R_X3 (Word 0x1 64)
)

(* 0x0010002c: add x1,x1,#0x1 *)
(*    1048620: add x1,x1,#0x1 *)
| 0x10002c => Some (4,
	(* (unique, 0x11e80, 8) COPY (const, 0x1, 8) *)
	Move (V_TEMP 0x11e80) (Word 0x1 64) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) (Var R_X1))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11e80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x11f80, 8) INT_ADD (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move (V_TEMP 0x11f80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x11f80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11f80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x11f80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11f80)) (Word 0x0 64))) $;
	(* (register, 0x4008, 8) COPY (unique, 0x11f80, 8) *)
	Move R_X1 (Var (V_TEMP 0x11f80))
)

(* 0x00100030: mov w0,#0x0 *)
(*    1048624: mov w0,#0x0 *)
| 0x100030 => Some (4,
	(* (register, 0x4000, 8) COPY (const, 0x0, 8) *)
	Move R_X0 (Word 0x0 64)
)

(* 0x00100034: mov w4,#0xa *)
(*    1048628: mov w4,#0xa *)
| 0x100034 => Some (4,
	(* (register, 0x4020, 8) COPY (const, 0xa, 8) *)
	Move R_X4 (Word 0xa 64)
)

(* 0x00100038: b 0x00100058 *)
(*    1048632: b 0x00100058 *)
| 0x100038 => Some (4,
	(*  ---  BRANCH (ram, 0x100058, 8) *)
	Jmp (Word 0x100058 64)
)

(* 0x0010003c: add x1,x1,#0x1 *)
(*    1048636: add x1,x1,#0x1 *)
| 0x10003c => Some (4,
	(* (unique, 0x11e80, 8) COPY (const, 0x1, 8) *)
	Move (V_TEMP 0x11e80) (Word 0x1 64) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) (Var R_X1))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11e80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x11f80, 8) INT_ADD (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move (V_TEMP 0x11f80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x11f80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11f80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x11f80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11f80)) (Word 0x0 64))) $;
	(* (register, 0x4008, 8) COPY (unique, 0x11f80, 8) *)
	Move R_X1 (Var (V_TEMP 0x11f80))
)

(* 0x00100040: b 0x00100004 *)
(*    1048640: b 0x00100004 *)
| 0x100040 => Some (4,
	(*  ---  BRANCH (ram, 0x100004, 8) *)
	Jmp (Word 0x100004 64)
)

(* 0x00100044: mov w3,#0x0 *)
(*    1048644: mov w3,#0x0 *)
| 0x100044 => Some (4,
	(* (register, 0x4018, 8) COPY (const, 0x0, 8) *)
	Move R_X3 (Word 0x0 64)
)

(* 0x00100048: b 0x0010002c *)
(*    1048648: b 0x0010002c *)
| 0x100048 => Some (4,
	(*  ---  BRANCH (ram, 0x10002c, 8) *)
	Jmp (Word 0x10002c 64)
)

(* 0x0010004c: mul w0,w0,w4 *)
(*    1048652: mul w0,w0,w4 *)
| 0x10004c => Some (4,
	(* (unique, 0x2b380, 4) INT_MULT (register, 0x4000, 4) , (register, 0x4020, 4) *)
	Move (V_TEMP 0x2b380) (BinOp OP_TIMES (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X4))) $;
	(* (register, 0x4000, 8) INT_ZEXT (unique, 0x2b380, 4) *)
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2b380)))
)

(* 0x00100050: add x1,x1,#0x1 *)
(*    1048656: add x1,x1,#0x1 *)
| 0x100050 => Some (4,
	(* (unique, 0x11e80, 8) COPY (const, 0x1, 8) *)
	Move (V_TEMP 0x11e80) (Word 0x1 64) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) (Var R_X1))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11e80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x11f80, 8) INT_ADD (register, 0x4008, 8) , (unique, 0x11e80, 8) *)
	Move (V_TEMP 0x11f80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11e80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x11f80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11f80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x11f80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11f80)) (Word 0x0 64))) $;
	(* (register, 0x4008, 8) COPY (unique, 0x11f80, 8) *)
	Move R_X1 (Var (V_TEMP 0x11f80))
)

(* 0x00100054: sub w0,w0,w2 *)
(*    1048660: sub w0,w0,w2 *)
| 0x100054 => Some (4,
	(* (unique, 0x3d780, 4) INT_SUB (register, 0x4000, 4) , (register, 0x4010, 4) *)
	Move (V_TEMP 0x3d780) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X2))) $;
	(* (register, 0x4000, 8) INT_ZEXT (unique, 0x3d780, 4) *)
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3d780)))
)

(* 0x00100058: ldrb w2,[x1] *)
(*    1048664: ldrb w2,[x1] *)
| 0x100058 => Some (4,
	(* (unique, 0x6680, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x6680) (Var R_X1) $;
	(* (unique, 0x25500, 1) LOAD (const, 0x1b1, 8) , (unique, 0x6680, 8) *)
	Move (V_TEMP 0x25500) (Load (Var V_MEM64) (Var (V_TEMP 0x6680)) LittleE 1) $;
	(* (register, 0x4010, 8) INT_ZEXT (unique, 0x25500, 1) *)
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25500)))
)

(* 0x0010005c: sub w2,w2,#0x30 *)
(*    1048668: sub w2,w2,#0x30 *)
| 0x10005c => Some (4,
	(* (unique, 0x3d080, 4) INT_SUB (register, 0x4010, 4) , (const, 0x30, 4) *)
	Move (V_TEMP 0x3d080) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x30 32)) $;
	(* (register, 0x4010, 8) INT_ZEXT (unique, 0x3d080, 4) *)
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3d080)))
)

(* 0x00100060: cmp w2,#0x9 *)
(*    1048672: cmp w2,#0x9 *)
| 0x100060 => Some (4,
	(* (unique, 0x1c980, 4) COPY (const, 0x9, 4) *)
	Move (V_TEMP 0x1c980) (Word 0x9 32) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (const, 0x9, 4) , (register, 0x4010, 4) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x9 32) (Extract 31 0 (Var R_X2)))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 4) , (const, 0x9, 4) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x9 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (unique, 0x1ca80, 4) INT_SUB (register, 0x4010, 4) , (unique, 0x1c980, 4) *)
	Move (V_TEMP 0x1ca80) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x1c980))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100064: b.ls 0x0010004c *)
(*    1048676: b.ls 0x0010004c *)
| 0x100064 => Some (4,
	(* (unique, 0xf00, 1) BOOL_NEGATE (register, 0x102, 1) *)
	Move (V_TEMP 0xf00) (UnOp OP_NOT (Var R_CY)) $;
	(* (unique, 0x1000, 1) BOOL_OR (unique, 0xf00, 1) , (register, 0x101, 1) *)
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	(*  ---  CBRANCH (ram, 0x10004c, 8) , (unique, 0x1000, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x10004c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100068: cbnz w3,0x00100070 *)
(*    1048680: cbnz w3,0x00100070 *)
| 0x100068 => Some (4,
	(* (unique, 0x18e00, 1) INT_NOTEQUAL (register, 0x4018, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x18e00) (BinOp OP_NEQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	(*  ---  CBRANCH (ram, 0x100070, 8) , (unique, 0x18e00, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18e00))) (
		Jmp (Word 0x100070 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010006c: neg w0,w0 *)
(*    1048684: neg w0,w0 *)
| 0x10006c => Some (4,
	(* (unique, 0x2b900, 4) INT_2COMP (register, 0x4000, 4) *)
	Move (V_TEMP 0x2b900) (UnOp OP_NEG (Extract 31 0 (Var R_X0))) $;
	(* (register, 0x4000, 8) INT_ZEXT (unique, 0x2b900, 4) *)
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2b900)))
)

(* 0x00100070: ret *)
(*    1048688: ret *)
| 0x100070 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100074: mov w3,#0x0 *)
(*    1048692: mov w3,#0x0 *)
| 0x100074 => Some (4,
	(* (register, 0x4018, 8) COPY (const, 0x0, 8) *)
	Move R_X3 (Word 0x0 64)
)

(* 0x00100078: b 0x00100030 *)
(*    1048696: b 0x00100030 *)
| 0x100078 => Some (4,
	(*  ---  BRANCH (ram, 0x100030, 8) *)
	Jmp (Word 0x100030 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx atoi_lo_atoi_armv8.
Proof. Picinae_typecheck. Qed.
