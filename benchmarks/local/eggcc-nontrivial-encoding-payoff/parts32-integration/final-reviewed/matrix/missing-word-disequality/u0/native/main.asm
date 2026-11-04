000000010000586c <_main>:
10000586c:     	stp	d11, d10, [sp, #-0x50]!
100005870:     	stp	d9, d8, [sp, #0x10]
100005874:     	stp	x22, x21, [sp, #0x20]
100005878:     	stp	x20, x19, [sp, #0x30]
10000587c:     	stp	x29, x30, [sp, #0x40]
100005880:     	mov	x21, x1
100005884:     	ldr	x0, [x1, #0x8]
100005888:     	bl	0x1000009a4 <__bril_parse_int>
10000588c:     	mov	x19, x0
100005890:     	ldr	x0, [x21, #0x10]
100005894:     	bl	0x1000009a4 <__bril_parse_int>
100005898:     	mov	x20, x0
10000589c:     	ldr	x0, [x21, #0x18]
1000058a0:     	bl	0x1000009a4 <__bril_parse_int>
1000058a4:     	mov	w8, #0x4240             ; =16960
1000058a8:     	movk	w8, #0xf, lsl #16
1000058ac:     	cmp	x0, x8
1000058b0:     	b.hi	0x1000058dc <_main+0x70>
1000058b4:     	cbz	x0, 0x1000058e4 <_main+0x78>
1000058b8:     	mov	x9, #0x1                ; =1
1000058bc:     	movk	x9, #0x2, lsl #32
1000058c0:     	cmp	x0, #0x8
1000058c4:     	b.hs	0x1000058ec <_main+0x80>
1000058c8:     	mov	x12, #0x0               ; =0
1000058cc:     	mov	x8, #0x0                ; =0
1000058d0:     	mov	x10, x19
1000058d4:     	mov	x11, x20
1000058d8:     	b	0x100005a50 <_main+0x1e4>
1000058dc:     	mov	x8, #-0x2               ; =-2
1000058e0:     	b	0x100005a90 <_main+0x224>
1000058e4:     	mov	x8, #0x0                ; =0
1000058e8:     	b	0x100005a90 <_main+0x224>
1000058ec:     	and	x12, x0, #0xffff8
1000058f0:     	lsr	x8, x12, #3
1000058f4:     	mov	x10, x12
1000058f8:     	bfi	x10, x8, #35, #17
1000058fc:     	add	x10, x19, x10
100005900:     	madd	x11, x12, x9, x20
100005904:     	dup.2d	v0, x19
100005908:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
10000590c:     	ldr	q1, [x8, #0xb70]
100005910:     	add.2d	v0, v0, v1
100005914:     	dup.2d	v1, x20
100005918:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
10000591c:     	ldr	q2, [x8, #0xb80]
100005920:     	add.2d	v2, v1, v2
100005924:     	movi.2d	v1, #0000000000000000
100005928:     	movi.4s	v3, #0x2
10000592c:     	movi.4s	v4, #0x4
100005930:     	movi.4s	v5, #0x6
100005934:     	mov	x8, #0x2                ; =2
100005938:     	movk	x8, #0x4, lsl #32
10000593c:     	dup.2d	v6, x8
100005940:     	mov	x8, #0x4                ; =4
100005944:     	movk	x8, #0x8, lsl #32
100005948:     	dup.2d	v7, x8
10000594c:     	mov	x8, #0x6                ; =6
100005950:     	movk	x8, #0xc, lsl #32
100005954:     	dup.2d	v16, x8
100005958:     	mov	x8, #0x100000000        ; =4294967296
10000595c:     	dup.2d	v17, x8
100005960:     	mov	w8, #0x7                ; =7
100005964:     	dup.2d	v18, x8
100005968:     	mov	w8, #0x63               ; =99
10000596c:     	dup.2d	v19, x8
100005970:     	movi.2d	v20, #0x000000ffffffff
100005974:     	mov	w8, #0x3                ; =3
100005978:     	dup.2d	v21, x8
10000597c:     	movi.4s	v22, #0x8
100005980:     	mov	x8, #0x8                ; =8
100005984:     	movk	x8, #0x10, lsl #32
100005988:     	dup.2d	v23, x8
10000598c:     	mov	x8, x12
100005990:     	movi.2d	v24, #0000000000000000
100005994:     	movi.2d	v25, #0000000000000000
100005998:     	movi.2d	v26, #0000000000000000
10000599c:     	add.2d	v27, v0, v3
1000059a0:     	add.2d	v28, v0, v4
1000059a4:     	add.2d	v29, v0, v5
1000059a8:     	add.2d	v30, v2, v6
1000059ac:     	add.2d	v31, v2, v7
1000059b0:     	add.2d	v8, v2, v16
1000059b4:     	eor.16b	v9, v2, v0
1000059b8:     	eor.16b	v27, v30, v27
1000059bc:     	eor.16b	v28, v31, v28
1000059c0:     	eor.16b	v29, v8, v29
1000059c4:     	and.16b	v30, v9, v20
1000059c8:     	and.16b	v31, v27, v20
1000059cc:     	and.16b	v8, v28, v20
1000059d0:     	and.16b	v10, v29, v20
1000059d4:     	cmeq.2d	v30, v30, #0
1000059d8:     	cmeq.2d	v31, v31, #0
1000059dc:     	cmeq.2d	v8, v8, #0
1000059e0:     	cmeq.2d	v10, v10, #0
1000059e4:     	cmhi.2d	v9, v17, v9
1000059e8:     	cmhi.2d	v27, v17, v27
1000059ec:     	cmhi.2d	v28, v17, v28
1000059f0:     	cmhi.2d	v29, v17, v29
1000059f4:     	bsl.16b	v9, v19, v18
1000059f8:     	bsl.16b	v27, v19, v18
1000059fc:     	bsl.16b	v28, v19, v18
100005a00:     	bsl.16b	v29, v19, v18
100005a04:     	bsl.16b	v30, v9, v21
100005a08:     	bif.16b	v27, v21, v31
100005a0c:     	bif.16b	v28, v21, v8
100005a10:     	bif.16b	v29, v21, v10
100005a14:     	add.2d	v1, v30, v1
100005a18:     	add.2d	v24, v27, v24
100005a1c:     	add.2d	v25, v28, v25
100005a20:     	add.2d	v26, v29, v26
100005a24:     	add.2d	v0, v0, v22
100005a28:     	add.2d	v2, v2, v23
100005a2c:     	subs	x8, x8, #0x8
100005a30:     	b.ne	0x10000599c <_main+0x130>
100005a34:     	add.2d	v0, v24, v1
100005a38:     	add.2d	v0, v25, v0
100005a3c:     	add.2d	v0, v26, v0
100005a40:     	addp.2d	d0, v0
100005a44:     	fmov	x8, d0
100005a48:     	cmp	x0, x12
100005a4c:     	b.eq	0x100005a90 <_main+0x224>
100005a50:     	sub	x12, x0, x12
100005a54:     	mov	w13, #0x7               ; =7
100005a58:     	mov	w14, #0x63              ; =99
100005a5c:     	mov	w15, #0x3               ; =3
100005a60:     	mov	x16, #0x100000001       ; =4294967297
100005a64:     	eor	x17, x11, x10
100005a68:     	lsr	x0, x17, #32
100005a6c:     	cmp	x0, #0x0
100005a70:     	csel	x0, x14, x13, eq
100005a74:     	cmp	w17, #0x0
100005a78:     	csel	x17, x0, x15, eq
100005a7c:     	add	x8, x17, x8
100005a80:     	add	x11, x11, x9
100005a84:     	add	x10, x10, x16
100005a88:     	subs	x12, x12, #0x1
100005a8c:     	b.ne	0x100005a64 <_main+0x1f8>
100005a90:     	mov	x0, x8
100005a94:     	bl	0x1000006f8 <__bril_print_int>
100005a98:     	bl	0x100000990 <__bril_print_end>
100005a9c:     	mov	w0, #0x0                ; =0
100005aa0:     	ldp	x29, x30, [sp, #0x40]
100005aa4:     	ldp	x20, x19, [sp, #0x30]
100005aa8:     	ldp	x22, x21, [sp, #0x20]
100005aac:     	ldp	d9, d8, [sp, #0x10]
100005ab0:     	ldp	d11, d10, [sp], #0x50
100005ab4:     	ret

