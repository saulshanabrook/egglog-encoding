0000000100005864 <_main>:
100005864:     	stp	d13, d12, [sp, #-0x60]!
100005868:     	stp	d11, d10, [sp, #0x10]
10000586c:     	stp	d9, d8, [sp, #0x20]
100005870:     	stp	x22, x21, [sp, #0x30]
100005874:     	stp	x20, x19, [sp, #0x40]
100005878:     	stp	x29, x30, [sp, #0x50]
10000587c:     	mov	x21, x1
100005880:     	ldr	x0, [x1, #0x8]
100005884:     	bl	0x1000009a4 <__bril_parse_int>
100005888:     	mov	x19, x0
10000588c:     	ldr	x0, [x21, #0x10]
100005890:     	bl	0x1000009a4 <__bril_parse_int>
100005894:     	mov	x20, x0
100005898:     	ldr	x0, [x21, #0x18]
10000589c:     	bl	0x1000009a4 <__bril_parse_int>
1000058a0:     	mov	w8, #0x4240             ; =16960
1000058a4:     	movk	w8, #0xf, lsl #16
1000058a8:     	cmp	x0, x8
1000058ac:     	b.hi	0x1000058d8 <_main+0x74>
1000058b0:     	cbz	x0, 0x1000058e0 <_main+0x7c>
1000058b4:     	mov	x9, #0x1                ; =1
1000058b8:     	movk	x9, #0x2, lsl #32
1000058bc:     	cmp	x0, #0x8
1000058c0:     	b.hs	0x1000058e8 <_main+0x84>
1000058c4:     	mov	x12, #0x0               ; =0
1000058c8:     	mov	x8, #0x0                ; =0
1000058cc:     	mov	x10, x19
1000058d0:     	mov	x11, x20
1000058d4:     	b	0x100005a38 <_main+0x1d4>
1000058d8:     	mov	x8, #-0x2               ; =-2
1000058dc:     	b	0x100005a78 <_main+0x214>
1000058e0:     	mov	x8, #0x0                ; =0
1000058e4:     	b	0x100005a78 <_main+0x214>
1000058e8:     	and	x12, x0, #0xffff8
1000058ec:     	lsr	x8, x12, #3
1000058f0:     	mov	x10, x12
1000058f4:     	bfi	x10, x8, #35, #17
1000058f8:     	add	x10, x19, x10
1000058fc:     	dup.2d	v0, x19
100005900:     	madd	x11, x12, x9, x20
100005904:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100005908:     	ldr	q1, [x8, #0xb50]
10000590c:     	add.2d	v0, v0, v1
100005910:     	dup.2d	v1, x20
100005914:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100005918:     	ldr	q2, [x8, #0xb60]
10000591c:     	add.2d	v2, v1, v2
100005920:     	movi.2d	v1, #0000000000000000
100005924:     	movi.4s	v3, #0x2
100005928:     	movi.4s	v4, #0x4
10000592c:     	mov	x8, #0x2                ; =2
100005930:     	movk	x8, #0x4, lsl #32
100005934:     	dup.2d	v5, x8
100005938:     	mov	x8, #0x4                ; =4
10000593c:     	movk	x8, #0x8, lsl #32
100005940:     	dup.2d	v6, x8
100005944:     	mov	x8, #0x6                ; =6
100005948:     	movk	x8, #0xc, lsl #32
10000594c:     	dup.2d	v7, x8
100005950:     	mov	x8, #0x100000000        ; =4294967296
100005954:     	dup.2d	v16, x8
100005958:     	mov	w8, #0x7                ; =7
10000595c:     	dup.2d	v17, x8
100005960:     	mov	w8, #0x63               ; =99
100005964:     	dup.2d	v18, x8
100005968:     	movi.4s	v19, #0x6
10000596c:     	mov	w8, #0x5                ; =5
100005970:     	dup.2d	v20, x8
100005974:     	movi.4s	v21, #0x8
100005978:     	mov	x8, #0x8                ; =8
10000597c:     	movk	x8, #0x10, lsl #32
100005980:     	dup.2d	v22, x8
100005984:     	mov	x8, x12
100005988:     	movi.2d	v23, #0000000000000000
10000598c:     	movi.2d	v24, #0000000000000000
100005990:     	movi.2d	v25, #0000000000000000
100005994:     	add.2d	v26, v0, v3
100005998:     	add.2d	v27, v0, v4
10000599c:     	add.2d	v28, v0, v19
1000059a0:     	add.2d	v29, v2, v5
1000059a4:     	add.2d	v30, v2, v6
1000059a8:     	add.2d	v31, v2, v7
1000059ac:     	cmeq.2d	v8, v2, v0
1000059b0:     	cmeq.2d	v9, v29, v26
1000059b4:     	cmeq.2d	v10, v30, v27
1000059b8:     	cmeq.2d	v11, v31, v28
1000059bc:     	eor.16b	v12, v2, v0
1000059c0:     	eor.16b	v26, v29, v26
1000059c4:     	eor.16b	v27, v30, v27
1000059c8:     	eor.16b	v28, v31, v28
1000059cc:     	cmhi.2d	v29, v16, v12
1000059d0:     	cmhi.2d	v26, v16, v26
1000059d4:     	cmhi.2d	v27, v16, v27
1000059d8:     	cmhi.2d	v28, v16, v28
1000059dc:     	bsl.16b	v29, v18, v17
1000059e0:     	bsl.16b	v26, v18, v17
1000059e4:     	bsl.16b	v27, v18, v17
1000059e8:     	bsl.16b	v28, v18, v17
1000059ec:     	bit.16b	v29, v20, v8
1000059f0:     	bit.16b	v26, v20, v9
1000059f4:     	bit.16b	v27, v20, v10
1000059f8:     	bit.16b	v28, v20, v11
1000059fc:     	add.2d	v1, v29, v1
100005a00:     	add.2d	v23, v26, v23
100005a04:     	add.2d	v24, v27, v24
100005a08:     	add.2d	v25, v28, v25
100005a0c:     	add.2d	v0, v0, v21
100005a10:     	add.2d	v2, v2, v22
100005a14:     	subs	x8, x8, #0x8
100005a18:     	b.ne	0x100005994 <_main+0x130>
100005a1c:     	add.2d	v0, v23, v1
100005a20:     	add.2d	v0, v24, v0
100005a24:     	add.2d	v0, v25, v0
100005a28:     	addp.2d	d0, v0
100005a2c:     	fmov	x8, d0
100005a30:     	cmp	x0, x12
100005a34:     	b.eq	0x100005a78 <_main+0x214>
100005a38:     	sub	x12, x0, x12
100005a3c:     	mov	w13, #0x7               ; =7
100005a40:     	mov	w14, #0x63              ; =99
100005a44:     	mov	w15, #0x5               ; =5
100005a48:     	mov	x16, #0x100000001       ; =4294967297
100005a4c:     	eor	x17, x11, x10
100005a50:     	lsr	x17, x17, #32
100005a54:     	cmp	x17, #0x0
100005a58:     	csel	x17, x14, x13, eq
100005a5c:     	cmp	x11, x10
100005a60:     	csel	x17, x15, x17, eq
100005a64:     	add	x8, x17, x8
100005a68:     	add	x11, x11, x9
100005a6c:     	add	x10, x10, x16
100005a70:     	subs	x12, x12, #0x1
100005a74:     	b.ne	0x100005a4c <_main+0x1e8>
100005a78:     	mov	x0, x8
100005a7c:     	bl	0x1000006f8 <__bril_print_int>
100005a80:     	bl	0x100000990 <__bril_print_end>
100005a84:     	mov	w0, #0x0                ; =0
100005a88:     	ldp	x29, x30, [sp, #0x50]
100005a8c:     	ldp	x20, x19, [sp, #0x40]
100005a90:     	ldp	x22, x21, [sp, #0x30]
100005a94:     	ldp	d9, d8, [sp, #0x20]
100005a98:     	ldp	d11, d10, [sp, #0x10]
100005a9c:     	ldp	d13, d12, [sp], #0x60
100005aa0:     	ret

