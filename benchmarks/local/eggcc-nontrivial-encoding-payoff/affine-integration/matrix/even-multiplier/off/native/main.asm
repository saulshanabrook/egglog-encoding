00000001000056b8 <_main>:
1000056b8:     	stp	x24, x23, [sp, #-0x40]!
1000056bc:     	stp	x22, x21, [sp, #0x10]
1000056c0:     	stp	x20, x19, [sp, #0x20]
1000056c4:     	stp	x29, x30, [sp, #0x30]
1000056c8:     	mov	x24, x1
1000056cc:     	ldr	x0, [x1, #0x8]
1000056d0:     	bl	0x1000009a4 <__bril_parse_int>
1000056d4:     	mov	x19, x0
1000056d8:     	ldr	x0, [x24, #0x10]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x20, x0
1000056e4:     	ldr	x0, [x24, #0x18]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x21, x0
1000056f0:     	ldr	x0, [x24, #0x20]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	mov	x23, x0
1000056fc:     	ldr	x0, [x24, #0x28]
100005700:     	bl	0x1000009a4 <__bril_parse_int>
100005704:     	mov	x22, x0
100005708:     	ldr	x0, [x24, #0x30]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	add	x8, x19, x20, lsl #1
100005714:     	add	x9, x21, x23, lsl #1
100005718:     	cmp	x9, x8
10000571c:     	b.ne	0x100005764 <_main+0xac>
100005720:     	add	x8, x23, x23, lsl #1
100005724:     	add	x8, x8, x21, lsl #1
100005728:     	add	x9, x20, x20, lsl #1
10000572c:     	add	x9, x9, x19, lsl #1
100005730:     	cmp	x9, x8
100005734:     	b.ne	0x100005764 <_main+0xac>
100005738:     	add	x8, x22, x21
10000573c:     	mov	w9, #0x5                ; =5
100005740:     	eor	x10, x0, x22
100005744:     	tst	x10, #0x7fffffffffffffff
100005748:     	mov	w10, #0x7               ; =7
10000574c:     	mov	w11, #0x63              ; =99
100005750:     	csel	x10, x11, x10, eq
100005754:     	add	x11, x0, x19
100005758:     	cmp	x8, x11
10000575c:     	csel	x0, x9, x10, eq
100005760:     	b	0x100005768 <_main+0xb0>
100005764:     	mov	w0, #0x3                ; =3
100005768:     	bl	0x1000006f8 <__bril_print_int>
10000576c:     	bl	0x100000990 <__bril_print_end>
100005770:     	mov	w0, #0x0                ; =0
100005774:     	ldp	x29, x30, [sp, #0x30]
100005778:     	ldp	x20, x19, [sp, #0x20]
10000577c:     	ldp	x22, x21, [sp, #0x10]
100005780:     	ldp	x24, x23, [sp], #0x40
100005784:     	ret

