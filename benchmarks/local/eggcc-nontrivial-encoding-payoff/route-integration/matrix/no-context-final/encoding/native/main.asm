00000001000056b0 <_main>:
1000056b0:     	stp	x26, x25, [sp, #-0x50]!
1000056b4:     	stp	x24, x23, [sp, #0x10]
1000056b8:     	stp	x22, x21, [sp, #0x20]
1000056bc:     	stp	x20, x19, [sp, #0x30]
1000056c0:     	stp	x29, x30, [sp, #0x40]
1000056c4:     	mov	x26, x1
1000056c8:     	ldr	x0, [x1, #0x8]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	mov	x19, x0
1000056d4:     	ldr	x0, [x26, #0x10]
1000056d8:     	bl	0x1000009a4 <__bril_parse_int>
1000056dc:     	mov	x20, x0
1000056e0:     	ldr	x0, [x26, #0x18]
1000056e4:     	bl	0x1000009a4 <__bril_parse_int>
1000056e8:     	mov	x21, x0
1000056ec:     	ldr	x0, [x26, #0x20]
1000056f0:     	bl	0x1000009a4 <__bril_parse_int>
1000056f4:     	mov	x24, x0
1000056f8:     	ldr	x0, [x26, #0x28]
1000056fc:     	bl	0x1000009a4 <__bril_parse_int>
100005700:     	mov	x22, x0
100005704:     	ldr	x0, [x26, #0x30]
100005708:     	bl	0x1000009a4 <__bril_parse_int>
10000570c:     	mov	x23, x0
100005710:     	ldr	x0, [x26, #0x38]
100005714:     	bl	0x1000009a4 <__bril_parse_int>
100005718:     	mov	x25, x0
10000571c:     	ldr	x0, [x26, #0x40]
100005720:     	bl	0x1000009a4 <__bril_parse_int>
100005724:     	cmp	x25, x0
100005728:     	csel	x8, x19, x20, lt
10000572c:     	csel	x9, x21, x24, lt
100005730:     	cmp	x9, x8
100005734:     	b.ne	0x100005778 <_main+0xc8>
100005738:     	cmp	x25, x0
10000573c:     	csel	x8, x24, x21, lt
100005740:     	csel	x9, x20, x19, lt
100005744:     	mov	w10, #0x3               ; =3
100005748:     	add	x11, x22, x21
10000574c:     	mov	w12, #0x7               ; =7
100005750:     	mov	w13, #0x63              ; =99
100005754:     	cmp	x22, x23
100005758:     	csel	x12, x13, x12, eq
10000575c:     	mov	w13, #0x5               ; =5
100005760:     	add	x14, x23, x19
100005764:     	cmp	x11, x14
100005768:     	csel	x11, x13, x12, eq
10000576c:     	cmp	x9, x8
100005770:     	csel	x0, x10, x11, ne
100005774:     	b	0x10000577c <_main+0xcc>
100005778:     	mov	w0, #0x3                ; =3
10000577c:     	bl	0x1000006f8 <__bril_print_int>
100005780:     	bl	0x100000990 <__bril_print_end>
100005784:     	mov	w0, #0x0                ; =0
100005788:     	ldp	x29, x30, [sp, #0x40]
10000578c:     	ldp	x20, x19, [sp, #0x30]
100005790:     	ldp	x22, x21, [sp, #0x20]
100005794:     	ldp	x24, x23, [sp, #0x10]
100005798:     	ldp	x26, x25, [sp], #0x50
10000579c:     	ret

