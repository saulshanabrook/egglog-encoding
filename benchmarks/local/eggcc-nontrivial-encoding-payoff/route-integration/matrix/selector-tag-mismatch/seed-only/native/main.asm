00000001000056b0 <_main>:
1000056b0:     	stp	x26, x25, [sp, #-0x50]!
1000056b4:     	stp	x24, x23, [sp, #0x10]
1000056b8:     	stp	x22, x21, [sp, #0x20]
1000056bc:     	stp	x20, x19, [sp, #0x30]
1000056c0:     	stp	x29, x30, [sp, #0x40]
1000056c4:     	mov	x23, x1
1000056c8:     	ldr	x0, [x1, #0x8]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	mov	x19, x0
1000056d4:     	ldr	x0, [x23, #0x10]
1000056d8:     	bl	0x1000009a4 <__bril_parse_int>
1000056dc:     	mov	x24, x0
1000056e0:     	ldr	x0, [x23, #0x18]
1000056e4:     	bl	0x1000009a4 <__bril_parse_int>
1000056e8:     	mov	x20, x0
1000056ec:     	ldr	x0, [x23, #0x20]
1000056f0:     	bl	0x1000009a4 <__bril_parse_int>
1000056f4:     	mov	x25, x0
1000056f8:     	ldr	x0, [x23, #0x28]
1000056fc:     	bl	0x1000009a4 <__bril_parse_int>
100005700:     	mov	x21, x0
100005704:     	ldr	x0, [x23, #0x30]
100005708:     	bl	0x1000009a4 <__bril_parse_int>
10000570c:     	mov	x22, x0
100005710:     	ldr	x0, [x23, #0x38]
100005714:     	bl	0x1000009a4 <__bril_parse_int>
100005718:     	mov	x26, x0
10000571c:     	ldr	x0, [x23, #0x40]
100005720:     	bl	0x1000009a4 <__bril_parse_int>
100005724:     	cmp	x26, x0
100005728:     	csel	x8, x19, x24, lt
10000572c:     	csel	x9, x24, x19, lt
100005730:     	cmp	x0, x26
100005734:     	csel	x10, x20, x25, lt
100005738:     	csel	x11, x25, x20, lt
10000573c:     	cmp	x10, x8
100005740:     	ccmp	x9, x11, #0x0, eq
100005744:     	b.eq	0x100005750 <_main+0xa0>
100005748:     	mov	w0, #0x3                ; =3
10000574c:     	b	0x100005774 <_main+0xc4>
100005750:     	add	x8, x21, x20
100005754:     	mov	w9, #0x5                ; =5
100005758:     	mov	w10, #0x7               ; =7
10000575c:     	mov	w11, #0x63              ; =99
100005760:     	cmp	x21, x22
100005764:     	csel	x10, x11, x10, eq
100005768:     	add	x11, x22, x19
10000576c:     	cmp	x8, x11
100005770:     	csel	x0, x9, x10, eq
100005774:     	bl	0x1000006f8 <__bril_print_int>
100005778:     	bl	0x100000990 <__bril_print_end>
10000577c:     	mov	w0, #0x0                ; =0
100005780:     	ldp	x29, x30, [sp, #0x40]
100005784:     	ldp	x20, x19, [sp, #0x30]
100005788:     	ldp	x22, x21, [sp, #0x20]
10000578c:     	ldp	x24, x23, [sp, #0x10]
100005790:     	ldp	x26, x25, [sp], #0x50
100005794:     	ret

