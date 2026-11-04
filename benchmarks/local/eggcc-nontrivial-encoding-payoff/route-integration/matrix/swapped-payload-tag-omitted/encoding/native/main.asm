00000001000056a8 <_main>:
1000056a8:     	stp	x26, x25, [sp, #-0x50]!
1000056ac:     	stp	x24, x23, [sp, #0x10]
1000056b0:     	stp	x22, x21, [sp, #0x20]
1000056b4:     	stp	x20, x19, [sp, #0x30]
1000056b8:     	stp	x29, x30, [sp, #0x40]
1000056bc:     	mov	x23, x1
1000056c0:     	ldr	x0, [x1, #0x8]
1000056c4:     	bl	0x1000009a4 <__bril_parse_int>
1000056c8:     	mov	x19, x0
1000056cc:     	ldr	x0, [x23, #0x10]
1000056d0:     	bl	0x1000009a4 <__bril_parse_int>
1000056d4:     	mov	x24, x0
1000056d8:     	ldr	x0, [x23, #0x18]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x20, x0
1000056e4:     	ldr	x0, [x23, #0x20]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x25, x0
1000056f0:     	ldr	x0, [x23, #0x28]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	mov	x21, x0
1000056fc:     	ldr	x0, [x23, #0x30]
100005700:     	bl	0x1000009a4 <__bril_parse_int>
100005704:     	mov	x22, x0
100005708:     	ldr	x0, [x23, #0x38]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	mov	x26, x0
100005714:     	ldr	x0, [x23, #0x40]
100005718:     	bl	0x1000009a4 <__bril_parse_int>
10000571c:     	cmp	x26, x0
100005720:     	csel	x8, x19, x24, lt
100005724:     	csel	x9, x25, x20, lt
100005728:     	csel	x10, x24, x19, lt
10000572c:     	csel	x11, x20, x25, lt
100005730:     	cmp	x9, x8
100005734:     	ccmp	x10, x11, #0x0, eq
100005738:     	b.eq	0x100005744 <_main+0x9c>
10000573c:     	mov	w0, #0x3                ; =3
100005740:     	b	0x100005768 <_main+0xc0>
100005744:     	add	x8, x21, x20
100005748:     	mov	w9, #0x5                ; =5
10000574c:     	mov	w10, #0x7               ; =7
100005750:     	mov	w11, #0x63              ; =99
100005754:     	cmp	x21, x22
100005758:     	csel	x10, x11, x10, eq
10000575c:     	add	x11, x22, x19
100005760:     	cmp	x8, x11
100005764:     	csel	x0, x9, x10, eq
100005768:     	bl	0x1000006f8 <__bril_print_int>
10000576c:     	bl	0x100000990 <__bril_print_end>
100005770:     	mov	w0, #0x0                ; =0
100005774:     	ldp	x29, x30, [sp, #0x40]
100005778:     	ldp	x20, x19, [sp, #0x30]
10000577c:     	ldp	x22, x21, [sp, #0x20]
100005780:     	ldp	x24, x23, [sp, #0x10]
100005784:     	ldp	x26, x25, [sp], #0x50
100005788:     	ret

