00000001000056ac <_main>:
1000056ac:     	stp	x26, x25, [sp, #-0x50]!
1000056b0:     	stp	x24, x23, [sp, #0x10]
1000056b4:     	stp	x22, x21, [sp, #0x20]
1000056b8:     	stp	x20, x19, [sp, #0x30]
1000056bc:     	stp	x29, x30, [sp, #0x40]
1000056c0:     	mov	x23, x1
1000056c4:     	ldr	x0, [x1, #0x8]
1000056c8:     	bl	0x1000009a4 <__bril_parse_int>
1000056cc:     	mov	x19, x0
1000056d0:     	ldr	x0, [x23, #0x10]
1000056d4:     	bl	0x1000009a4 <__bril_parse_int>
1000056d8:     	mov	x24, x0
1000056dc:     	ldr	x0, [x23, #0x18]
1000056e0:     	bl	0x1000009a4 <__bril_parse_int>
1000056e4:     	mov	x20, x0
1000056e8:     	ldr	x0, [x23, #0x20]
1000056ec:     	bl	0x1000009a4 <__bril_parse_int>
1000056f0:     	mov	x25, x0
1000056f4:     	ldr	x0, [x23, #0x28]
1000056f8:     	bl	0x1000009a4 <__bril_parse_int>
1000056fc:     	mov	x22, x0
100005700:     	ldr	x0, [x23, #0x30]
100005704:     	bl	0x1000009a4 <__bril_parse_int>
100005708:     	mov	x21, x0
10000570c:     	ldr	x0, [x23, #0x38]
100005710:     	bl	0x1000009a4 <__bril_parse_int>
100005714:     	mov	x26, x0
100005718:     	ldr	x0, [x23, #0x40]
10000571c:     	bl	0x1000009a4 <__bril_parse_int>
100005720:     	cmp	x26, x0
100005724:     	csel	x8, x19, x24, lt
100005728:     	csel	x9, x20, x25, lt
10000572c:     	csel	x10, x24, x19, lt
100005730:     	csel	x11, x25, x20, lt
100005734:     	cmp	x9, x8
100005738:     	ccmp	x10, x11, #0x0, eq
10000573c:     	b.eq	0x100005748 <_main+0x9c>
100005740:     	mov	w0, #0x3                ; =3
100005744:     	b	0x100005770 <_main+0xc4>
100005748:     	add	x8, x22, x20
10000574c:     	mov	w9, #0x5                ; =5
100005750:     	eor	x10, x21, x22
100005754:     	tst	x10, #0x7fffffffffffffff
100005758:     	mov	w10, #0x7               ; =7
10000575c:     	mov	w11, #0x63              ; =99
100005760:     	csel	x10, x11, x10, eq
100005764:     	add	x11, x21, x19
100005768:     	cmp	x8, x11
10000576c:     	csel	x0, x9, x10, eq
100005770:     	bl	0x1000006f8 <__bril_print_int>
100005774:     	bl	0x100000990 <__bril_print_end>
100005778:     	mov	w0, #0x0                ; =0
10000577c:     	ldp	x29, x30, [sp, #0x40]
100005780:     	ldp	x20, x19, [sp, #0x30]
100005784:     	ldp	x22, x21, [sp, #0x20]
100005788:     	ldp	x24, x23, [sp, #0x10]
10000578c:     	ldp	x26, x25, [sp], #0x50
100005790:     	ret

