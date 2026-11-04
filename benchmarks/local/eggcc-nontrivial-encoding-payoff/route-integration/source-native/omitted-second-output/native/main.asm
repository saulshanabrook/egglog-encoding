000000010000569c <_main>:
10000569c:     	stp	x26, x25, [sp, #-0x50]!
1000056a0:     	stp	x24, x23, [sp, #0x10]
1000056a4:     	stp	x22, x21, [sp, #0x20]
1000056a8:     	stp	x20, x19, [sp, #0x30]
1000056ac:     	stp	x29, x30, [sp, #0x40]
1000056b0:     	mov	x20, x1
1000056b4:     	ldr	x0, [x1, #0x8]
1000056b8:     	bl	0x1000009a4 <__bril_parse_int>
1000056bc:     	mov	x19, x0
1000056c0:     	ldr	x0, [x20, #0x10]
1000056c4:     	bl	0x1000009a4 <__bril_parse_int>
1000056c8:     	mov	x21, x0
1000056cc:     	ldr	x0, [x20, #0x18]
1000056d0:     	bl	0x1000009a4 <__bril_parse_int>
1000056d4:     	mov	x22, x0
1000056d8:     	ldr	x0, [x20, #0x20]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x23, x0
1000056e4:     	ldr	x0, [x20, #0x28]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x24, x0
1000056f0:     	ldr	x0, [x20, #0x30]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	mov	x25, x0
1000056fc:     	ldr	x0, [x20, #0x38]
100005700:     	bl	0x1000009a4 <__bril_parse_int>
100005704:     	mov	x26, x0
100005708:     	ldr	x0, [x20, #0x40]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	cmp	x26, x0
100005714:     	csel	x8, x19, x21, lt
100005718:     	csel	x9, x22, x23, lt
10000571c:     	mov	w10, #0x3               ; =3
100005720:     	add	x11, x24, x22
100005724:     	mov	w12, #0x7               ; =7
100005728:     	mov	w13, #0x63              ; =99
10000572c:     	cmp	x24, x25
100005730:     	csel	x12, x13, x12, eq
100005734:     	mov	w13, #0x5               ; =5
100005738:     	add	x14, x25, x19
10000573c:     	cmp	x11, x14
100005740:     	csel	x11, x13, x12, eq
100005744:     	cmp	x8, x9
100005748:     	csel	x0, x10, x11, ne
10000574c:     	bl	0x1000006f8 <__bril_print_int>
100005750:     	bl	0x100000990 <__bril_print_end>
100005754:     	mov	w0, #0x0                ; =0
100005758:     	ldp	x29, x30, [sp, #0x40]
10000575c:     	ldp	x20, x19, [sp, #0x30]
100005760:     	ldp	x22, x21, [sp, #0x20]
100005764:     	ldp	x24, x23, [sp, #0x10]
100005768:     	ldp	x26, x25, [sp], #0x50
10000576c:     	ret

