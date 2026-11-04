0000000100005698 <_main>:
100005698:     	stp	x24, x23, [sp, #-0x40]!
10000569c:     	stp	x22, x21, [sp, #0x10]
1000056a0:     	stp	x20, x19, [sp, #0x20]
1000056a4:     	stp	x29, x30, [sp, #0x30]
1000056a8:     	mov	x19, x1
1000056ac:     	ldr	x0, [x1, #0x8]
1000056b0:     	bl	0x1000009a4 <__bril_parse_int>
1000056b4:     	mov	x20, x0
1000056b8:     	ldr	x0, [x19, #0x10]
1000056bc:     	bl	0x1000009a4 <__bril_parse_int>
1000056c0:     	mov	x21, x0
1000056c4:     	ldr	x0, [x19, #0x18]
1000056c8:     	bl	0x1000009a4 <__bril_parse_int>
1000056cc:     	mov	x22, x0
1000056d0:     	ldr	x0, [x19, #0x20]
1000056d4:     	bl	0x1000009a4 <__bril_parse_int>
1000056d8:     	mov	x23, x0
1000056dc:     	ldr	x0, [x19, #0x28]
1000056e0:     	bl	0x1000009a4 <__bril_parse_int>
1000056e4:     	mov	x24, x0
1000056e8:     	ldr	x0, [x19, #0x30]
1000056ec:     	bl	0x1000009a4 <__bril_parse_int>
1000056f0:     	add	x8, x20, x21, lsl #1
1000056f4:     	add	x9, x22, x23, lsl #1
1000056f8:     	mov	w10, #0x3               ; =3
1000056fc:     	add	x11, x24, x22
100005700:     	mov	w12, #0x7               ; =7
100005704:     	mov	w13, #0x63              ; =99
100005708:     	cmp	x24, x0
10000570c:     	csel	x12, x13, x12, eq
100005710:     	mov	w13, #0x5               ; =5
100005714:     	add	x14, x0, x20
100005718:     	cmp	x11, x14
10000571c:     	csel	x11, x13, x12, eq
100005720:     	cmp	x9, x8
100005724:     	csel	x0, x10, x11, ne
100005728:     	bl	0x1000006f8 <__bril_print_int>
10000572c:     	bl	0x100000990 <__bril_print_end>
100005730:     	mov	w0, #0x0                ; =0
100005734:     	ldp	x29, x30, [sp, #0x30]
100005738:     	ldp	x20, x19, [sp, #0x20]
10000573c:     	ldp	x22, x21, [sp, #0x10]
100005740:     	ldp	x24, x23, [sp], #0x40
100005744:     	ret

