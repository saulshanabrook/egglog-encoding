00000001000056a0 <_main>:
1000056a0:     	stp	x24, x23, [sp, #-0x40]!
1000056a4:     	stp	x22, x21, [sp, #0x10]
1000056a8:     	stp	x20, x19, [sp, #0x20]
1000056ac:     	stp	x29, x30, [sp, #0x30]
1000056b0:     	mov	x22, x1
1000056b4:     	ldr	x0, [x1, #0x8]
1000056b8:     	bl	0x1000009a4 <__bril_parse_int>
1000056bc:     	mov	x19, x0
1000056c0:     	ldr	x0, [x22, #0x10]
1000056c4:     	bl	0x1000009a4 <__bril_parse_int>
1000056c8:     	mov	x23, x0
1000056cc:     	ldr	x0, [x22, #0x18]
1000056d0:     	bl	0x1000009a4 <__bril_parse_int>
1000056d4:     	mov	x20, x0
1000056d8:     	ldr	x0, [x22, #0x20]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x24, x0
1000056e4:     	ldr	x0, [x22, #0x28]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x21, x0
1000056f0:     	ldr	x0, [x22, #0x30]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	add	x8, x23, x23, lsl #1
1000056fc:     	add	x8, x8, x19, lsl #1
100005700:     	add	x9, x24, x24, lsl #1
100005704:     	add	x9, x9, x20, lsl #1
100005708:     	cmp	x8, x9
10000570c:     	b.ne	0x100005738 <_main+0x98>
100005710:     	add	x8, x21, x20
100005714:     	mov	w9, #0x5                ; =5
100005718:     	mov	w10, #0x7               ; =7
10000571c:     	mov	w11, #0x63              ; =99
100005720:     	cmp	x21, x0
100005724:     	csel	x10, x11, x10, eq
100005728:     	add	x11, x0, x19
10000572c:     	cmp	x8, x11
100005730:     	csel	x0, x9, x10, eq
100005734:     	b	0x10000573c <_main+0x9c>
100005738:     	mov	w0, #0x3                ; =3
10000573c:     	bl	0x1000006f8 <__bril_print_int>
100005740:     	bl	0x100000990 <__bril_print_end>
100005744:     	mov	w0, #0x0                ; =0
100005748:     	ldp	x29, x30, [sp, #0x30]
10000574c:     	ldp	x20, x19, [sp, #0x20]
100005750:     	ldp	x22, x21, [sp, #0x10]
100005754:     	ldp	x24, x23, [sp], #0x40
100005758:     	ret

