00000001000056b4 <_main>:
1000056b4:     	stp	x24, x23, [sp, #-0x40]!
1000056b8:     	stp	x22, x21, [sp, #0x10]
1000056bc:     	stp	x20, x19, [sp, #0x20]
1000056c0:     	stp	x29, x30, [sp, #0x30]
1000056c4:     	mov	x24, x1
1000056c8:     	ldr	x0, [x1, #0x8]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	mov	x19, x0
1000056d4:     	ldr	x0, [x24, #0x10]
1000056d8:     	bl	0x1000009a4 <__bril_parse_int>
1000056dc:     	mov	x20, x0
1000056e0:     	ldr	x0, [x24, #0x18]
1000056e4:     	bl	0x1000009a4 <__bril_parse_int>
1000056e8:     	mov	x21, x0
1000056ec:     	ldr	x0, [x24, #0x20]
1000056f0:     	bl	0x1000009a4 <__bril_parse_int>
1000056f4:     	mov	x23, x0
1000056f8:     	ldr	x0, [x24, #0x28]
1000056fc:     	bl	0x1000009a4 <__bril_parse_int>
100005700:     	mov	x22, x0
100005704:     	ldr	x0, [x24, #0x30]
100005708:     	bl	0x1000009a4 <__bril_parse_int>
10000570c:     	add	x8, x19, x20, lsl #1
100005710:     	add	x9, x21, x23, lsl #1
100005714:     	cmp	x9, x8
100005718:     	b.ne	0x10000575c <_main+0xa8>
10000571c:     	lsl	x8, x23, #2
100005720:     	add	x8, x8, x21, lsl #1
100005724:     	lsl	x9, x20, #2
100005728:     	add	x9, x9, x19, lsl #1
10000572c:     	cmp	x9, x8
100005730:     	b.ne	0x10000575c <_main+0xa8>
100005734:     	add	x8, x22, x21
100005738:     	mov	w9, #0x5                ; =5
10000573c:     	mov	w10, #0x7               ; =7
100005740:     	mov	w11, #0x63              ; =99
100005744:     	cmp	x22, x0
100005748:     	csel	x10, x11, x10, eq
10000574c:     	add	x11, x0, x19
100005750:     	cmp	x8, x11
100005754:     	csel	x0, x9, x10, eq
100005758:     	b	0x100005760 <_main+0xac>
10000575c:     	mov	w0, #0x3                ; =3
100005760:     	bl	0x1000006f8 <__bril_print_int>
100005764:     	bl	0x100000990 <__bril_print_end>
100005768:     	mov	w0, #0x0                ; =0
10000576c:     	ldp	x29, x30, [sp, #0x30]
100005770:     	ldp	x20, x19, [sp, #0x20]
100005774:     	ldp	x22, x21, [sp, #0x10]
100005778:     	ldp	x24, x23, [sp], #0x40
10000577c:     	ret

