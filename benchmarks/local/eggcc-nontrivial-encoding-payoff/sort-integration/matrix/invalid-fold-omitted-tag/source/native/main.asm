0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, lt
10000565c:     	csel	x9, x0, x1, gt
100005660:     	cmp	x2, x3
100005664:     	csel	x10, x2, x3, lt
100005668:     	csel	x11, x2, x3, gt
10000566c:     	add	x12, x4, x2
100005670:     	add	x13, x5, x0
100005674:     	cmp	x12, x13
100005678:     	mov	w12, #0x7               ; =7
10000567c:     	mov	w13, #0x5               ; =5
100005680:     	csel	x12, x13, x12, eq
100005684:     	cmp	x9, x11
100005688:     	ccmp	x8, x10, #0x0, eq
10000568c:     	mov	w8, #0x3                ; =3
100005690:     	csel	x0, x12, x8, eq
100005694:     	bl	0x1000006f8 <__bril_print_int>
100005698:     	ldp	x29, x30, [sp], #0x10
10000569c:     	b	0x100000990 <__bril_print_end>


00000001000056a0 <_main>:
1000056a0:     	stp	x24, x23, [sp, #-0x40]!
1000056a4:     	stp	x22, x21, [sp, #0x10]
1000056a8:     	stp	x20, x19, [sp, #0x20]
1000056ac:     	stp	x29, x30, [sp, #0x30]
1000056b0:     	mov	x19, x1
1000056b4:     	ldr	x0, [x1, #0x8]
1000056b8:     	bl	0x1000009a4 <__bril_parse_int>
1000056bc:     	mov	x20, x0
1000056c0:     	ldr	x0, [x19, #0x10]
1000056c4:     	bl	0x1000009a4 <__bril_parse_int>
1000056c8:     	mov	x21, x0
1000056cc:     	ldr	x0, [x19, #0x18]
1000056d0:     	bl	0x1000009a4 <__bril_parse_int>
1000056d4:     	mov	x22, x0
1000056d8:     	ldr	x0, [x19, #0x20]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x23, x0
1000056e4:     	ldr	x0, [x19, #0x28]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x24, x0
1000056f0:     	ldr	x0, [x19, #0x30]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	cmp	x20, x21
1000056fc:     	csel	x8, x20, x21, lt
100005700:     	csel	x9, x20, x21, gt
100005704:     	cmp	x22, x23
100005708:     	csel	x10, x22, x23, lt
10000570c:     	csel	x11, x22, x23, gt
100005710:     	add	x12, x24, x22
100005714:     	add	x13, x0, x20
100005718:     	cmp	x12, x13
10000571c:     	mov	w12, #0x7               ; =7
100005720:     	mov	w13, #0x5               ; =5
100005724:     	csel	x12, x13, x12, eq
100005728:     	cmp	x9, x11
10000572c:     	ccmp	x8, x10, #0x0, eq
100005730:     	mov	w8, #0x3                ; =3
100005734:     	csel	x0, x12, x8, eq
100005738:     	bl	0x1000006f8 <__bril_print_int>
10000573c:     	bl	0x100000990 <__bril_print_end>
100005740:     	mov	w0, #0x0                ; =0
100005744:     	ldp	x29, x30, [sp, #0x30]
100005748:     	ldp	x20, x19, [sp, #0x20]
10000574c:     	ldp	x22, x21, [sp, #0x10]
100005750:     	ldp	x24, x23, [sp], #0x40
100005754:     	ret

