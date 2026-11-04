0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, lt
10000565c:     	csel	x9, x0, x1, gt
100005660:     	cset	w10, lt
100005664:     	cmp	x2, x3
100005668:     	csel	x11, x2, x3, lt
10000566c:     	csel	x12, x2, x3, gt
100005670:     	cset	w13, ge
100005674:     	cmp	x8, x11
100005678:     	eor	w8, w10, w13
10000567c:     	ccmp	x12, x9, #0x0, eq
100005680:     	cset	w9, eq
100005684:     	add	x10, x4, x2
100005688:     	add	x11, x5, x0
10000568c:     	cmp	x10, x11
100005690:     	mov	w10, #0x7               ; =7
100005694:     	mov	w11, #0x5               ; =5
100005698:     	csel	x10, x11, x10, eq
10000569c:     	tst	w9, w8
1000056a0:     	mov	w8, #0x3                ; =3
1000056a4:     	csel	x0, x10, x8, ne
1000056a8:     	bl	0x1000006f8 <__bril_print_int>
1000056ac:     	ldp	x29, x30, [sp], #0x10
1000056b0:     	b	0x100000990 <__bril_print_end>


00000001000056b4 <_main>:
1000056b4:     	stp	x24, x23, [sp, #-0x40]!
1000056b8:     	stp	x22, x21, [sp, #0x10]
1000056bc:     	stp	x20, x19, [sp, #0x20]
1000056c0:     	stp	x29, x30, [sp, #0x30]
1000056c4:     	mov	x19, x1
1000056c8:     	ldr	x0, [x1, #0x8]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	mov	x20, x0
1000056d4:     	ldr	x0, [x19, #0x10]
1000056d8:     	bl	0x1000009a4 <__bril_parse_int>
1000056dc:     	mov	x21, x0
1000056e0:     	ldr	x0, [x19, #0x18]
1000056e4:     	bl	0x1000009a4 <__bril_parse_int>
1000056e8:     	mov	x22, x0
1000056ec:     	ldr	x0, [x19, #0x20]
1000056f0:     	bl	0x1000009a4 <__bril_parse_int>
1000056f4:     	mov	x23, x0
1000056f8:     	ldr	x0, [x19, #0x28]
1000056fc:     	bl	0x1000009a4 <__bril_parse_int>
100005700:     	mov	x24, x0
100005704:     	ldr	x0, [x19, #0x30]
100005708:     	bl	0x1000009a4 <__bril_parse_int>
10000570c:     	cmp	x20, x21
100005710:     	csel	x8, x20, x21, lt
100005714:     	csel	x9, x20, x21, gt
100005718:     	cset	w10, lt
10000571c:     	cmp	x22, x23
100005720:     	csel	x11, x22, x23, lt
100005724:     	csel	x12, x22, x23, gt
100005728:     	cset	w13, ge
10000572c:     	cmp	x8, x11
100005730:     	eor	w8, w10, w13
100005734:     	ccmp	x12, x9, #0x0, eq
100005738:     	cset	w9, eq
10000573c:     	add	x10, x24, x22
100005740:     	add	x11, x0, x20
100005744:     	cmp	x10, x11
100005748:     	mov	w10, #0x7               ; =7
10000574c:     	mov	w11, #0x5               ; =5
100005750:     	csel	x10, x11, x10, eq
100005754:     	tst	w8, w9
100005758:     	mov	w8, #0x3                ; =3
10000575c:     	csel	x0, x10, x8, ne
100005760:     	bl	0x1000006f8 <__bril_print_int>
100005764:     	bl	0x100000990 <__bril_print_end>
100005768:     	mov	w0, #0x0                ; =0
10000576c:     	ldp	x29, x30, [sp, #0x30]
100005770:     	ldp	x20, x19, [sp, #0x20]
100005774:     	ldp	x22, x21, [sp, #0x10]
100005778:     	ldp	x24, x23, [sp], #0x40
10000577c:     	ret

