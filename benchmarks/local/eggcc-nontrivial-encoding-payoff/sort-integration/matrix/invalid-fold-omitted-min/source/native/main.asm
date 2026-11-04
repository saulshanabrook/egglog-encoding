0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, gt
10000565c:     	cset	w9, lt
100005660:     	cmp	x2, x3
100005664:     	csel	x10, x2, x3, gt
100005668:     	cset	w11, ge
10000566c:     	cmp	x8, x10
100005670:     	cset	w8, eq
100005674:     	eor	w9, w9, w11
100005678:     	add	x10, x4, x2
10000567c:     	add	x11, x5, x0
100005680:     	cmp	x10, x11
100005684:     	mov	w10, #0x7               ; =7
100005688:     	mov	w11, #0x5               ; =5
10000568c:     	csel	x10, x11, x10, eq
100005690:     	tst	w8, w9
100005694:     	mov	w8, #0x3                ; =3
100005698:     	csel	x0, x10, x8, ne
10000569c:     	bl	0x1000006f8 <__bril_print_int>
1000056a0:     	ldp	x29, x30, [sp], #0x10
1000056a4:     	b	0x100000990 <__bril_print_end>


00000001000056a8 <_main>:
1000056a8:     	stp	x24, x23, [sp, #-0x40]!
1000056ac:     	stp	x22, x21, [sp, #0x10]
1000056b0:     	stp	x20, x19, [sp, #0x20]
1000056b4:     	stp	x29, x30, [sp, #0x30]
1000056b8:     	mov	x19, x1
1000056bc:     	ldr	x0, [x1, #0x8]
1000056c0:     	bl	0x1000009a4 <__bril_parse_int>
1000056c4:     	mov	x20, x0
1000056c8:     	ldr	x0, [x19, #0x10]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	mov	x21, x0
1000056d4:     	ldr	x0, [x19, #0x18]
1000056d8:     	bl	0x1000009a4 <__bril_parse_int>
1000056dc:     	mov	x22, x0
1000056e0:     	ldr	x0, [x19, #0x20]
1000056e4:     	bl	0x1000009a4 <__bril_parse_int>
1000056e8:     	mov	x23, x0
1000056ec:     	ldr	x0, [x19, #0x28]
1000056f0:     	bl	0x1000009a4 <__bril_parse_int>
1000056f4:     	mov	x24, x0
1000056f8:     	ldr	x0, [x19, #0x30]
1000056fc:     	bl	0x1000009a4 <__bril_parse_int>
100005700:     	cmp	x20, x21
100005704:     	csel	x8, x20, x21, gt
100005708:     	cset	w9, lt
10000570c:     	cmp	x22, x23
100005710:     	csel	x10, x22, x23, gt
100005714:     	cset	w11, ge
100005718:     	cmp	x8, x10
10000571c:     	cset	w8, eq
100005720:     	eor	w9, w9, w11
100005724:     	add	x10, x24, x22
100005728:     	add	x11, x0, x20
10000572c:     	cmp	x10, x11
100005730:     	mov	w10, #0x7               ; =7
100005734:     	mov	w11, #0x5               ; =5
100005738:     	csel	x10, x11, x10, eq
10000573c:     	tst	w8, w9
100005740:     	mov	w8, #0x3                ; =3
100005744:     	csel	x0, x10, x8, ne
100005748:     	bl	0x1000006f8 <__bril_print_int>
10000574c:     	bl	0x100000990 <__bril_print_end>
100005750:     	mov	w0, #0x0                ; =0
100005754:     	ldp	x29, x30, [sp, #0x30]
100005758:     	ldp	x20, x19, [sp, #0x20]
10000575c:     	ldp	x22, x21, [sp, #0x10]
100005760:     	ldp	x24, x23, [sp], #0x40
100005764:     	ret

