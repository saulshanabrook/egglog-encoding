0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, lt
10000565c:     	csel	x9, x0, x1, gt
100005660:     	cset	w10, lt
100005664:     	cmp	x2, x3
100005668:     	csel	x11, x2, x3, lt
10000566c:     	csel	x12, x2, x3, gt
100005670:     	cmp	x8, x11
100005674:     	ccmp	x9, x12, #0x0, eq
100005678:     	cset	w8, eq
10000567c:     	cmp	x3, x2
100005680:     	cset	w9, ge
100005684:     	eor	w9, w10, w9
100005688:     	add	x10, x4, x2
10000568c:     	add	x11, x5, x0
100005690:     	cmp	x10, x11
100005694:     	mov	w10, #0x7               ; =7
100005698:     	mov	w11, #0x5               ; =5
10000569c:     	csel	x10, x11, x10, eq
1000056a0:     	tst	w8, w9
1000056a4:     	mov	w8, #0x3                ; =3
1000056a8:     	csel	x0, x10, x8, ne
1000056ac:     	bl	0x1000006f8 <__bril_print_int>
1000056b0:     	ldp	x29, x30, [sp], #0x10
1000056b4:     	b	0x100000990 <__bril_print_end>


00000001000056b8 <_main>:
1000056b8:     	stp	x24, x23, [sp, #-0x40]!
1000056bc:     	stp	x22, x21, [sp, #0x10]
1000056c0:     	stp	x20, x19, [sp, #0x20]
1000056c4:     	stp	x29, x30, [sp, #0x30]
1000056c8:     	mov	x19, x1
1000056cc:     	ldr	x0, [x1, #0x8]
1000056d0:     	bl	0x1000009a4 <__bril_parse_int>
1000056d4:     	mov	x20, x0
1000056d8:     	ldr	x0, [x19, #0x10]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x21, x0
1000056e4:     	ldr	x0, [x19, #0x18]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x22, x0
1000056f0:     	ldr	x0, [x19, #0x20]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	mov	x23, x0
1000056fc:     	ldr	x0, [x19, #0x28]
100005700:     	bl	0x1000009a4 <__bril_parse_int>
100005704:     	mov	x24, x0
100005708:     	ldr	x0, [x19, #0x30]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	cmp	x20, x21
100005714:     	csel	x8, x20, x21, lt
100005718:     	csel	x9, x20, x21, gt
10000571c:     	cset	w10, lt
100005720:     	cmp	x22, x23
100005724:     	csel	x11, x22, x23, lt
100005728:     	csel	x12, x22, x23, gt
10000572c:     	cmp	x8, x11
100005730:     	ccmp	x9, x12, #0x0, eq
100005734:     	cset	w8, eq
100005738:     	cmp	x23, x22
10000573c:     	cset	w9, ge
100005740:     	eor	w9, w10, w9
100005744:     	add	x10, x24, x22
100005748:     	add	x11, x0, x20
10000574c:     	cmp	x10, x11
100005750:     	mov	w10, #0x7               ; =7
100005754:     	mov	w11, #0x5               ; =5
100005758:     	csel	x10, x11, x10, eq
10000575c:     	tst	w9, w8
100005760:     	mov	w8, #0x3                ; =3
100005764:     	csel	x0, x10, x8, ne
100005768:     	bl	0x1000006f8 <__bril_print_int>
10000576c:     	bl	0x100000990 <__bril_print_end>
100005770:     	mov	w0, #0x0                ; =0
100005774:     	ldp	x29, x30, [sp, #0x30]
100005778:     	ldp	x20, x19, [sp, #0x20]
10000577c:     	ldp	x22, x21, [sp, #0x10]
100005780:     	ldp	x24, x23, [sp], #0x40
100005784:     	ret

