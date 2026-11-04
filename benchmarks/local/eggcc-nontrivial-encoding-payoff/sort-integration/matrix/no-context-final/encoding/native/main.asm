0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, lt
10000565c:     	cmp	x2, x3
100005660:     	csel	x9, x2, x3, lt
100005664:     	mov	w10, #0x3               ; =3
100005668:     	cmp	x0, x1
10000566c:     	csel	x11, x0, x1, gt
100005670:     	cset	w12, lt
100005674:     	cmp	x2, x3
100005678:     	csel	x13, x2, x3, gt
10000567c:     	cset	w14, ge
100005680:     	eor	w12, w12, w14
100005684:     	mov	w14, #0x3               ; =3
100005688:     	add	x15, x4, x2
10000568c:     	mov	w16, #0x7               ; =7
100005690:     	mov	w17, #0x63              ; =99
100005694:     	cmp	x4, x5
100005698:     	csel	x16, x17, x16, eq
10000569c:     	mov	w17, #0x5               ; =5
1000056a0:     	add	x0, x5, x0
1000056a4:     	cmp	x15, x0
1000056a8:     	csel	x15, x17, x16, eq
1000056ac:     	tst	w12, #0x1
1000056b0:     	csel	x12, x15, x14, ne
1000056b4:     	cmp	x11, x13
1000056b8:     	csel	x11, x14, x12, ne
1000056bc:     	cmp	x8, x9
1000056c0:     	csel	x0, x10, x11, ne
1000056c4:     	bl	0x1000006f8 <__bril_print_int>
1000056c8:     	ldp	x29, x30, [sp], #0x10
1000056cc:     	b	0x100000990 <__bril_print_end>


00000001000056d0 <_main>:
1000056d0:     	stp	x24, x23, [sp, #-0x40]!
1000056d4:     	stp	x22, x21, [sp, #0x10]
1000056d8:     	stp	x20, x19, [sp, #0x20]
1000056dc:     	stp	x29, x30, [sp, #0x30]
1000056e0:     	mov	x24, x1
1000056e4:     	ldr	x0, [x1, #0x8]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x19, x0
1000056f0:     	ldr	x0, [x24, #0x10]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	mov	x22, x0
1000056fc:     	ldr	x0, [x24, #0x18]
100005700:     	bl	0x1000009a4 <__bril_parse_int>
100005704:     	mov	x20, x0
100005708:     	ldr	x0, [x24, #0x20]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	mov	x23, x0
100005714:     	ldr	x0, [x24, #0x28]
100005718:     	bl	0x1000009a4 <__bril_parse_int>
10000571c:     	mov	x21, x0
100005720:     	ldr	x0, [x24, #0x30]
100005724:     	bl	0x1000009a4 <__bril_parse_int>
100005728:     	cmp	x19, x22
10000572c:     	csel	x8, x19, x22, lt
100005730:     	cmp	x20, x23
100005734:     	csel	x9, x20, x23, lt
100005738:     	cmp	x8, x9
10000573c:     	b.ne	0x100005768 <_main+0x98>
100005740:     	cmp	x19, x22
100005744:     	csel	x8, x19, x22, gt
100005748:     	cset	w9, lt
10000574c:     	cmp	x20, x23
100005750:     	csel	x10, x20, x23, gt
100005754:     	cset	w11, ge
100005758:     	eor	w9, w9, w11
10000575c:     	cmp	x8, x10
100005760:     	ccmp	w9, #0x0, #0x4, eq
100005764:     	b.ne	0x100005770 <_main+0xa0>
100005768:     	mov	w0, #0x3                ; =3
10000576c:     	b	0x100005794 <_main+0xc4>
100005770:     	add	x8, x21, x20
100005774:     	mov	w9, #0x5                ; =5
100005778:     	mov	w10, #0x7               ; =7
10000577c:     	mov	w11, #0x63              ; =99
100005780:     	cmp	x21, x0
100005784:     	csel	x10, x11, x10, eq
100005788:     	add	x11, x0, x19
10000578c:     	cmp	x8, x11
100005790:     	csel	x0, x9, x10, eq
100005794:     	bl	0x1000006f8 <__bril_print_int>
100005798:     	bl	0x100000990 <__bril_print_end>
10000579c:     	mov	w0, #0x0                ; =0
1000057a0:     	ldp	x29, x30, [sp, #0x30]
1000057a4:     	ldp	x20, x19, [sp, #0x20]
1000057a8:     	ldp	x22, x21, [sp, #0x10]
1000057ac:     	ldp	x24, x23, [sp], #0x40
1000057b0:     	ret

