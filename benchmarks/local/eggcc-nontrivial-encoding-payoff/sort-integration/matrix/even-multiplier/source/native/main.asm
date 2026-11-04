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
100005674:     	eor	w10, w10, w13
100005678:     	mov	w13, #0x3               ; =3
10000567c:     	add	x14, x4, x2
100005680:     	eor	x15, x5, x4
100005684:     	tst	x15, #0x7fffffffffffffff
100005688:     	mov	w15, #0x7               ; =7
10000568c:     	mov	w16, #0x63              ; =99
100005690:     	csel	x15, x16, x15, eq
100005694:     	mov	w16, #0x5               ; =5
100005698:     	add	x17, x5, x0
10000569c:     	cmp	x14, x17
1000056a0:     	csel	x14, x16, x15, eq
1000056a4:     	tst	w10, #0x1
1000056a8:     	csel	x10, x14, x13, ne
1000056ac:     	cmp	x9, x12
1000056b0:     	csel	x9, x13, x10, ne
1000056b4:     	cmp	x8, x11
1000056b8:     	csel	x0, x13, x9, ne
1000056bc:     	bl	0x1000006f8 <__bril_print_int>
1000056c0:     	ldp	x29, x30, [sp], #0x10
1000056c4:     	b	0x100000990 <__bril_print_end>


00000001000056c8 <_main>:
1000056c8:     	stp	x24, x23, [sp, #-0x40]!
1000056cc:     	stp	x22, x21, [sp, #0x10]
1000056d0:     	stp	x20, x19, [sp, #0x20]
1000056d4:     	stp	x29, x30, [sp, #0x30]
1000056d8:     	mov	x22, x1
1000056dc:     	ldr	x0, [x1, #0x8]
1000056e0:     	bl	0x1000009a4 <__bril_parse_int>
1000056e4:     	mov	x19, x0
1000056e8:     	ldr	x0, [x22, #0x10]
1000056ec:     	bl	0x1000009a4 <__bril_parse_int>
1000056f0:     	mov	x23, x0
1000056f4:     	ldr	x0, [x22, #0x18]
1000056f8:     	bl	0x1000009a4 <__bril_parse_int>
1000056fc:     	mov	x20, x0
100005700:     	ldr	x0, [x22, #0x20]
100005704:     	bl	0x1000009a4 <__bril_parse_int>
100005708:     	mov	x24, x0
10000570c:     	ldr	x0, [x22, #0x28]
100005710:     	bl	0x1000009a4 <__bril_parse_int>
100005714:     	mov	x21, x0
100005718:     	ldr	x0, [x22, #0x30]
10000571c:     	bl	0x1000009a4 <__bril_parse_int>
100005720:     	cmp	x19, x23
100005724:     	csel	x8, x19, x23, lt
100005728:     	csel	x9, x19, x23, gt
10000572c:     	cset	w10, lt
100005730:     	cmp	x20, x24
100005734:     	csel	x11, x20, x24, lt
100005738:     	csel	x12, x20, x24, gt
10000573c:     	cset	w13, ge
100005740:     	cmp	w10, w13
100005744:     	ccmp	x8, x11, #0x0, ne
100005748:     	ccmp	x9, x12, #0x0, eq
10000574c:     	b.eq	0x100005758 <_main+0x90>
100005750:     	mov	w0, #0x3                ; =3
100005754:     	b	0x100005780 <_main+0xb8>
100005758:     	add	x8, x21, x20
10000575c:     	mov	w9, #0x5                ; =5
100005760:     	eor	x10, x0, x21
100005764:     	tst	x10, #0x7fffffffffffffff
100005768:     	mov	w10, #0x7               ; =7
10000576c:     	mov	w11, #0x63              ; =99
100005770:     	csel	x10, x11, x10, eq
100005774:     	add	x11, x0, x19
100005778:     	cmp	x8, x11
10000577c:     	csel	x0, x9, x10, eq
100005780:     	bl	0x1000006f8 <__bril_print_int>
100005784:     	bl	0x100000990 <__bril_print_end>
100005788:     	mov	w0, #0x0                ; =0
10000578c:     	ldp	x29, x30, [sp, #0x30]
100005790:     	ldp	x20, x19, [sp, #0x20]
100005794:     	ldp	x22, x21, [sp, #0x10]
100005798:     	ldp	x24, x23, [sp], #0x40
10000579c:     	ret

