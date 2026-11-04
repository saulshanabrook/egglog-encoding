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
100005680:     	mov	w15, #0x7               ; =7
100005684:     	mov	w16, #0x63              ; =99
100005688:     	cmp	x4, x5
10000568c:     	csel	x15, x16, x15, eq
100005690:     	mov	w16, #0x5               ; =5
100005694:     	add	x17, x5, x0
100005698:     	cmp	x14, x17
10000569c:     	csel	x14, x16, x15, eq
1000056a0:     	tst	w10, #0x1
1000056a4:     	csel	x10, x14, x13, ne
1000056a8:     	cmp	x9, x12
1000056ac:     	csel	x9, x13, x10, ne
1000056b0:     	cmp	x8, x11
1000056b4:     	csel	x0, x13, x9, ne
1000056b8:     	bl	0x1000006f8 <__bril_print_int>
1000056bc:     	ldp	x29, x30, [sp], #0x10
1000056c0:     	b	0x100000990 <__bril_print_end>


00000001000056c4 <_main>:
1000056c4:     	stp	x24, x23, [sp, #-0x40]!
1000056c8:     	stp	x22, x21, [sp, #0x10]
1000056cc:     	stp	x20, x19, [sp, #0x20]
1000056d0:     	stp	x29, x30, [sp, #0x30]
1000056d4:     	mov	x22, x1
1000056d8:     	ldr	x0, [x1, #0x8]
1000056dc:     	bl	0x1000009a4 <__bril_parse_int>
1000056e0:     	mov	x19, x0
1000056e4:     	ldr	x0, [x22, #0x10]
1000056e8:     	bl	0x1000009a4 <__bril_parse_int>
1000056ec:     	mov	x23, x0
1000056f0:     	ldr	x0, [x22, #0x18]
1000056f4:     	bl	0x1000009a4 <__bril_parse_int>
1000056f8:     	mov	x20, x0
1000056fc:     	ldr	x0, [x22, #0x20]
100005700:     	bl	0x1000009a4 <__bril_parse_int>
100005704:     	mov	x24, x0
100005708:     	ldr	x0, [x22, #0x28]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	mov	x21, x0
100005714:     	ldr	x0, [x22, #0x30]
100005718:     	bl	0x1000009a4 <__bril_parse_int>
10000571c:     	cmp	x19, x23
100005720:     	csel	x8, x19, x23, lt
100005724:     	csel	x9, x19, x23, gt
100005728:     	cset	w10, lt
10000572c:     	cmp	x20, x24
100005730:     	csel	x11, x20, x24, lt
100005734:     	csel	x12, x20, x24, gt
100005738:     	cset	w13, ge
10000573c:     	cmp	w10, w13
100005740:     	ccmp	x8, x11, #0x0, ne
100005744:     	ccmp	x9, x12, #0x0, eq
100005748:     	b.eq	0x100005754 <_main+0x90>
10000574c:     	mov	w0, #0x3                ; =3
100005750:     	b	0x100005778 <_main+0xb4>
100005754:     	add	x8, x21, x20
100005758:     	mov	w9, #0x5                ; =5
10000575c:     	mov	w10, #0x7               ; =7
100005760:     	mov	w11, #0x63              ; =99
100005764:     	cmp	x21, x0
100005768:     	csel	x10, x11, x10, eq
10000576c:     	add	x11, x0, x19
100005770:     	cmp	x8, x11
100005774:     	csel	x0, x9, x10, eq
100005778:     	bl	0x1000006f8 <__bril_print_int>
10000577c:     	bl	0x100000990 <__bril_print_end>
100005780:     	mov	w0, #0x0                ; =0
100005784:     	ldp	x29, x30, [sp, #0x30]
100005788:     	ldp	x20, x19, [sp, #0x20]
10000578c:     	ldp	x22, x21, [sp, #0x10]
100005790:     	ldp	x24, x23, [sp], #0x40
100005794:     	ret

