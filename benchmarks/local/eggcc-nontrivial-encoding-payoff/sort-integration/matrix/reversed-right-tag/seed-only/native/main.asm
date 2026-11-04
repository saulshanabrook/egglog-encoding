0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x2, x3
100005658:     	csel	x8, x2, x3, lt
10000565c:     	csel	x9, x2, x3, gt
100005660:     	cmp	x0, x1
100005664:     	csel	x10, x0, x1, lt
100005668:     	csel	x11, x0, x1, gt
10000566c:     	cset	w12, lt
100005670:     	cmp	x3, x2
100005674:     	cset	w13, ge
100005678:     	eor	w12, w12, w13
10000567c:     	mov	w13, #0x3               ; =3
100005680:     	add	x14, x4, x2
100005684:     	mov	w15, #0x7               ; =7
100005688:     	mov	w16, #0x63              ; =99
10000568c:     	cmp	x4, x5
100005690:     	csel	x15, x16, x15, eq
100005694:     	mov	w16, #0x5               ; =5
100005698:     	add	x17, x5, x0
10000569c:     	cmp	x14, x17
1000056a0:     	csel	x14, x16, x15, eq
1000056a4:     	cmp	w12, #0x0
1000056a8:     	csel	x12, x13, x14, eq
1000056ac:     	cmp	x9, x11
1000056b0:     	csel	x9, x13, x12, ne
1000056b4:     	cmp	x10, x8
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
100005720:     	cmp	x20, x24
100005724:     	csel	x8, x20, x24, lt
100005728:     	csel	x9, x20, x24, gt
10000572c:     	cmp	x19, x23
100005730:     	csel	x10, x19, x23, lt
100005734:     	csel	x11, x19, x23, gt
100005738:     	cset	w12, lt
10000573c:     	cmp	x24, x20
100005740:     	cset	w13, ge
100005744:     	cmp	w12, w13
100005748:     	ccmp	x10, x8, #0x0, ne
10000574c:     	ccmp	x9, x11, #0x0, eq
100005750:     	b.eq	0x10000575c <_main+0x94>
100005754:     	mov	w0, #0x3                ; =3
100005758:     	b	0x100005780 <_main+0xb8>
10000575c:     	add	x8, x21, x20
100005760:     	mov	w9, #0x5                ; =5
100005764:     	mov	w10, #0x7               ; =7
100005768:     	mov	w11, #0x63              ; =99
10000576c:     	cmp	x21, x0
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

