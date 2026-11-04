0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, gt
10000565c:     	cset	w9, lt
100005660:     	cmp	x2, x3
100005664:     	csel	x10, x2, x3, gt
100005668:     	cset	w11, ge
10000566c:     	eor	w9, w9, w11
100005670:     	mov	w11, #0x3               ; =3
100005674:     	add	x12, x4, x2
100005678:     	mov	w13, #0x7               ; =7
10000567c:     	mov	w14, #0x63              ; =99
100005680:     	cmp	x4, x5
100005684:     	csel	x13, x14, x13, eq
100005688:     	mov	w14, #0x5               ; =5
10000568c:     	add	x15, x5, x0
100005690:     	cmp	x12, x15
100005694:     	csel	x12, x14, x13, eq
100005698:     	tst	w9, #0x1
10000569c:     	csel	x9, x12, x11, ne
1000056a0:     	cmp	x8, x10
1000056a4:     	csel	x0, x11, x9, ne
1000056a8:     	bl	0x1000006f8 <__bril_print_int>
1000056ac:     	ldp	x29, x30, [sp], #0x10
1000056b0:     	b	0x100000990 <__bril_print_end>


00000001000056b4 <_main>:
1000056b4:     	stp	x24, x23, [sp, #-0x40]!
1000056b8:     	stp	x22, x21, [sp, #0x10]
1000056bc:     	stp	x20, x19, [sp, #0x20]
1000056c0:     	stp	x29, x30, [sp, #0x30]
1000056c4:     	mov	x22, x1
1000056c8:     	ldr	x0, [x1, #0x8]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	mov	x19, x0
1000056d4:     	ldr	x0, [x22, #0x10]
1000056d8:     	bl	0x1000009a4 <__bril_parse_int>
1000056dc:     	mov	x23, x0
1000056e0:     	ldr	x0, [x22, #0x18]
1000056e4:     	bl	0x1000009a4 <__bril_parse_int>
1000056e8:     	mov	x20, x0
1000056ec:     	ldr	x0, [x22, #0x20]
1000056f0:     	bl	0x1000009a4 <__bril_parse_int>
1000056f4:     	mov	x24, x0
1000056f8:     	ldr	x0, [x22, #0x28]
1000056fc:     	bl	0x1000009a4 <__bril_parse_int>
100005700:     	mov	x21, x0
100005704:     	ldr	x0, [x22, #0x30]
100005708:     	bl	0x1000009a4 <__bril_parse_int>
10000570c:     	cmp	x19, x23
100005710:     	csel	x8, x19, x23, gt
100005714:     	cset	w9, lt
100005718:     	cmp	x20, x24
10000571c:     	csel	x10, x20, x24, gt
100005720:     	cset	w11, ge
100005724:     	eor	w9, w9, w11
100005728:     	cmp	x8, x10
10000572c:     	ccmp	w9, #0x0, #0x4, eq
100005730:     	b.ne	0x10000573c <_main+0x88>
100005734:     	mov	w0, #0x3                ; =3
100005738:     	b	0x100005760 <_main+0xac>
10000573c:     	add	x8, x21, x20
100005740:     	mov	w9, #0x5                ; =5
100005744:     	mov	w10, #0x7               ; =7
100005748:     	mov	w11, #0x63              ; =99
10000574c:     	cmp	x21, x0
100005750:     	csel	x10, x11, x10, eq
100005754:     	add	x11, x0, x19
100005758:     	cmp	x8, x11
10000575c:     	csel	x0, x9, x10, eq
100005760:     	bl	0x1000006f8 <__bril_print_int>
100005764:     	bl	0x100000990 <__bril_print_end>
100005768:     	mov	w0, #0x0                ; =0
10000576c:     	ldp	x29, x30, [sp, #0x30]
100005770:     	ldp	x20, x19, [sp, #0x20]
100005774:     	ldp	x22, x21, [sp, #0x10]
100005778:     	ldp	x24, x23, [sp], #0x40
10000577c:     	ret

