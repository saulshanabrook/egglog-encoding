0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	cmp	x0, x1
100005658:     	csel	x8, x0, x1, lt
10000565c:     	csel	x9, x0, x1, gt
100005660:     	cmp	x2, x3
100005664:     	csel	x10, x2, x3, lt
100005668:     	csel	x11, x2, x3, gt
10000566c:     	mov	w12, #0x3               ; =3
100005670:     	add	x13, x4, x2
100005674:     	mov	w14, #0x7               ; =7
100005678:     	mov	w15, #0x63              ; =99
10000567c:     	cmp	x4, x5
100005680:     	csel	x14, x15, x14, eq
100005684:     	mov	w15, #0x5               ; =5
100005688:     	add	x16, x5, x0
10000568c:     	cmp	x13, x16
100005690:     	csel	x13, x15, x14, eq
100005694:     	cmp	x9, x11
100005698:     	csel	x9, x13, x12, eq
10000569c:     	cmp	x8, x10
1000056a0:     	csel	x0, x12, x9, ne
1000056a4:     	bl	0x1000006f8 <__bril_print_int>
1000056a8:     	ldp	x29, x30, [sp], #0x10
1000056ac:     	b	0x100000990 <__bril_print_end>


00000001000056b0 <_main>:
1000056b0:     	stp	x24, x23, [sp, #-0x40]!
1000056b4:     	stp	x22, x21, [sp, #0x10]
1000056b8:     	stp	x20, x19, [sp, #0x20]
1000056bc:     	stp	x29, x30, [sp, #0x30]
1000056c0:     	mov	x22, x1
1000056c4:     	ldr	x0, [x1, #0x8]
1000056c8:     	bl	0x1000009a4 <__bril_parse_int>
1000056cc:     	mov	x19, x0
1000056d0:     	ldr	x0, [x22, #0x10]
1000056d4:     	bl	0x1000009a4 <__bril_parse_int>
1000056d8:     	mov	x23, x0
1000056dc:     	ldr	x0, [x22, #0x18]
1000056e0:     	bl	0x1000009a4 <__bril_parse_int>
1000056e4:     	mov	x20, x0
1000056e8:     	ldr	x0, [x22, #0x20]
1000056ec:     	bl	0x1000009a4 <__bril_parse_int>
1000056f0:     	mov	x24, x0
1000056f4:     	ldr	x0, [x22, #0x28]
1000056f8:     	bl	0x1000009a4 <__bril_parse_int>
1000056fc:     	mov	x21, x0
100005700:     	ldr	x0, [x22, #0x30]
100005704:     	bl	0x1000009a4 <__bril_parse_int>
100005708:     	cmp	x19, x23
10000570c:     	csel	x8, x19, x23, lt
100005710:     	csel	x9, x19, x23, gt
100005714:     	cmp	x20, x24
100005718:     	csel	x10, x20, x24, lt
10000571c:     	csel	x11, x20, x24, gt
100005720:     	cmp	x8, x10
100005724:     	ccmp	x9, x11, #0x0, eq
100005728:     	b.eq	0x100005734 <_main+0x84>
10000572c:     	mov	w0, #0x3                ; =3
100005730:     	b	0x100005758 <_main+0xa8>
100005734:     	add	x8, x21, x20
100005738:     	mov	w9, #0x5                ; =5
10000573c:     	mov	w10, #0x7               ; =7
100005740:     	mov	w11, #0x63              ; =99
100005744:     	cmp	x21, x0
100005748:     	csel	x10, x11, x10, eq
10000574c:     	add	x11, x0, x19
100005750:     	cmp	x8, x11
100005754:     	csel	x0, x9, x10, eq
100005758:     	bl	0x1000006f8 <__bril_print_int>
10000575c:     	bl	0x100000990 <__bril_print_end>
100005760:     	mov	w0, #0x0                ; =0
100005764:     	ldp	x29, x30, [sp, #0x30]
100005768:     	ldp	x20, x19, [sp, #0x20]
10000576c:     	ldp	x22, x21, [sp, #0x10]
100005770:     	ldp	x24, x23, [sp], #0x40
100005774:     	ret

