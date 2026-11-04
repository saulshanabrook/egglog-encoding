0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	add	x8, x4, x2
100005658:     	mov	w9, #0x7                ; =7
10000565c:     	mov	w10, #0x63              ; =99
100005660:     	cmp	x4, x5
100005664:     	csel	x9, x10, x9, eq
100005668:     	add	x10, x5, x0
10000566c:     	cmp	x8, x10
100005670:     	mov	w8, #0x5                ; =5
100005674:     	csel	x0, x8, x9, eq
100005678:     	bl	0x1000006f8 <__bril_print_int>
10000567c:     	ldp	x29, x30, [sp], #0x10
100005680:     	b	0x100000990 <__bril_print_end>


0000000100005684 <_main>:
100005684:     	stp	x22, x21, [sp, #-0x30]!
100005688:     	stp	x20, x19, [sp, #0x10]
10000568c:     	stp	x29, x30, [sp, #0x20]
100005690:     	mov	x19, x1
100005694:     	ldr	x0, [x1, #0x8]
100005698:     	bl	0x1000009a4 <__bril_parse_int>
10000569c:     	mov	x20, x0
1000056a0:     	ldr	x0, [x19, #0x10]
1000056a4:     	bl	0x1000009a4 <__bril_parse_int>
1000056a8:     	ldr	x0, [x19, #0x18]
1000056ac:     	bl	0x1000009a4 <__bril_parse_int>
1000056b0:     	mov	x21, x0
1000056b4:     	ldr	x0, [x19, #0x20]
1000056b8:     	bl	0x1000009a4 <__bril_parse_int>
1000056bc:     	ldr	x0, [x19, #0x28]
1000056c0:     	bl	0x1000009a4 <__bril_parse_int>
1000056c4:     	mov	x22, x0
1000056c8:     	ldr	x0, [x19, #0x30]
1000056cc:     	bl	0x1000009a4 <__bril_parse_int>
1000056d0:     	add	x8, x22, x21
1000056d4:     	mov	w9, #0x7                ; =7
1000056d8:     	mov	w10, #0x63              ; =99
1000056dc:     	cmp	x22, x0
1000056e0:     	csel	x9, x10, x9, eq
1000056e4:     	add	x10, x0, x20
1000056e8:     	cmp	x8, x10
1000056ec:     	mov	w8, #0x5                ; =5
1000056f0:     	csel	x0, x8, x9, eq
1000056f4:     	bl	0x1000006f8 <__bril_print_int>
1000056f8:     	bl	0x100000990 <__bril_print_end>
1000056fc:     	mov	w0, #0x0                ; =0
100005700:     	ldp	x29, x30, [sp, #0x20]
100005704:     	ldp	x20, x19, [sp, #0x10]
100005708:     	ldp	x22, x21, [sp], #0x30
10000570c:     	ret

