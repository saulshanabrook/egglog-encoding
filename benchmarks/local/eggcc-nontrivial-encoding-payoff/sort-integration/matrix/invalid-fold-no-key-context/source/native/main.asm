0000000100005650 <__main>:
100005650:     	stp	x29, x30, [sp, #-0x10]!
100005654:     	add	x8, x4, x2
100005658:     	add	x9, x5, x0
10000565c:     	cmp	x8, x9
100005660:     	mov	w8, #0x7                ; =7
100005664:     	mov	w9, #0x5                ; =5
100005668:     	csel	x0, x9, x8, eq
10000566c:     	bl	0x1000006f8 <__bril_print_int>
100005670:     	ldp	x29, x30, [sp], #0x10
100005674:     	b	0x100000990 <__bril_print_end>


0000000100005678 <_main>:
100005678:     	stp	x22, x21, [sp, #-0x30]!
10000567c:     	stp	x20, x19, [sp, #0x10]
100005680:     	stp	x29, x30, [sp, #0x20]
100005684:     	mov	x19, x1
100005688:     	ldr	x0, [x1, #0x8]
10000568c:     	bl	0x1000009a4 <__bril_parse_int>
100005690:     	mov	x20, x0
100005694:     	ldr	x0, [x19, #0x10]
100005698:     	bl	0x1000009a4 <__bril_parse_int>
10000569c:     	ldr	x0, [x19, #0x18]
1000056a0:     	bl	0x1000009a4 <__bril_parse_int>
1000056a4:     	mov	x21, x0
1000056a8:     	ldr	x0, [x19, #0x20]
1000056ac:     	bl	0x1000009a4 <__bril_parse_int>
1000056b0:     	ldr	x0, [x19, #0x28]
1000056b4:     	bl	0x1000009a4 <__bril_parse_int>
1000056b8:     	mov	x22, x0
1000056bc:     	ldr	x0, [x19, #0x30]
1000056c0:     	bl	0x1000009a4 <__bril_parse_int>
1000056c4:     	add	x8, x22, x21
1000056c8:     	add	x9, x0, x20
1000056cc:     	cmp	x8, x9
1000056d0:     	mov	w8, #0x7                ; =7
1000056d4:     	mov	w9, #0x5                ; =5
1000056d8:     	csel	x0, x9, x8, eq
1000056dc:     	bl	0x1000006f8 <__bril_print_int>
1000056e0:     	bl	0x100000990 <__bril_print_end>
1000056e4:     	mov	w0, #0x0                ; =0
1000056e8:     	ldp	x29, x30, [sp, #0x20]
1000056ec:     	ldp	x20, x19, [sp, #0x10]
1000056f0:     	ldp	x22, x21, [sp], #0x30
1000056f4:     	ret

