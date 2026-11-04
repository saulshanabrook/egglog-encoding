
/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-reviewed/matrix/wrong-divisor/off/native/program:	file format mach-o arm64

Disassembly of section __TEXT,__text:

0000000100000500 <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE>:
100000500:     	sub	sp, sp, #0x40
100000504:     	stp	x22, x21, [sp, #0x10]
100000508:     	stp	x20, x19, [sp, #0x20]
10000050c:     	stp	x29, x30, [sp, #0x30]
100000510:     	add	x29, sp, #0x30
100000514:     	str	wzr, [sp, #0xc]
100000518:     	cmp	w1, #0x80
10000051c:     	b.hs	0x10000052c <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0x2c>
100000520:     	strb	w1, [sp, #0xc]
100000524:     	mov	w20, #0x1               ; =1
100000528:     	b	0x1000005bc <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0xbc>
10000052c:     	cmp	w1, #0x800
100000530:     	b.hs	0x100000554 <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0x54>
100000534:     	lsr	w8, w1, #6
100000538:     	orr	w8, w8, #0xc0
10000053c:     	strb	w8, [sp, #0xc]
100000540:     	mov	w8, #0x80               ; =128
100000544:     	bfxil	w8, w1, #0, #6
100000548:     	strb	w8, [sp, #0xd]
10000054c:     	mov	w20, #0x2               ; =2
100000550:     	b	0x1000005bc <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0xbc>
100000554:     	cmp	w1, #0x10, lsl #12      ; =0x10000
100000558:     	b.hs	0x100000588 <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0x88>
10000055c:     	lsr	w8, w1, #12
100000560:     	orr	w8, w8, #0xe0
100000564:     	strb	w8, [sp, #0xc]
100000568:     	mov	w8, #0x80               ; =128
10000056c:     	mov	w9, #0x80               ; =128
100000570:     	bfxil	w9, w1, #6, #6
100000574:     	strb	w9, [sp, #0xd]
100000578:     	bfxil	w8, w1, #0, #6
10000057c:     	strb	w8, [sp, #0xe]
100000580:     	mov	w20, #0x3               ; =3
100000584:     	b	0x1000005bc <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0xbc>
100000588:     	mov	w8, #0xf0               ; =240
10000058c:     	bfxil	w8, w1, #18, #3
100000590:     	strb	w8, [sp, #0xc]
100000594:     	mov	w8, #0x80               ; =128
100000598:     	mov	w9, #0x80               ; =128
10000059c:     	bfxil	w9, w1, #12, #6
1000005a0:     	strb	w9, [sp, #0xd]
1000005a4:     	mov	w9, #0x80               ; =128
1000005a8:     	bfxil	w9, w1, #6, #6
1000005ac:     	strb	w9, [sp, #0xe]
1000005b0:     	bfxil	w8, w1, #0, #6
1000005b4:     	strb	w8, [sp, #0xf]
1000005b8:     	mov	w20, #0x4               ; =4
1000005bc:     	mov	x21, #0x0               ; =0
1000005c0:     	ldr	w19, [x0]
1000005c4:     	add	x22, sp, #0xc
1000005c8:     	sub	x2, x20, x21
1000005cc:     	add	x1, x22, x21
1000005d0:     	mov	x0, x19
1000005d4:     	bl	0x100005864 <_write+0x100005864>
1000005d8:     	add	x21, x0, x21
1000005dc:     	cmp	x0, #0x1
1000005e0:     	ccmp	x21, x20, #0x2, ge
1000005e4:     	b.lo	0x1000005c8 <__ZN4core3fmt5Write10write_char17h8c585c872c0483bcE+0xc8>
1000005e8:     	mov	w0, #0x0                ; =0
1000005ec:     	ldp	x29, x30, [sp, #0x30]
1000005f0:     	ldp	x20, x19, [sp, #0x20]
1000005f4:     	ldp	x22, x21, [sp, #0x10]
1000005f8:     	add	sp, sp, #0x40
1000005fc:     	ret

0000000100000600 <__ZN4core3fmt5Write9write_fmt17he7bf56288f0df65cE>:
100000600:     	mov	x2, x1
100000604:     	adrp	x1, 0x10000c000 <_write+0x10000c000>
100000608:     	add	x1, x1, #0x28
10000060c:     	b	0x1000014b8 <__ZN4core3fmt5write17h2595086b0d4e920fE>

0000000100000610 <__ZN4core3ptr45drop_in_place$LT$libc_print..__LibCWriter$GT$17h80065d73c2fe05b4E>:
100000610:     	ret

0000000100000614 <__ZN61_$LT$libc_print..__LibCWriter$u20$as$u20$core..fmt..Write$GT$9write_str17h40c8cbc3ffde91e2E>:
100000614:     	cbz	x2, 0x100000664 <__ZN61_$LT$libc_print..__LibCWriter$u20$as$u20$core..fmt..Write$GT$9write_str17h40c8cbc3ffde91e2E+0x50>
100000618:     	stp	x22, x21, [sp, #-0x30]!
10000061c:     	stp	x20, x19, [sp, #0x10]
100000620:     	stp	x29, x30, [sp, #0x20]
100000624:     	add	x29, sp, #0x20
100000628:     	mov	x19, x2
10000062c:     	mov	x20, x1
100000630:     	mov	x22, #0x0               ; =0
100000634:     	ldr	w21, [x0]
100000638:     	sub	x2, x19, x22
10000063c:     	add	x1, x20, x22
100000640:     	mov	x0, x21
100000644:     	bl	0x100005864 <_write+0x100005864>
100000648:     	add	x22, x0, x22
10000064c:     	cmp	x0, #0x1
100000650:     	ccmp	x22, x19, #0x2, ge
100000654:     	b.lo	0x100000638 <__ZN61_$LT$libc_print..__LibCWriter$u20$as$u20$core..fmt..Write$GT$9write_str17h40c8cbc3ffde91e2E+0x24>
100000658:     	ldp	x29, x30, [sp, #0x20]
10000065c:     	ldp	x20, x19, [sp, #0x10]
100000660:     	ldp	x22, x21, [sp], #0x30
100000664:     	mov	w0, #0x0                ; =0
100000668:     	ret

000000010000066c <__bril_get_ticks>:
10000066c:     	stp	x29, x30, [sp, #-0x10]!
100000670:     	mov	x29, sp
100000674:     	mrs	x0, CNTVCT_EL0
100000678:     	ldp	x29, x30, [sp], #0x10
10000067c:     	ret

0000000100000680 <__bril_eprintln_unsigned_int>:
100000680:     	sub	sp, sp, #0x60
100000684:     	stp	x29, x30, [sp, #0x50]
100000688:     	add	x29, sp, #0x50
10000068c:     	str	x0, [sp]
100000690:     	mov	w8, #0x2                ; =2
100000694:     	str	w8, [sp, #0xc]
100000698:     	adrp	x8, 0x100000000 <_write+0x100000000>
10000069c:     	add	x8, x8, #0xef4
1000006a0:     	mov	x9, sp
1000006a4:     	stp	x9, x8, [x29, #-0x10]
1000006a8:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000006ac:     	add	x8, x8, #0x880
1000006b0:     	mov	w9, #0x1                ; =1
1000006b4:     	stp	x8, x9, [sp, #0x10]
1000006b8:     	stp	x9, xzr, [sp, #0x28]
1000006bc:     	sub	x8, x29, #0x10
1000006c0:     	str	x8, [sp, #0x20]
1000006c4:     	adrp	x1, 0x10000c000 <_write+0x10000c000>
1000006c8:     	add	x1, x1, #0x28
1000006cc:     	add	x0, sp, #0xc
1000006d0:     	add	x2, sp, #0x10
1000006d4:     	bl	0x1000014b8 <__ZN4core3fmt5write17h2595086b0d4e920fE>
1000006d8:     	ldr	w0, [sp, #0xc]
1000006dc:     	adrp	x1, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000006e0:     	add	x1, x1, #0x8b5
1000006e4:     	mov	w2, #0x1                ; =1
1000006e8:     	bl	0x100005864 <_write+0x100005864>
1000006ec:     	ldp	x29, x30, [sp, #0x50]
1000006f0:     	add	sp, sp, #0x60
1000006f4:     	ret

00000001000006f8 <__bril_print_int>:
1000006f8:     	sub	sp, sp, #0x60
1000006fc:     	stp	x29, x30, [sp, #0x50]
100000700:     	add	x29, sp, #0x50
100000704:     	str	x0, [sp]
100000708:     	mov	w8, #0x1                ; =1
10000070c:     	str	w8, [sp, #0xc]
100000710:     	mov	x9, sp
100000714:     	adrp	x10, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000718:     	add	x10, x10, #0x504
10000071c:     	stp	x9, x10, [x29, #-0x10]
100000720:     	adrp	x9, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000724:     	add	x9, x9, #0x880
100000728:     	stp	x9, x8, [sp, #0x10]
10000072c:     	stp	x8, xzr, [sp, #0x28]
100000730:     	sub	x9, x29, #0x10
100000734:     	str	x9, [sp, #0x20]
100000738:     	adrp	x1, 0x10000c000 <_write+0x10000c000>
10000073c:     	add	x1, x1, #0x28
100000740:     	add	x0, sp, #0xc
100000744:     	add	x2, sp, #0x10
100000748:     	bl	0x1000014b8 <__ZN4core3fmt5write17h2595086b0d4e920fE>
10000074c:     	ldp	x29, x30, [sp, #0x50]
100000750:     	add	sp, sp, #0x60
100000754:     	ret

0000000100000758 <__bril_print_bool>:
100000758:     	stp	x22, x21, [sp, #-0x30]!
10000075c:     	stp	x20, x19, [sp, #0x10]
100000760:     	stp	x29, x30, [sp, #0x20]
100000764:     	add	x29, sp, #0x20
100000768:     	mov	x19, #0x0               ; =0
10000076c:     	tbz	w0, #0x0, 0x1000007a0 <__bril_print_bool+0x48>
100000770:     	mov	w20, #0x4               ; =4
100000774:     	adrp	x21, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000778:     	add	x21, x21, #0x8a8
10000077c:     	sub	x2, x20, x19
100000780:     	add	x1, x21, x19
100000784:     	mov	w0, #0x1                ; =1
100000788:     	bl	0x100005864 <_write+0x100005864>
10000078c:     	add	x19, x0, x19
100000790:     	cmp	x0, #0x1
100000794:     	ccmp	x19, #0x4, #0x2, ge
100000798:     	b.lo	0x10000077c <__bril_print_bool+0x24>
10000079c:     	b	0x1000007cc <__bril_print_bool+0x74>
1000007a0:     	mov	w20, #0x5               ; =5
1000007a4:     	adrp	x21, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000007a8:     	add	x21, x21, #0x8b0
1000007ac:     	sub	x2, x20, x19
1000007b0:     	add	x1, x21, x19
1000007b4:     	mov	w0, #0x1                ; =1
1000007b8:     	bl	0x100005864 <_write+0x100005864>
1000007bc:     	add	x19, x0, x19
1000007c0:     	cmp	x0, #0x1
1000007c4:     	ccmp	x19, #0x5, #0x2, ge
1000007c8:     	b.lo	0x1000007ac <__bril_print_bool+0x54>
1000007cc:     	ldp	x29, x30, [sp, #0x20]
1000007d0:     	ldp	x20, x19, [sp, #0x10]
1000007d4:     	ldp	x22, x21, [sp], #0x30
1000007d8:     	ret

00000001000007dc <__bril_print_float>:
1000007dc:     	sub	sp, sp, #0xc0
1000007e0:     	stp	x22, x21, [sp, #0x90]
1000007e4:     	stp	x20, x19, [sp, #0xa0]
1000007e8:     	stp	x29, x30, [sp, #0xb0]
1000007ec:     	add	x29, sp, #0xb0
1000007f0:     	str	d0, [sp]
1000007f4:     	fabs	d1, d0
1000007f8:     	mov	x8, #0x7ff0000000000000 ; =9218868437227405312
1000007fc:     	fmov	d2, x8
100000800:     	fcmp	d1, d2
100000804:     	b.ne	0x100000854 <__bril_print_float+0x78>
100000808:     	mov	x19, #0x0               ; =0
10000080c:     	fmov	x8, d0
100000810:     	tbnz	x8, #0x3f, 0x100000884 <__bril_print_float+0xa8>
100000814:     	mov	w20, #0x8               ; =8
100000818:     	adrp	x21, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
10000081c:     	add	x21, x21, #0x8a0
100000820:     	sub	x2, x20, x19
100000824:     	add	x1, x21, x19
100000828:     	mov	w0, #0x1                ; =1
10000082c:     	bl	0x100005864 <_write+0x100005864>
100000830:     	add	x19, x0, x19
100000834:     	cmp	x0, #0x1
100000838:     	ccmp	x19, #0x8, #0x2, ge
10000083c:     	b.lo	0x100000820 <__bril_print_float+0x44>
100000840:     	ldp	x29, x30, [sp, #0xb0]
100000844:     	ldp	x20, x19, [sp, #0xa0]
100000848:     	ldp	x22, x21, [sp, #0x90]
10000084c:     	add	sp, sp, #0xc0
100000850:     	ret
100000854:     	mov	w8, #0x1                ; =1
100000858:     	fcmp	d0, d0
10000085c:     	b.vs	0x100000938 <__bril_print_float+0x15c>
100000860:     	fcmp	d0, #0.0
100000864:     	b.ne	0x1000008b4 <__bril_print_float+0xd8>
100000868:     	adrp	x9, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
10000086c:     	add	x9, x9, #0x898
100000870:     	adrp	x10, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000874:     	add	x10, x10, #0x4c4
100000878:     	str	w8, [sp, #0xc]
10000087c:     	stp	x9, x10, [sp, #0x40]
100000880:     	b	0x1000008c8 <__bril_print_float+0xec>
100000884:     	mov	w20, #0x9               ; =9
100000888:     	adrp	x21, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
10000088c:     	add	x21, x21, #0x8b6
100000890:     	sub	x2, x20, x19
100000894:     	add	x1, x21, x19
100000898:     	mov	w0, #0x1                ; =1
10000089c:     	bl	0x100005864 <_write+0x100005864>
1000008a0:     	add	x19, x0, x19
1000008a4:     	cmp	x0, #0x1
1000008a8:     	ccmp	x19, #0x9, #0x2, ge
1000008ac:     	b.lo	0x100000890 <__bril_print_float+0xb4>
1000008b0:     	b	0x100000840 <__bril_print_float+0x64>
1000008b4:     	str	w8, [sp, #0xc]
1000008b8:     	adrp	x9, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000008bc:     	add	x9, x9, #0x4c4
1000008c0:     	mov	x10, sp
1000008c4:     	stp	x10, x9, [sp, #0x40]
1000008c8:     	adrp	x9, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000008cc:     	ldr	q0, [x9, #0x870]
1000008d0:     	str	q0, [sp, #0x50]
1000008d4:     	mov	w9, #0x2                ; =2
1000008d8:     	str	x9, [sp, #0x60]
1000008dc:     	str	xzr, [sp, #0x70]
1000008e0:     	adrp	x9, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000008e4:     	ldr	d0, [x9, #0x890]
1000008e8:     	str	d0, [sp, #0x78]
1000008ec:     	mov	w9, #0x3                ; =3
1000008f0:     	strb	w9, [sp, #0x80]
1000008f4:     	adrp	x9, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000008f8:     	add	x9, x9, #0x880
1000008fc:     	stp	x9, x8, [sp, #0x10]
100000900:     	add	x9, sp, #0x50
100000904:     	stp	x9, x8, [sp, #0x30]
100000908:     	add	x9, sp, #0x40
10000090c:     	stp	x9, x8, [sp, #0x20]
100000910:     	adrp	x1, 0x10000c000 <_write+0x10000c000>
100000914:     	add	x1, x1, #0x28
100000918:     	add	x0, sp, #0xc
10000091c:     	add	x2, sp, #0x10
100000920:     	bl	0x1000014b8 <__ZN4core3fmt5write17h2595086b0d4e920fE>
100000924:     	ldp	x29, x30, [sp, #0xb0]
100000928:     	ldp	x20, x19, [sp, #0xa0]
10000092c:     	ldp	x22, x21, [sp, #0x90]
100000930:     	add	sp, sp, #0xc0
100000934:     	ret
100000938:     	str	w8, [sp, #0x10]
10000093c:     	adrp	x9, 0x10000c000 <_write+0x10000c000>
100000940:     	add	x9, x9, #0x58
100000944:     	stp	x9, x8, [sp, #0x50]
100000948:     	mov	w8, #0x8                ; =8
10000094c:     	stp	xzr, xzr, [sp, #0x68]
100000950:     	str	x8, [sp, #0x60]
100000954:     	adrp	x1, 0x10000c000 <_write+0x10000c000>
100000958:     	add	x1, x1, #0x28
10000095c:     	add	x0, sp, #0x10
100000960:     	add	x2, sp, #0x50
100000964:     	bl	0x1000014b8 <__ZN4core3fmt5write17h2595086b0d4e920fE>
100000968:     	ldp	x29, x30, [sp, #0xb0]
10000096c:     	ldp	x20, x19, [sp, #0xa0]
100000970:     	ldp	x22, x21, [sp, #0x90]
100000974:     	add	sp, sp, #0xc0
100000978:     	ret

000000010000097c <__bril_print_sep>:
10000097c:     	adrp	x1, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000980:     	add	x1, x1, #0x8bf
100000984:     	mov	w0, #0x1                ; =1
100000988:     	mov	w2, #0x1                ; =1
10000098c:     	b	0x100005864 <_write+0x100005864>

0000000100000990 <__bril_print_end>:
100000990:     	adrp	x1, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000994:     	add	x1, x1, #0x8b5
100000998:     	mov	w0, #0x1                ; =1
10000099c:     	mov	w2, #0x1                ; =1
1000009a0:     	b	0x100005864 <_write+0x100005864>

00000001000009a4 <__bril_parse_int>:
1000009a4:     	sub	sp, sp, #0x40
1000009a8:     	stp	x20, x19, [sp, #0x20]
1000009ac:     	stp	x29, x30, [sp, #0x30]
1000009b0:     	add	x29, sp, #0x30
1000009b4:     	mov	x19, x0
1000009b8:     	bl	0x100005858 <_write+0x100005858>
1000009bc:     	mov	x8, x0
1000009c0:     	add	x0, sp, #0x8
1000009c4:     	add	x2, x8, #0x1
1000009c8:     	mov	x1, x19
1000009cc:     	bl	0x100001e04 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E>
1000009d0:     	ldr	x8, [sp, #0x8]
1000009d4:     	cbnz	x8, 0x100000b48 <__bril_parse_int+0x1a4>
1000009d8:     	ldp	x8, x9, [sp, #0x10]
1000009dc:     	subs	x10, x9, #0x1
1000009e0:     	b.eq	0x1000009f0 <__bril_parse_int+0x4c>
1000009e4:     	cbz	x9, 0x100000b48 <__bril_parse_int+0x1a4>
1000009e8:     	ldrb	w11, [x8]
1000009ec:     	b	0x100000a04 <__bril_parse_int+0x60>
1000009f0:     	ldrb	w11, [x8]
1000009f4:     	cmp	w11, #0x2b
1000009f8:     	b.eq	0x100000b48 <__bril_parse_int+0x1a4>
1000009fc:     	cmp	w11, #0x2d
100000a00:     	b.eq	0x100000b48 <__bril_parse_int+0x1a4>
100000a04:     	cmp	w11, #0x2d
100000a08:     	b.eq	0x100000a3c <__bril_parse_int+0x98>
100000a0c:     	cmp	w11, #0x2b
100000a10:     	b.ne	0x100000a88 <__bril_parse_int+0xe4>
100000a14:     	add	x8, x8, #0x1
100000a18:     	cmp	x9, #0x11
100000a1c:     	b.hs	0x100000ac0 <__bril_parse_int+0x11c>
100000a20:     	mov	x9, x10
100000a24:     	cbnz	x10, 0x100000a90 <__bril_parse_int+0xec>
100000a28:     	mov	x0, #0x0                ; =0
100000a2c:     	ldp	x29, x30, [sp, #0x30]
100000a30:     	ldp	x20, x19, [sp, #0x20]
100000a34:     	add	sp, sp, #0x40
100000a38:     	ret
100000a3c:     	add	x8, x8, #0x1
100000a40:     	cmp	x9, #0x11
100000a44:     	b.hs	0x100000b04 <__bril_parse_int+0x160>
100000a48:     	mov	x0, #0x0                ; =0
100000a4c:     	cbz	x10, 0x100000a78 <__bril_parse_int+0xd4>
100000a50:     	mov	w9, #0xa                ; =10
100000a54:     	ldrb	w11, [x8]
100000a58:     	sub	w11, w11, #0x30
100000a5c:     	cmp	w11, #0x9
100000a60:     	b.hi	0x100000b48 <__bril_parse_int+0x1a4>
100000a64:     	mul	x12, x0, x9
100000a68:     	add	x8, x8, #0x1
100000a6c:     	sub	x0, x12, w11, uxtw
100000a70:     	sub	x10, x10, #0x1
100000a74:     	cbnz	x10, 0x100000a54 <__bril_parse_int+0xb0>
100000a78:     	ldp	x29, x30, [sp, #0x30]
100000a7c:     	ldp	x20, x19, [sp, #0x20]
100000a80:     	add	sp, sp, #0x40
100000a84:     	ret
100000a88:     	cmp	x9, #0x10
100000a8c:     	b.hs	0x100000ac4 <__bril_parse_int+0x120>
100000a90:     	mov	x0, #0x0                ; =0
100000a94:     	mov	w10, #0xa               ; =10
100000a98:     	ldrb	w11, [x8]
100000a9c:     	sub	w11, w11, #0x30
100000aa0:     	cmp	w11, #0x9
100000aa4:     	b.hi	0x100000b48 <__bril_parse_int+0x1a4>
100000aa8:     	mul	x12, x0, x10
100000aac:     	add	x8, x8, #0x1
100000ab0:     	add	x0, x12, w11, uxtw
100000ab4:     	subs	x9, x9, #0x1
100000ab8:     	b.ne	0x100000a98 <__bril_parse_int+0xf4>
100000abc:     	b	0x100000a78 <__bril_parse_int+0xd4>
100000ac0:     	mov	x9, x10
100000ac4:     	mov	x0, #0x0                ; =0
100000ac8:     	mov	w10, #0xa               ; =10
100000acc:     	smulh	x12, x0, x10
100000ad0:     	add	x11, x0, x0, lsl #2
100000ad4:     	lsl	x11, x11, #1
100000ad8:     	cmp	x12, x11, asr #63
100000adc:     	b.ne	0x100000b48 <__bril_parse_int+0x1a4>
100000ae0:     	ldrb	w12, [x8], #0x1
100000ae4:     	sub	w12, w12, #0x30
100000ae8:     	cmp	w12, #0x9
100000aec:     	b.hi	0x100000b48 <__bril_parse_int+0x1a4>
100000af0:     	adds	x0, x11, w12, uxtw
100000af4:     	b.vs	0x100000b48 <__bril_parse_int+0x1a4>
100000af8:     	sub	x9, x9, #0x1
100000afc:     	cbnz	x9, 0x100000acc <__bril_parse_int+0x128>
100000b00:     	b	0x100000a78 <__bril_parse_int+0xd4>
100000b04:     	mov	x0, #0x0                ; =0
100000b08:     	mov	w9, #0xa                ; =10
100000b0c:     	smulh	x12, x0, x9
100000b10:     	add	x11, x0, x0, lsl #2
100000b14:     	lsl	x11, x11, #1
100000b18:     	cmp	x12, x11, asr #63
100000b1c:     	b.ne	0x100000b48 <__bril_parse_int+0x1a4>
100000b20:     	ldrb	w12, [x8]
100000b24:     	sub	w12, w12, #0x30
100000b28:     	cmp	w12, #0x9
100000b2c:     	b.hi	0x100000b48 <__bril_parse_int+0x1a4>
100000b30:     	subs	x0, x11, w12, uxtw
100000b34:     	b.vs	0x100000b48 <__bril_parse_int+0x1a4>
100000b38:     	add	x8, x8, #0x1
100000b3c:     	sub	x10, x10, #0x1
100000b40:     	cbnz	x10, 0x100000b0c <__bril_parse_int+0x168>
100000b44:     	b	0x100000a78 <__bril_parse_int+0xd4>
100000b48:     	bl	0x100005828 <__ZN4core6result13unwrap_failed17h172b8a6210fff28dE>

0000000100000b4c <__bril_parse_bool>:
100000b4c:     	sub	sp, sp, #0x40
100000b50:     	stp	x20, x19, [sp, #0x20]
100000b54:     	stp	x29, x30, [sp, #0x30]
100000b58:     	add	x29, sp, #0x30
100000b5c:     	mov	x19, x0
100000b60:     	bl	0x100005858 <_write+0x100005858>
100000b64:     	mov	x8, x0
100000b68:     	add	x0, sp, #0x8
100000b6c:     	add	x2, x8, #0x1
100000b70:     	mov	x1, x19
100000b74:     	bl	0x100001e04 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E>
100000b78:     	ldr	x8, [sp, #0x8]
100000b7c:     	cbnz	x8, 0x100000c00 <__bril_parse_bool+0xb4>
100000b80:     	ldp	x8, x9, [sp, #0x10]
100000b84:     	cmp	x9, #0x5
100000b88:     	b.eq	0x100000bbc <__bril_parse_bool+0x70>
100000b8c:     	cmp	x9, #0x4
100000b90:     	b.ne	0x100000c00 <__bril_parse_bool+0xb4>
100000b94:     	ldr	w8, [x8]
100000b98:     	mov	w9, #0x7274             ; =29300
100000b9c:     	movk	w9, #0x6575, lsl #16
100000ba0:     	cmp	w8, w9
100000ba4:     	b.ne	0x100000c00 <__bril_parse_bool+0xb4>
100000ba8:     	mov	w0, #0x1                ; =1
100000bac:     	ldp	x29, x30, [sp, #0x30]
100000bb0:     	ldp	x20, x19, [sp, #0x20]
100000bb4:     	add	sp, sp, #0x40
100000bb8:     	ret
100000bbc:     	ldrb	w9, [x8, #0x4]
100000bc0:     	ldr	w8, [x8]
100000bc4:     	orr	x8, x8, x9, lsl #32
100000bc8:     	rev	x8, x8
100000bcc:     	mov	x9, #0x65000000         ; =1694498816
100000bd0:     	movk	x9, #0x6c73, lsl #32
100000bd4:     	movk	x9, #0x6661, lsl #48
100000bd8:     	cmp	x8, x9
100000bdc:     	cset	w8, hi
100000be0:     	cset	w9, lo
100000be4:     	cmp	w8, w9
100000be8:     	b.ne	0x100000c00 <__bril_parse_bool+0xb4>
100000bec:     	mov	w0, #0x0                ; =0
100000bf0:     	ldp	x29, x30, [sp, #0x30]
100000bf4:     	ldp	x20, x19, [sp, #0x20]
100000bf8:     	add	sp, sp, #0x40
100000bfc:     	ret
100000c00:     	bl	0x100005828 <__ZN4core6result13unwrap_failed17h172b8a6210fff28dE>

0000000100000c04 <__bril_parse_float>:
100000c04:     	sub	sp, sp, #0x40
100000c08:     	stp	x20, x19, [sp, #0x20]
100000c0c:     	stp	x29, x30, [sp, #0x30]
100000c10:     	add	x29, sp, #0x30
100000c14:     	mov	x19, x0
100000c18:     	bl	0x100005858 <_write+0x100005858>
100000c1c:     	mov	x8, x0
100000c20:     	add	x0, sp, #0x8
100000c24:     	add	x2, x8, #0x1
100000c28:     	mov	x1, x19
100000c2c:     	bl	0x100001e04 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E>
100000c30:     	ldr	x8, [sp, #0x8]
100000c34:     	cbnz	x8, 0x100000c60 <__bril_parse_float+0x5c>
100000c38:     	ldp	x1, x2, [sp, #0x10]
100000c3c:     	add	x0, sp, #0x8
100000c40:     	bl	0x100002054 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE>
100000c44:     	ldrb	w8, [sp, #0x8]
100000c48:     	cbnz	w8, 0x100000c60 <__bril_parse_float+0x5c>
100000c4c:     	ldr	d0, [sp, #0x10]
100000c50:     	ldp	x29, x30, [sp, #0x30]
100000c54:     	ldp	x20, x19, [sp, #0x20]
100000c58:     	add	sp, sp, #0x40
100000c5c:     	ret
100000c60:     	bl	0x100005828 <__ZN4core6result13unwrap_failed17h172b8a6210fff28dE>

0000000100000c64 <_rust_begin_unwind>:
100000c64:     	b	0x100000c64 <_rust_begin_unwind>

0000000100000c68 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E>:
100000c68:     	stp	x29, x30, [sp, #-0x10]!
100000c6c:     	mov	x29, sp
100000c70:     	ldr	x9, [x0]
100000c74:     	cbz	x9, 0x100000c90 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x28>
100000c78:     	ldr	w8, [x0, #0x308]
100000c7c:     	tbnz	w8, #0x1f, 0x100000c90 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x28>
100000c80:     	cmp	w8, #0x12
100000c84:     	b.ls	0x100000c9c <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x34>
100000c88:     	mov	x0, #-0x1               ; =-1
100000c8c:     	b	0x100000c94 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x2c>
100000c90:     	mov	x0, #0x0                ; =0
100000c94:     	ldp	x29, x30, [sp], #0x10
100000c98:     	ret
100000c9c:     	mov	x10, x0
100000ca0:     	mov	x0, #0x0                ; =0
100000ca4:     	cbz	w8, 0x100000cdc <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x74>
100000ca8:     	mov	x11, #0x0               ; =0
100000cac:     	add	x12, x10, #0x8
100000cb0:     	b	0x100000cc0 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x58>
100000cb4:     	add	x11, x11, #0x1
100000cb8:     	cmp	x8, x11
100000cbc:     	b.eq	0x100000cdc <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x74>
100000cc0:     	add	x13, x0, x0, lsl #2
100000cc4:     	lsl	x0, x13, #1
100000cc8:     	cmp	x11, x9
100000ccc:     	b.hs	0x100000cb4 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x4c>
100000cd0:     	ldrb	w13, [x12, x11]
100000cd4:     	add	x0, x0, x13
100000cd8:     	b	0x100000cb4 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x4c>
100000cdc:     	cmp	x9, x8
100000ce0:     	b.ls	0x100000c94 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x2c>
100000ce4:     	add	x11, x10, #0x8
100000ce8:     	ldrb	w12, [x11, x8]
100000cec:     	add	x13, x8, #0x1
100000cf0:     	cmp	x13, x9
100000cf4:     	b.ne	0x100000d1c <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0xb4>
100000cf8:     	cmp	w12, #0x5
100000cfc:     	b.ne	0x100000d1c <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0xb4>
100000d00:     	ldrb	w9, [x10, #0x30c]
100000d04:     	cbnz	w9, 0x100000d24 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0xbc>
100000d08:     	cbz	w8, 0x100000c94 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x2c>
100000d0c:     	add	x8, x8, x11
100000d10:     	ldurb	w8, [x8, #-0x1]
100000d14:     	tbnz	w8, #0x0, 0x100000d24 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0xbc>
100000d18:     	b	0x100000c94 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x2c>
100000d1c:     	cmp	w12, #0x4
100000d20:     	b.ls	0x100000c94 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x2c>
100000d24:     	add	x0, x0, #0x1
100000d28:     	b	0x100000c94 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E+0x2c>

0000000100000d2c <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE>:
100000d2c:     	stp	x29, x30, [sp, #-0x10]!
100000d30:     	mov	x29, sp
100000d34:     	ldr	x10, [x0]
100000d38:     	cbz	x10, 0x100000e94 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x168>
100000d3c:     	and	x9, x1, #0x3f
100000d40:     	adrp	x11, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000d44:     	add	x11, x11, #0x8c0
100000d48:     	ldrh	w8, [x11, x9, lsl #1]
100000d4c:     	and	x15, x8, #0x7ff
100000d50:     	cmp	w15, #0x51d
100000d54:     	b.hs	0x100000ef0 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x1c4>
100000d58:     	lsr	x8, x8, #11
100000d5c:     	add	x11, x11, x9, lsl #1
100000d60:     	ldrh	w11, [x11, #0x2]
100000d64:     	and	x13, x11, #0x7ff
100000d68:     	add	x11, x0, #0x8
100000d6c:     	neg	x12, x10
100000d70:     	sub	x13, x15, x13
100000d74:     	neg	x14, x15
100000d78:     	adrp	x16, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100000d7c:     	add	x16, x16, #0x942
100000d80:     	add	x15, x16, x15
100000d84:     	mov	x16, #-0x51c            ; =-1308
100000d88:     	add	x17, x13, x16
100000d8c:     	cmn	x17, #0x51c
100000d90:     	b.eq	0x100000ddc <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xb0>
100000d94:     	cmp	x14, x16
100000d98:     	b.eq	0x100000ddc <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xb0>
100000d9c:     	add	x17, x12, x16
100000da0:     	cmn	x17, #0x51c
100000da4:     	b.eq	0x100000dd8 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xac>
100000da8:     	cmn	x16, #0x21c
100000dac:     	b.eq	0x100000eec <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x1c0>
100000db0:     	add	x17, x15, x16
100000db4:     	ldrb	w17, [x17, #0x51c]
100000db8:     	add	x1, x11, x16
100000dbc:     	ldrb	w1, [x1, #0x51c]
100000dc0:     	add	x16, x16, #0x1
100000dc4:     	cmp	w1, w17
100000dc8:     	b.eq	0x100000d88 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x5c>
100000dcc:     	cset	w11, lo
100000dd0:     	sub	x8, x8, x11
100000dd4:     	b	0x100000ddc <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xb0>
100000dd8:     	sub	x8, x8, #0x1
100000ddc:     	mov	x11, #0x0               ; =0
100000de0:     	add	x12, x0, #0x7
100000de4:     	add	x13, x12, x8
100000de8:     	mov	x14, #-0x3333333333333334 ; =-3689348814741910324
100000dec:     	movk	x14, #0xcccd
100000df0:     	mov	x15, #-0xa              ; =-10
100000df4:     	mov	w16, #0x1               ; =1
100000df8:     	b	0x100000e08 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xdc>
100000dfc:     	strb	w2, [x13, x10]
100000e00:     	mov	x10, x17
100000e04:     	cbz	x17, 0x100000e44 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x118>
100000e08:     	cmp	x10, #0x301
100000e0c:     	b.hs	0x100000eec <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x1c0>
100000e10:     	sub	x17, x10, #0x1
100000e14:     	add	x3, x17, x8
100000e18:     	ldrb	w1, [x12, x10]
100000e1c:     	lsl	x1, x1, x9
100000e20:     	add	x1, x1, x11
100000e24:     	umulh	x11, x1, x14
100000e28:     	lsr	x11, x11, #3
100000e2c:     	madd	x2, x11, x15, x1
100000e30:     	cmp	x3, #0x300
100000e34:     	b.lo	0x100000dfc <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xd0>
100000e38:     	cbz	x2, 0x100000e00 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xd4>
100000e3c:     	strb	w16, [x0, #0x30c]
100000e40:     	b	0x100000e00 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0xd4>
100000e44:     	cmp	x1, #0xa
100000e48:     	b.hs	0x100000e9c <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x170>
100000e4c:     	ldr	x9, [x0]
100000e50:     	ldr	w10, [x0, #0x308]
100000e54:     	add	w10, w10, w8
100000e58:     	str	w10, [x0, #0x308]
100000e5c:     	add	x9, x9, x8
100000e60:     	mov	w8, #0x300              ; =768
100000e64:     	cmp	x9, #0x300
100000e68:     	csel	x8, x9, x8, lo
100000e6c:     	str	x8, [x0]
100000e70:     	cbz	x9, 0x100000e94 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x168>
100000e74:     	add	x8, x8, #0x7
100000e78:     	ldrb	w9, [x0, x8]
100000e7c:     	cbnz	w9, 0x100000e94 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x168>
100000e80:     	sub	x9, x8, #0x8
100000e84:     	str	x9, [x0]
100000e88:     	sub	x8, x8, #0x1
100000e8c:     	cmp	x8, #0x7
100000e90:     	b.ne	0x100000e78 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x14c>
100000e94:     	ldp	x29, x30, [sp], #0x10
100000e98:     	ret
100000e9c:     	add	x9, x8, #0x7
100000ea0:     	mov	x10, #-0x3333333333333334 ; =-3689348814741910324
100000ea4:     	movk	x10, #0xcccd
100000ea8:     	mov	x12, #-0xa              ; =-10
100000eac:     	mov	w13, #0x1               ; =1
100000eb0:     	b	0x100000ec8 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x19c>
100000eb4:     	strb	w15, [x0, x9]
100000eb8:     	sub	x9, x9, #0x1
100000ebc:     	cmp	x11, #0xa
100000ec0:     	mov	x11, x14
100000ec4:     	b.lo	0x100000e4c <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x120>
100000ec8:     	sub	x16, x9, #0x8
100000ecc:     	umulh	x14, x11, x10
100000ed0:     	lsr	x14, x14, #3
100000ed4:     	madd	x15, x14, x12, x11
100000ed8:     	cmp	x16, #0x300
100000edc:     	b.lo	0x100000eb4 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x188>
100000ee0:     	cbz	x15, 0x100000eb8 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x18c>
100000ee4:     	strb	w13, [x0, #0x30c]
100000ee8:     	b	0x100000eb8 <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE+0x18c>
100000eec:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>
100000ef0:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>

0000000100000ef4 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E>:
100000ef4:     	sub	sp, sp, #0x40
100000ef8:     	stp	x29, x30, [sp, #0x30]
100000efc:     	add	x29, sp, #0x30
100000f00:     	ldr	x9, [x0]
100000f04:     	lsr	x10, x9, #4
100000f08:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100000f0c:     	add	x8, x8, #0x63c
100000f10:     	cmp	x10, #0x271
100000f14:     	b.lo	0x100000f98 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0xa4>
100000f18:     	mov	x10, #0x0               ; =0
100000f1c:     	mov	x11, #0x594b            ; =22859
100000f20:     	movk	x11, #0x3886, lsl #16
100000f24:     	movk	x11, #0xc5d6, lsl #32
100000f28:     	movk	x11, #0x346d, lsl #48
100000f2c:     	mov	w12, #0xd8f0            ; =55536
100000f30:     	mov	w13, #0x147b            ; =5243
100000f34:     	mov	w14, #-0x64             ; =-100
100000f38:     	add	x15, sp, #0x9
100000f3c:     	mov	w16, #0xe0ff            ; =57599
100000f40:     	movk	w16, #0x5f5, lsl #16
100000f44:     	mov	x17, x9
100000f48:     	umulh	x9, x9, x11
100000f4c:     	lsr	x9, x9, #11
100000f50:     	madd	w0, w9, w12, w17
100000f54:     	ubfx	w2, w0, #2, #14
100000f58:     	mul	w2, w2, w13
100000f5c:     	lsr	w2, w2, #17
100000f60:     	madd	w0, w2, w14, w0
100000f64:     	and	x0, x0, #0xffff
100000f68:     	add	x3, x15, x10
100000f6c:     	ldrh	w2, [x8, w2, uxtw #1]
100000f70:     	sturh	w2, [x3, #0x23]
100000f74:     	ldrh	w0, [x8, x0, lsl #1]
100000f78:     	sturh	w0, [x3, #0x25]
100000f7c:     	sub	x10, x10, #0x4
100000f80:     	cmp	x17, x16
100000f84:     	b.hi	0x100000f44 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0x50>
100000f88:     	add	x10, x10, #0x27
100000f8c:     	cmp	x9, #0x63
100000f90:     	b.hi	0x100000fa4 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0xb0>
100000f94:     	b	0x100000fd4 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0xe0>
100000f98:     	mov	w10, #0x27              ; =39
100000f9c:     	cmp	x9, #0x63
100000fa0:     	b.ls	0x100000fd4 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0xe0>
100000fa4:     	ubfx	w11, w9, #2, #14
100000fa8:     	mov	w12, #0x147b            ; =5243
100000fac:     	mul	w11, w11, w12
100000fb0:     	lsr	w11, w11, #17
100000fb4:     	mov	w12, #-0x64             ; =-100
100000fb8:     	madd	w9, w11, w12, w9
100000fbc:     	and	x9, x9, #0xffff
100000fc0:     	sub	x10, x10, #0x2
100000fc4:     	ldrh	w9, [x8, x9, lsl #1]
100000fc8:     	add	x12, sp, #0x9
100000fcc:     	strh	w9, [x12, x10]
100000fd0:     	mov	x9, x11
100000fd4:     	cmp	x9, #0xa
100000fd8:     	b.hs	0x100000ff0 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0xfc>
100000fdc:     	sub	x10, x10, #0x1
100000fe0:     	orr	w8, w9, #0x30
100000fe4:     	add	x9, sp, #0x9
100000fe8:     	strb	w8, [x9, x10]
100000fec:     	b	0x100001000 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17hdfe0988635c7f2a7E+0x10c>
100000ff0:     	sub	x10, x10, #0x2
100000ff4:     	ldrh	w8, [x8, x9, lsl #1]
100000ff8:     	add	x9, sp, #0x9
100000ffc:     	strh	w8, [x9, x10]
100001000:     	add	x8, sp, #0x9
100001004:     	mov	w9, #0x27               ; =39
100001008:     	sub	x5, x9, x10
10000100c:     	add	x4, x8, x10
100001010:     	mov	x0, x1
100001014:     	mov	w1, #0x1                ; =1
100001018:     	mov	w2, #0x1                ; =1
10000101c:     	mov	x3, #0x0                ; =0
100001020:     	bl	0x100001030 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE>
100001024:     	ldp	x29, x30, [sp, #0x30]
100001028:     	add	sp, sp, #0x40
10000102c:     	ret

0000000100001030 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE>:
100001030:     	sub	sp, sp, #0x70
100001034:     	stp	x28, x27, [sp, #0x10]
100001038:     	stp	x26, x25, [sp, #0x20]
10000103c:     	stp	x24, x23, [sp, #0x30]
100001040:     	stp	x22, x21, [sp, #0x40]
100001044:     	stp	x20, x19, [sp, #0x50]
100001048:     	stp	x29, x30, [sp, #0x60]
10000104c:     	add	x29, sp, #0x60
100001050:     	mov	x19, x5
100001054:     	mov	x20, x4
100001058:     	mov	x21, x3
10000105c:     	mov	x22, x2
100001060:     	tbz	w1, #0x0, 0x1000010b8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x88>
100001064:     	ldr	w8, [x0, #0x34]
100001068:     	and	x9, x8, #0x1
10000106c:     	mov	w10, #0x2b              ; =43
100001070:     	mov	w11, #0x110000          ; =1114112
100001074:     	cmp	w9, #0x0
100001078:     	csel	w23, w11, w10, eq
10000107c:     	add	x9, x9, x19
100001080:     	tbz	w8, #0x2, 0x1000010c8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x98>
100001084:     	mov	x10, #0x0               ; =0
100001088:     	cbz	x21, 0x1000010a8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x78>
10000108c:     	mov	x11, x22
100001090:     	mov	x12, x21
100001094:     	ldrsb	w13, [x11], #0x1
100001098:     	cmn	w13, #0x41
10000109c:     	cinc	x10, x10, gt
1000010a0:     	subs	x12, x12, #0x1
1000010a4:     	b.ne	0x100001094 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x64>
1000010a8:     	add	x9, x10, x9
1000010ac:     	ldr	x10, [x0]
1000010b0:     	cbnz	x10, 0x1000010d4 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xa4>
1000010b4:     	b	0x1000010f8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xc8>
1000010b8:     	add	x9, x19, #0x1
1000010bc:     	ldr	w8, [x0, #0x34]
1000010c0:     	mov	w23, #0x2d              ; =45
1000010c4:     	tbnz	w8, #0x2, 0x100001084 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x54>
1000010c8:     	mov	x22, #0x0               ; =0
1000010cc:     	ldr	x10, [x0]
1000010d0:     	cbz	x10, 0x1000010f8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xc8>
1000010d4:     	ldr	x10, [x0, #0x8]
1000010d8:     	subs	x27, x10, x9
1000010dc:     	b.ls	0x1000010f8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xc8>
1000010e0:     	tbnz	w8, #0x3, 0x10000116c <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x13c>
1000010e4:     	ldrb	w8, [x0, #0x38]
1000010e8:     	cmp	w8, #0x1
1000010ec:     	b.gt	0x1000011d8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1a8>
1000010f0:     	cbz	w8, 0x1000011f8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1c8>
1000010f4:     	b	0x1000011f0 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1c0>
1000010f8:     	ldp	x24, x25, [x0, #0x20]
1000010fc:     	mov	x0, x24
100001100:     	mov	x1, x25
100001104:     	mov	x2, x23
100001108:     	mov	x3, x22
10000110c:     	mov	x4, x21
100001110:     	bl	0x1000012c0 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E>
100001114:     	tbz	w0, #0x0, 0x10000113c <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x10c>
100001118:     	mov	w0, #0x1                ; =1
10000111c:     	ldp	x29, x30, [sp, #0x60]
100001120:     	ldp	x20, x19, [sp, #0x50]
100001124:     	ldp	x22, x21, [sp, #0x40]
100001128:     	ldp	x24, x23, [sp, #0x30]
10000112c:     	ldp	x26, x25, [sp, #0x20]
100001130:     	ldp	x28, x27, [sp, #0x10]
100001134:     	add	sp, sp, #0x70
100001138:     	ret
10000113c:     	ldr	x3, [x25, #0x18]
100001140:     	mov	x0, x24
100001144:     	mov	x1, x20
100001148:     	mov	x2, x19
10000114c:     	ldp	x29, x30, [sp, #0x60]
100001150:     	ldp	x20, x19, [sp, #0x50]
100001154:     	ldp	x22, x21, [sp, #0x40]
100001158:     	ldp	x24, x23, [sp, #0x30]
10000115c:     	ldp	x26, x25, [sp, #0x20]
100001160:     	ldp	x28, x27, [sp, #0x10]
100001164:     	add	sp, sp, #0x70
100001168:     	br	x3
10000116c:     	ldr	w8, [x0, #0x30]
100001170:     	str	w8, [sp, #0xc]
100001174:     	mov	w8, #0x30               ; =48
100001178:     	str	w8, [x0, #0x30]
10000117c:     	ldrb	w28, [x0, #0x38]
100001180:     	mov	w8, #0x1                ; =1
100001184:     	strb	w8, [x0, #0x38]
100001188:     	ldp	x24, x25, [x0, #0x20]
10000118c:     	mov	x26, x0
100001190:     	mov	x0, x24
100001194:     	mov	x1, x25
100001198:     	mov	x2, x23
10000119c:     	mov	x3, x22
1000011a0:     	mov	x4, x21
1000011a4:     	bl	0x1000012c0 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E>
1000011a8:     	mov	x8, x0
1000011ac:     	mov	w0, #0x1                ; =1
1000011b0:     	tbnz	w8, #0x0, 0x10000111c <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xec>
1000011b4:     	add	x21, x27, #0x1
1000011b8:     	subs	x21, x21, #0x1
1000011bc:     	b.eq	0x100001284 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x254>
1000011c0:     	ldr	x8, [x25, #0x20]
1000011c4:     	mov	x0, x24
1000011c8:     	mov	w1, #0x30               ; =48
1000011cc:     	blr	x8
1000011d0:     	tbz	w0, #0x0, 0x1000011b8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x188>
1000011d4:     	b	0x100001118 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xe8>
1000011d8:     	cmp	w8, #0x2
1000011dc:     	b.ne	0x1000011f0 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1c0>
1000011e0:     	lsr	x8, x27, #1
1000011e4:     	add	x9, x27, #0x1
1000011e8:     	lsr	x27, x9, #1
1000011ec:     	b	0x1000011f8 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1c8>
1000011f0:     	mov	x8, x27
1000011f4:     	mov	x27, #0x0               ; =0
1000011f8:     	ldp	x24, x25, [x0, #0x20]
1000011fc:     	add	x28, x8, #0x1
100001200:     	ldr	w26, [x0, #0x30]
100001204:     	subs	x28, x28, #0x1
100001208:     	b.eq	0x100001224 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1f4>
10000120c:     	ldr	x8, [x25, #0x20]
100001210:     	mov	x0, x24
100001214:     	mov	x1, x26
100001218:     	blr	x8
10000121c:     	tbz	w0, #0x0, 0x100001204 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x1d4>
100001220:     	b	0x100001118 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xe8>
100001224:     	mov	x0, x24
100001228:     	mov	x1, x25
10000122c:     	mov	x2, x23
100001230:     	mov	x3, x22
100001234:     	mov	x4, x21
100001238:     	bl	0x1000012c0 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E>
10000123c:     	tbnz	w0, #0x0, 0x100001118 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xe8>
100001240:     	ldr	x8, [x25, #0x18]
100001244:     	mov	x0, x24
100001248:     	mov	x1, x20
10000124c:     	mov	x2, x19
100001250:     	blr	x8
100001254:     	tbnz	w0, #0x0, 0x100001118 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xe8>
100001258:     	mov	x19, #0x0               ; =0
10000125c:     	cmp	x27, x19
100001260:     	b.eq	0x1000012b0 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x280>
100001264:     	add	x19, x19, #0x1
100001268:     	ldr	x8, [x25, #0x20]
10000126c:     	mov	x0, x24
100001270:     	mov	x1, x26
100001274:     	blr	x8
100001278:     	cbz	w0, 0x10000125c <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x22c>
10000127c:     	sub	x8, x19, #0x1
100001280:     	b	0x1000012b4 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0x284>
100001284:     	ldr	x8, [x25, #0x18]
100001288:     	mov	x0, x24
10000128c:     	mov	x1, x20
100001290:     	mov	x2, x19
100001294:     	blr	x8
100001298:     	tbnz	w0, #0x0, 0x100001118 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xe8>
10000129c:     	mov	w0, #0x0                ; =0
1000012a0:     	ldr	w8, [sp, #0xc]
1000012a4:     	str	w8, [x26, #0x30]
1000012a8:     	strb	w28, [x26, #0x38]
1000012ac:     	b	0x10000111c <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xec>
1000012b0:     	mov	x8, x27
1000012b4:     	cmp	x8, x27
1000012b8:     	cset	w0, lo
1000012bc:     	b	0x10000111c <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE+0xec>

00000001000012c0 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E>:
1000012c0:     	stp	x22, x21, [sp, #-0x30]!
1000012c4:     	stp	x20, x19, [sp, #0x10]
1000012c8:     	stp	x29, x30, [sp, #0x20]
1000012cc:     	add	x29, sp, #0x20
1000012d0:     	mov	x19, x4
1000012d4:     	mov	x20, x3
1000012d8:     	mov	x21, x1
1000012dc:     	cmp	w2, #0x110, lsl #12     ; =0x110000
1000012e0:     	b.eq	0x100001308 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E+0x48>
1000012e4:     	ldr	x8, [x21, #0x20]
1000012e8:     	mov	x22, x0
1000012ec:     	mov	x1, x2
1000012f0:     	blr	x8
1000012f4:     	mov	x8, x0
1000012f8:     	mov	x0, x22
1000012fc:     	tbz	w8, #0x0, 0x100001308 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E+0x48>
100001300:     	mov	w0, #0x1                ; =1
100001304:     	b	0x10000132c <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E+0x6c>
100001308:     	cbz	x20, 0x100001328 <__ZN4core3fmt9Formatter12pad_integral12write_prefix17h53c6aecfd2e4cf96E+0x68>
10000130c:     	ldr	x3, [x21, #0x18]
100001310:     	mov	x1, x20
100001314:     	mov	x2, x19
100001318:     	ldp	x29, x30, [sp, #0x20]
10000131c:     	ldp	x20, x19, [sp, #0x10]
100001320:     	ldp	x22, x21, [sp], #0x30
100001324:     	br	x3
100001328:     	mov	w0, #0x0                ; =0
10000132c:     	ldp	x29, x30, [sp, #0x20]
100001330:     	ldp	x20, x19, [sp, #0x10]
100001334:     	ldp	x22, x21, [sp], #0x30
100001338:     	ret

000000010000133c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E>:
10000133c:     	stp	x29, x30, [sp, #-0x10]!
100001340:     	mov	x29, sp
100001344:     	mov	x12, #0x0               ; =0
100001348:     	mov	x10, #0x0               ; =0
10000134c:     	and	x8, x1, #0x3f
100001350:     	mov	x9, x0
100001354:     	ldr	x11, [x9], #0x8
100001358:     	mov	w13, #0xa               ; =10
10000135c:     	cmp	x11, x12
100001360:     	b.eq	0x100001388 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x4c>
100001364:     	cmp	x12, #0x300
100001368:     	b.eq	0x1000014b4 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x178>
10000136c:     	add	x14, x0, x12
100001370:     	ldrb	w14, [x14, #0x8]
100001374:     	madd	x10, x10, x13, x14
100001378:     	add	x12, x12, #0x1
10000137c:     	lsr	x14, x10, x8
100001380:     	cbz	x14, 0x10000135c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x20>
100001384:     	b	0x1000013b4 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x78>
100001388:     	cbz	x10, 0x1000014ac <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x170>
10000138c:     	lsr	x12, x10, x8
100001390:     	cbz	x12, 0x10000139c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x60>
100001394:     	mov	x12, x11
100001398:     	b	0x1000013b4 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x78>
10000139c:     	mov	x12, x11
1000013a0:     	add	x10, x10, x10, lsl #2
1000013a4:     	lsl	x10, x10, #1
1000013a8:     	add	x12, x12, #0x1
1000013ac:     	lsr	x13, x10, x8
1000013b0:     	cbz	x13, 0x1000013a0 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x64>
1000013b4:     	ldr	w13, [x0, #0x308]
1000013b8:     	sub	w13, w13, w12
1000013bc:     	add	w13, w13, #0x1
1000013c0:     	str	w13, [x0, #0x308]
1000013c4:     	cmn	w13, #0x7ff
1000013c8:     	b.ge	0x1000013dc <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0xa0>
1000013cc:     	str	xzr, [x0]
1000013d0:     	str	wzr, [x0, #0x308]
1000013d4:     	strb	wzr, [x0, #0x30c]
1000013d8:     	b	0x1000014ac <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x170>
1000013dc:     	mov	x13, #-0x1              ; =-1
1000013e0:     	lsl	x13, x13, x8
1000013e4:     	mvn	x14, x13
1000013e8:     	subs	x13, x11, x12
1000013ec:     	b.ls	0x100001464 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x128>
1000013f0:     	mov	w15, #0x300             ; =768
1000013f4:     	cmp	x12, #0x300
1000013f8:     	csel	x15, x12, x15, lo
1000013fc:     	sub	x15, x15, #0x300
100001400:     	mov	w16, #0xa               ; =10
100001404:     	mov	x17, x9
100001408:     	cbz	x15, 0x1000014b4 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x178>
10000140c:     	lsr	x1, x10, x8
100001410:     	and	x10, x10, x14
100001414:     	ldrb	w2, [x17, x12]
100001418:     	madd	x10, x10, x16, x2
10000141c:     	strb	w1, [x17], #0x1
100001420:     	sub	x11, x11, #0x1
100001424:     	add	x15, x15, #0x1
100001428:     	cmp	x12, x11
10000142c:     	b.ne	0x100001408 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0xcc>
100001430:     	cbnz	x10, 0x10000146c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x130>
100001434:     	str	x13, [x0]
100001438:     	cmp	x13, #0x300
10000143c:     	b.hi	0x1000014b4 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x178>
100001440:     	add	x8, x13, #0x7
100001444:     	ldrb	w9, [x0, x8]
100001448:     	cbnz	w9, 0x1000014ac <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x170>
10000144c:     	sub	x9, x8, #0x8
100001450:     	str	x9, [x0]
100001454:     	sub	x8, x8, #0x1
100001458:     	cmp	x8, #0x7
10000145c:     	b.ne	0x100001444 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x108>
100001460:     	b	0x1000014ac <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x170>
100001464:     	cbz	x10, 0x1000014a8 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x16c>
100001468:     	mov	x13, #0x0               ; =0
10000146c:     	mov	w11, #0x1               ; =1
100001470:     	b	0x10000148c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x150>
100001474:     	strb	w12, [x9, x13]
100001478:     	add	x13, x13, #0x1
10000147c:     	and	x10, x10, x14
100001480:     	add	x10, x10, x10, lsl #2
100001484:     	lsl	x10, x10, #1
100001488:     	cbz	x10, 0x100001434 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0xf8>
10000148c:     	lsr	x12, x10, x8
100001490:     	cmp	x13, #0x300
100001494:     	b.lo	0x100001474 <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x138>
100001498:     	tst	w12, #0xff
10000149c:     	b.eq	0x10000147c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x140>
1000014a0:     	strb	w11, [x0, #0x30c]
1000014a4:     	b	0x10000147c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E+0x140>
1000014a8:     	str	xzr, [x0]
1000014ac:     	ldp	x29, x30, [sp], #0x10
1000014b0:     	ret
1000014b4:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>

00000001000014b8 <__ZN4core3fmt5write17h2595086b0d4e920fE>:
1000014b8:     	sub	sp, sp, #0x80
1000014bc:     	stp	x24, x23, [sp, #0x40]
1000014c0:     	stp	x22, x21, [sp, #0x50]
1000014c4:     	stp	x20, x19, [sp, #0x60]
1000014c8:     	stp	x29, x30, [sp, #0x70]
1000014cc:     	add	x29, sp, #0x70
1000014d0:     	mov	x19, x2
1000014d4:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000014d8:     	ldr	d0, [x8, #0x890]
1000014dc:     	str	d0, [sp, #0x30]
1000014e0:     	mov	w8, #0x3                ; =3
1000014e4:     	strb	w8, [sp, #0x38]
1000014e8:     	str	xzr, [sp]
1000014ec:     	str	xzr, [sp, #0x10]
1000014f0:     	stp	x0, x1, [sp, #0x20]
1000014f4:     	ldr	x8, [x2, #0x20]
1000014f8:     	cbz	x8, 0x1000015f8 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x140>
1000014fc:     	ldr	x9, [x19, #0x28]
100001500:     	cbz	x9, 0x10000166c <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1b4>
100001504:     	ldr	x10, [x19]
100001508:     	ldr	x21, [x19, #0x10]
10000150c:     	sub	x11, x9, #0x1
100001510:     	and	x11, x11, #0x1fffffffffffffff
100001514:     	add	x20, x11, #0x1
100001518:     	add	x22, x10, #0x8
10000151c:     	lsl	x10, x9, #6
100001520:     	sub	x23, x10, x9, lsl #3
100001524:     	add	x24, x8, #0x18
100001528:     	ldr	x2, [x22]
10000152c:     	cbz	x2, 0x100001544 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x8c>
100001530:     	ldp	x0, x8, [sp, #0x20]
100001534:     	ldur	x1, [x22, #-0x8]
100001538:     	ldr	x8, [x8, #0x18]
10000153c:     	blr	x8
100001540:     	tbnz	w0, #0x0, 0x100001698 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e0>
100001544:     	ldrb	w8, [x24, #0x18]
100001548:     	strb	w8, [sp, #0x38]
10000154c:     	ldp	w8, w9, [x24, #0x10]
100001550:     	stp	w8, w9, [sp, #0x30]
100001554:     	ldp	x9, x8, [x24, #-0x8]
100001558:     	cbz	x9, 0x10000158c <__ZN4core3fmt5write17h2595086b0d4e920fE+0xd4>
10000155c:     	cmp	x9, #0x1
100001560:     	b.ne	0x100001570 <__ZN4core3fmt5write17h2595086b0d4e920fE+0xb8>
100001564:     	add	x8, x21, x8, lsl #4
100001568:     	ldr	x9, [x8, #0x8]
10000156c:     	cbz	x9, 0x100001588 <__ZN4core3fmt5write17h2595086b0d4e920fE+0xd0>
100001570:     	mov	x9, #0x0                ; =0
100001574:     	stp	x9, x8, [sp]
100001578:     	ldur	x9, [x24, #-0x18]
10000157c:     	cmp	x9, #0x2
100001580:     	b.ne	0x1000015a0 <__ZN4core3fmt5write17h2595086b0d4e920fE+0xe8>
100001584:     	b	0x1000015b8 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x100>
100001588:     	ldr	x8, [x8]
10000158c:     	mov	w9, #0x1                ; =1
100001590:     	stp	x9, x8, [sp]
100001594:     	ldur	x9, [x24, #-0x18]
100001598:     	cmp	x9, #0x2
10000159c:     	b.eq	0x1000015b8 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x100>
1000015a0:     	ldur	x8, [x24, #-0x10]
1000015a4:     	cmp	x9, #0x1
1000015a8:     	b.ne	0x1000015c4 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x10c>
1000015ac:     	add	x8, x21, x8, lsl #4
1000015b0:     	ldr	x9, [x8, #0x8]
1000015b4:     	cbz	x9, 0x1000015c0 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x108>
1000015b8:     	mov	x9, #0x0                ; =0
1000015bc:     	b	0x1000015c8 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x110>
1000015c0:     	ldr	x8, [x8]
1000015c4:     	mov	w9, #0x1                ; =1
1000015c8:     	stp	x9, x8, [sp, #0x10]
1000015cc:     	ldr	x8, [x24, #0x8]
1000015d0:     	add	x8, x21, x8, lsl #4
1000015d4:     	ldp	x0, x9, [x8]
1000015d8:     	mov	x1, sp
1000015dc:     	blr	x9
1000015e0:     	tbnz	w0, #0x0, 0x100001698 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e0>
1000015e4:     	add	x22, x22, #0x10
1000015e8:     	add	x24, x24, #0x38
1000015ec:     	subs	x23, x23, #0x38
1000015f0:     	b.ne	0x100001528 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x70>
1000015f4:     	b	0x10000165c <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1a4>
1000015f8:     	ldr	x8, [x19, #0x18]
1000015fc:     	cbz	x8, 0x10000166c <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1b4>
100001600:     	ldr	x9, [x19, #0x10]
100001604:     	sub	x10, x8, #0x1
100001608:     	and	x10, x10, #0xfffffffffffffff
10000160c:     	ldr	x11, [x19]
100001610:     	add	x20, x10, #0x1
100001614:     	add	x21, x11, #0x8
100001618:     	add	x22, x9, #0x8
10000161c:     	lsl	x23, x8, #4
100001620:     	ldr	x2, [x21]
100001624:     	cbz	x2, 0x10000163c <__ZN4core3fmt5write17h2595086b0d4e920fE+0x184>
100001628:     	ldp	x0, x8, [sp, #0x20]
10000162c:     	ldur	x1, [x21, #-0x8]
100001630:     	ldr	x8, [x8, #0x18]
100001634:     	blr	x8
100001638:     	tbnz	w0, #0x0, 0x100001698 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e0>
10000163c:     	ldp	x0, x8, [x22, #-0x8]
100001640:     	mov	x1, sp
100001644:     	blr	x8
100001648:     	tbnz	w0, #0x0, 0x100001698 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e0>
10000164c:     	add	x21, x21, #0x10
100001650:     	add	x22, x22, #0x10
100001654:     	subs	x23, x23, #0x10
100001658:     	b.ne	0x100001620 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x168>
10000165c:     	ldr	x8, [x19, #0x8]
100001660:     	cmp	x20, x8
100001664:     	b.lo	0x10000167c <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1c4>
100001668:     	b	0x1000016a0 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e8>
10000166c:     	mov	x20, #0x0               ; =0
100001670:     	ldr	x8, [x19, #0x8]
100001674:     	cmp	x20, x8
100001678:     	b.hs	0x1000016a0 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e8>
10000167c:     	ldr	x8, [x19]
100001680:     	add	x8, x8, x20, lsl #4
100001684:     	ldp	x0, x9, [sp, #0x20]
100001688:     	ldp	x1, x2, [x8]
10000168c:     	ldr	x8, [x9, #0x18]
100001690:     	blr	x8
100001694:     	tbz	w0, #0x0, 0x1000016a0 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1e8>
100001698:     	mov	w0, #0x1                ; =1
10000169c:     	b	0x1000016a4 <__ZN4core3fmt5write17h2595086b0d4e920fE+0x1ec>
1000016a0:     	mov	w0, #0x0                ; =0
1000016a4:     	ldp	x29, x30, [sp, #0x70]
1000016a8:     	ldp	x20, x19, [sp, #0x60]
1000016ac:     	ldp	x22, x21, [sp, #0x50]
1000016b0:     	ldp	x24, x23, [sp, #0x40]
1000016b4:     	add	sp, sp, #0x80
1000016b8:     	ret

00000001000016bc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E>:
1000016bc:     	stp	x20, x19, [sp, #-0x20]!
1000016c0:     	stp	x29, x30, [sp, #0x10]
1000016c4:     	add	x29, sp, #0x10
1000016c8:     	mov	x19, x1
1000016cc:     	ands	x10, x1, #0x7
1000016d0:     	b.eq	0x10000172c <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x70>
1000016d4:     	ldr	x8, [x0, #0xa0]
1000016d8:     	cmp	x8, #0x29
1000016dc:     	b.hs	0x10000180c <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x150>
1000016e0:     	cbz	x8, 0x100001728 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x6c>
1000016e4:     	mov	x9, #0x0                ; =0
1000016e8:     	adrp	x11, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000016ec:     	add	x11, x11, #0x608
1000016f0:     	ldr	w10, [x11, x10, lsl #2]
1000016f4:     	lsl	x11, x8, #2
1000016f8:     	mov	x12, x0
1000016fc:     	ldr	w13, [x12]
100001700:     	umaddl	x9, w13, w10, x9
100001704:     	str	w9, [x12], #0x4
100001708:     	lsr	x9, x9, #32
10000170c:     	subs	x11, x11, #0x4
100001710:     	b.ne	0x1000016fc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x40>
100001714:     	cbz	w9, 0x100001728 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x6c>
100001718:     	cmp	x8, #0x28
10000171c:     	b.eq	0x100001808 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x14c>
100001720:     	str	w9, [x0, x8, lsl #2]
100001724:     	add	x8, x8, #0x1
100001728:     	str	x8, [x0, #0xa0]
10000172c:     	tbz	w19, #0x3, 0x100001784 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xc8>
100001730:     	ldr	x8, [x0, #0xa0]
100001734:     	cmp	x8, #0x29
100001738:     	b.hs	0x10000180c <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x150>
10000173c:     	cbz	x8, 0x100001780 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xc4>
100001740:     	mov	x9, #0x0                ; =0
100001744:     	lsl	x10, x8, #2
100001748:     	mov	w11, #0xe100            ; =57600
10000174c:     	movk	w11, #0x5f5, lsl #16
100001750:     	mov	x12, x0
100001754:     	ldr	w13, [x12]
100001758:     	umaddl	x9, w13, w11, x9
10000175c:     	str	w9, [x12], #0x4
100001760:     	lsr	x9, x9, #32
100001764:     	subs	x10, x10, #0x4
100001768:     	b.ne	0x100001754 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x98>
10000176c:     	cbz	w9, 0x100001780 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xc4>
100001770:     	cmp	x8, #0x28
100001774:     	b.eq	0x100001808 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x14c>
100001778:     	str	w9, [x0, x8, lsl #2]
10000177c:     	add	x8, x8, #0x1
100001780:     	str	x8, [x0, #0xa0]
100001784:     	tbnz	w19, #0x4, 0x1000017b4 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xf8>
100001788:     	tbnz	w19, #0x5, 0x1000017c8 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x10c>
10000178c:     	tbnz	w19, #0x6, 0x1000017dc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x120>
100001790:     	tbnz	w19, #0x7, 0x1000017f0 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0x134>
100001794:     	tbz	w19, #0x8, 0x1000017a8 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xec>
100001798:     	adrp	x1, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
10000179c:     	add	x1, x1, #0x8c
1000017a0:     	mov	w2, #0x1b               ; =27
1000017a4:     	bl	0x100001810 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E>
1000017a8:     	ldp	x29, x30, [sp, #0x10]
1000017ac:     	ldp	x20, x19, [sp], #0x20
1000017b0:     	ret
1000017b4:     	adrp	x1, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000017b8:     	add	x1, x1, #0x20
1000017bc:     	mov	w2, #0x2                ; =2
1000017c0:     	bl	0x100001810 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E>
1000017c4:     	tbz	w19, #0x5, 0x10000178c <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xd0>
1000017c8:     	adrp	x1, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000017cc:     	add	x1, x1, #0x28
1000017d0:     	mov	w2, #0x4                ; =4
1000017d4:     	bl	0x100001810 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E>
1000017d8:     	tbz	w19, #0x6, 0x100001790 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xd4>
1000017dc:     	adrp	x1, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000017e0:     	add	x1, x1, #0x38
1000017e4:     	mov	w2, #0x7                ; =7
1000017e8:     	bl	0x100001810 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E>
1000017ec:     	tbz	w19, #0x7, 0x100001794 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xd8>
1000017f0:     	adrp	x1, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000017f4:     	add	x1, x1, #0x54
1000017f8:     	mov	w2, #0xe                ; =14
1000017fc:     	bl	0x100001810 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E>
100001800:     	tbnz	w19, #0x8, 0x100001798 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xdc>
100001804:     	b	0x1000017a8 <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E+0xec>
100001808:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>
10000180c:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>

0000000100001810 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E>:
100001810:     	sub	sp, sp, #0xc0
100001814:     	stp	x20, x19, [sp, #0xa0]
100001818:     	stp	x29, x30, [sp, #0xb0]
10000181c:     	add	x29, sp, #0xb0
100001820:     	movi.2d	v0, #0000000000000000
100001824:     	stp	q0, q0, [sp, #0x80]
100001828:     	stp	q0, q0, [sp, #0x60]
10000182c:     	stp	q0, q0, [sp, #0x40]
100001830:     	stp	q0, q0, [sp, #0x20]
100001834:     	stp	q0, q0, [sp]
100001838:     	ldr	x9, [x0, #0xa0]
10000183c:     	cmp	x9, x2
100001840:     	b.hs	0x100001924 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x114>
100001844:     	cmp	x9, #0x29
100001848:     	b.hs	0x100001a40 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x230>
10000184c:     	mov	x11, #0x0               ; =0
100001850:     	mov	x8, #0x0                ; =0
100001854:     	add	x10, x2, #0x1
100001858:     	mov	x12, sp
10000185c:     	sub	x12, x12, #0x4
100001860:     	sub	x13, x2, #0x1
100001864:     	lsl	x14, x2, #2
100001868:     	mov	x3, x0
10000186c:     	mov	x15, x0
100001870:     	add	x9, x0, x9, lsl #2
100001874:     	mov	x16, #0x0               ; =0
100001878:     	add	x17, x12, x11, lsl #2
10000187c:     	cmp	x15, x9
100001880:     	b.eq	0x100001a00 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x1f0>
100001884:     	add	x15, x15, #0x4
100001888:     	ldr	w4, [x3, x16, lsl #2]
10000188c:     	add	x17, x17, #0x4
100001890:     	add	x16, x16, #0x1
100001894:     	cbz	w4, 0x10000187c <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x6c>
100001898:     	mov	x6, #0x0                ; =0
10000189c:     	mov	x5, #0x0                ; =0
1000018a0:     	add	x3, x11, x16
1000018a4:     	sub	x7, x11, #0x1
1000018a8:     	add	x19, x16, x7
1000018ac:     	cmp	x19, #0x28
1000018b0:     	b.hs	0x100001a3c <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x22c>
1000018b4:     	ldr	w19, [x1, x6]
1000018b8:     	ldr	w20, [x17, x6]
1000018bc:     	add	x5, x5, x20
1000018c0:     	umaddl	x19, w19, w4, x5
1000018c4:     	lsr	x5, x19, #32
1000018c8:     	str	w19, [x17, x6]
1000018cc:     	add	x7, x7, #0x1
1000018d0:     	add	x6, x6, #0x4
1000018d4:     	cmp	x14, x6
1000018d8:     	b.ne	0x1000018a8 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x98>
1000018dc:     	mov	x17, x2
1000018e0:     	cbz	w5, 0x100001904 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0xf4>
1000018e4:     	add	x17, x13, x11
1000018e8:     	add	x17, x17, x16
1000018ec:     	cmp	x17, #0x28
1000018f0:     	b.hs	0x100001a3c <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x22c>
1000018f4:     	add	x17, x2, x11
1000018f8:     	add	x17, x12, x17, lsl #2
1000018fc:     	str	w5, [x17, x16, lsl #2]
100001900:     	mov	x17, x10
100001904:     	add	x11, x11, x17
100001908:     	add	x11, x11, x16
10000190c:     	sub	x11, x11, #0x1
100001910:     	cmp	x8, x11
100001914:     	csel	x8, x8, x11, hi
100001918:     	mov	x11, x3
10000191c:     	mov	x3, x15
100001920:     	b	0x100001874 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x64>
100001924:     	cmp	x9, #0x29
100001928:     	b.hs	0x100001a40 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x230>
10000192c:     	mov	x11, #0x0               ; =0
100001930:     	mov	x8, #0x0                ; =0
100001934:     	add	x10, x9, #0x1
100001938:     	mov	x12, sp
10000193c:     	sub	x12, x12, #0x4
100001940:     	sub	x13, x9, #0x1
100001944:     	lsl	x14, x9, #2
100001948:     	mov	x15, x1
10000194c:     	add	x16, x1, x2, lsl #2
100001950:     	mov	x17, #0x0               ; =0
100001954:     	add	x2, x12, x11, lsl #2
100001958:     	cmp	x15, x16
10000195c:     	b.eq	0x100001a00 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x1f0>
100001960:     	add	x15, x15, #0x4
100001964:     	ldr	w3, [x1, x17, lsl #2]
100001968:     	add	x2, x2, #0x4
10000196c:     	add	x17, x17, #0x1
100001970:     	cbz	w3, 0x100001958 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x148>
100001974:     	mov	x5, #0x0                ; =0
100001978:     	mov	x4, #0x0                ; =0
10000197c:     	add	x1, x11, x17
100001980:     	sub	x6, x11, #0x1
100001984:     	add	x7, x17, x6
100001988:     	cmp	x7, #0x28
10000198c:     	b.hs	0x100001a3c <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x22c>
100001990:     	ldr	w7, [x0, x5]
100001994:     	ldr	w19, [x2, x5]
100001998:     	add	x4, x4, x19
10000199c:     	umaddl	x7, w7, w3, x4
1000019a0:     	lsr	x4, x7, #32
1000019a4:     	str	w7, [x2, x5]
1000019a8:     	add	x6, x6, #0x1
1000019ac:     	add	x5, x5, #0x4
1000019b0:     	cmp	x14, x5
1000019b4:     	b.ne	0x100001984 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x174>
1000019b8:     	mov	x2, x9
1000019bc:     	cbz	w4, 0x1000019e0 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x1d0>
1000019c0:     	add	x2, x13, x11
1000019c4:     	add	x2, x2, x17
1000019c8:     	cmp	x2, #0x28
1000019cc:     	b.hs	0x100001a3c <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x22c>
1000019d0:     	add	x2, x9, x11
1000019d4:     	add	x2, x12, x2, lsl #2
1000019d8:     	str	w4, [x2, x17, lsl #2]
1000019dc:     	mov	x2, x10
1000019e0:     	add	x11, x11, x2
1000019e4:     	add	x11, x11, x17
1000019e8:     	sub	x11, x11, #0x1
1000019ec:     	cmp	x8, x11
1000019f0:     	csel	x8, x8, x11, hi
1000019f4:     	mov	x11, x1
1000019f8:     	mov	x1, x15
1000019fc:     	b	0x100001950 <__ZN4core3num6bignum8Big32x4010mul_digits17h2c4cfa448df16e56E+0x140>
100001a00:     	ldp	q0, q1, [sp, #0x60]
100001a04:     	stp	q0, q1, [x0, #0x60]
100001a08:     	ldp	q0, q1, [sp, #0x80]
100001a0c:     	stp	q0, q1, [x0, #0x80]
100001a10:     	ldp	q0, q1, [sp, #0x20]
100001a14:     	stp	q0, q1, [x0, #0x20]
100001a18:     	ldp	q0, q1, [sp, #0x40]
100001a1c:     	stp	q0, q1, [x0, #0x40]
100001a20:     	ldp	q0, q1, [sp]
100001a24:     	stp	q0, q1, [x0]
100001a28:     	str	x8, [x0, #0xa0]
100001a2c:     	ldp	x29, x30, [sp, #0xb0]
100001a30:     	ldp	x20, x19, [sp, #0xa0]
100001a34:     	add	sp, sp, #0xc0
100001a38:     	ret
100001a3c:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>
100001a40:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>

0000000100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>:
100001a44:     	stp	x24, x23, [sp, #-0x40]!
100001a48:     	stp	x22, x21, [sp, #0x10]
100001a4c:     	stp	x20, x19, [sp, #0x20]
100001a50:     	stp	x29, x30, [sp, #0x30]
100001a54:     	add	x29, sp, #0x30
100001a58:     	mov	x20, x1
100001a5c:     	lsr	x23, x1, #5
100001a60:     	ldr	x8, [x0, #0xa0]
100001a64:     	cbz	x8, 0x100001a98 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x54>
100001a68:     	cmp	x8, #0x28
100001a6c:     	b.hi	0x100001b6c <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x128>
100001a70:     	sub	x8, x8, #0x1
100001a74:     	add	x9, x8, x23
100001a78:     	cmp	x9, #0x27
100001a7c:     	b.hi	0x100001b6c <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x128>
100001a80:     	ldr	w10, [x0, x8, lsl #2]
100001a84:     	str	w10, [x0, x9, lsl #2]
100001a88:     	sub	x8, x8, #0x1
100001a8c:     	sub	x9, x9, #0x1
100001a90:     	cmn	x8, #0x1
100001a94:     	b.ne	0x100001a78 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x34>
100001a98:     	and	x22, x20, #0x1f
100001a9c:     	lsl	x19, x23, #2
100001aa0:     	cmp	x20, #0x20
100001aa4:     	b.lo	0x100001ab8 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x74>
100001aa8:     	mov	x21, x0
100001aac:     	mov	x1, x19
100001ab0:     	bl	0x100005834 <_write+0x100005834>
100001ab4:     	mov	x0, x21
100001ab8:     	ldr	x8, [x0, #0xa0]
100001abc:     	add	x8, x8, x23
100001ac0:     	cbz	x22, 0x100001b50 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x10c>
100001ac4:     	sub	x9, x8, #0x1
100001ac8:     	cmp	x9, #0x27
100001acc:     	b.hi	0x100001b6c <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x128>
100001ad0:     	ldr	w9, [x0, x9, lsl #2]
100001ad4:     	neg	w12, w20
100001ad8:     	lsr	w11, w9, w12
100001adc:     	mov	x10, x8
100001ae0:     	cbz	w11, 0x100001af4 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0xb0>
100001ae4:     	cmp	x8, #0x27
100001ae8:     	b.hi	0x100001b6c <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x128>
100001aec:     	str	w11, [x0, x8, lsl #2]
100001af0:     	add	x10, x8, #0x1
100001af4:     	add	x11, x23, #0x1
100001af8:     	cmp	x11, x8
100001afc:     	b.hs	0x100001b40 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0xfc>
100001b00:     	and	w12, w12, #0x1f
100001b04:     	add	x13, x0, x8, lsl #2
100001b08:     	sub	x13, x13, #0x4
100001b0c:     	sub	x14, x8, #0x2
100001b10:     	cmp	x14, #0x28
100001b14:     	b.hs	0x100001b6c <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x128>
100001b18:     	lsl	w14, w9, w22
100001b1c:     	mov	x15, x13
100001b20:     	ldr	w9, [x15, #-0x4]!
100001b24:     	sub	x8, x8, #0x1
100001b28:     	lsr	w16, w9, w12
100001b2c:     	orr	w14, w16, w14
100001b30:     	str	w14, [x13]
100001b34:     	mov	x13, x15
100001b38:     	cmp	x11, x8
100001b3c:     	b.lo	0x100001b0c <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0xc8>
100001b40:     	ldr	w8, [x0, x19]
100001b44:     	lsl	w8, w8, w22
100001b48:     	str	w8, [x0, x19]
100001b4c:     	b	0x100001b54 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E+0x110>
100001b50:     	mov	x10, x8
100001b54:     	str	x10, [x0, #0xa0]
100001b58:     	ldp	x29, x30, [sp, #0x30]
100001b5c:     	ldp	x20, x19, [sp, #0x20]
100001b60:     	ldp	x22, x21, [sp, #0x10]
100001b64:     	ldp	x24, x23, [sp], #0x40
100001b68:     	ret
100001b6c:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>

0000000100001b70 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE>:
100001b70:     	stp	x26, x25, [sp, #-0x50]!
100001b74:     	stp	x24, x23, [sp, #0x10]
100001b78:     	stp	x22, x21, [sp, #0x20]
100001b7c:     	stp	x20, x19, [sp, #0x30]
100001b80:     	stp	x29, x30, [sp, #0x40]
100001b84:     	add	x29, sp, #0x40
100001b88:     	ldr	x8, [x29, #0x10]
100001b8c:     	subs	x9, x7, x8
100001b90:     	b.ls	0x100001bc8 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x58>
100001b94:     	cmp	x9, x8
100001b98:     	b.ls	0x100001bc8 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x58>
100001b9c:     	sub	x9, x7, x6
100001ba0:     	cmp	x9, x6
100001ba4:     	b.ls	0x100001bb4 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x44>
100001ba8:     	sub	x9, x7, x6, lsl #1
100001bac:     	cmp	x9, x8, lsl #1
100001bb0:     	b.hs	0x100001cec <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x17c>
100001bb4:     	subs	x8, x6, x8
100001bb8:     	b.ls	0x100001bc8 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x58>
100001bbc:     	sub	x9, x7, x8
100001bc0:     	cmp	x9, x8
100001bc4:     	b.ls	0x100001be4 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x74>
100001bc8:     	str	xzr, [x0]
100001bcc:     	ldp	x29, x30, [sp, #0x40]
100001bd0:     	ldp	x20, x19, [sp, #0x30]
100001bd4:     	ldp	x22, x21, [sp, #0x20]
100001bd8:     	ldp	x24, x23, [sp, #0x10]
100001bdc:     	ldp	x26, x25, [sp], #0x50
100001be0:     	ret
100001be4:     	cmp	x3, x2
100001be8:     	b.hi	0x100001d00 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x190>
100001bec:     	mov	x8, #0x0                ; =0
100001bf0:     	mov	x9, x1
100001bf4:     	cmp	x3, x8
100001bf8:     	b.eq	0x100001c74 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x104>
100001bfc:     	add	x10, x9, x3
100001c00:     	ldurb	w10, [x10, #-0x1]
100001c04:     	add	x8, x8, #0x1
100001c08:     	sub	x9, x9, #0x1
100001c0c:     	cmp	w10, #0x39
100001c10:     	b.eq	0x100001bf4 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x84>
100001c14:     	ldrb	w10, [x9, x3]
100001c18:     	add	w10, w10, #0x1
100001c1c:     	strb	w10, [x9, x3]
100001c20:     	sub	x10, x3, x8
100001c24:     	add	x10, x10, #0x1
100001c28:     	cmp	x10, x3
100001c2c:     	b.hs	0x100001cec <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x17c>
100001c30:     	sub	x8, x8, #0x1
100001c34:     	add	x9, x9, x3
100001c38:     	mov	x19, x0
100001c3c:     	add	x0, x9, #0x1
100001c40:     	mov	x20, x1
100001c44:     	mov	w1, #0x30               ; =48
100001c48:     	mov	x21, x2
100001c4c:     	mov	x2, x8
100001c50:     	mov	x22, x4
100001c54:     	mov	x23, x3
100001c58:     	bl	0x10000584c <_write+0x10000584c>
100001c5c:     	mov	x2, x21
100001c60:     	mov	x1, x20
100001c64:     	mov	x3, x23
100001c68:     	mov	x4, x22
100001c6c:     	mov	x0, x19
100001c70:     	b	0x100001cec <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x17c>
100001c74:     	mov	w19, #0x31              ; =49
100001c78:     	cbz	x3, 0x100001ccc <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x15c>
100001c7c:     	strb	w19, [x1]
100001c80:     	mov	w19, #0x30              ; =48
100001c84:     	subs	x8, x3, #0x1
100001c88:     	b.eq	0x100001ccc <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x15c>
100001c8c:     	mov	x20, x0
100001c90:     	add	x0, x1, #0x1
100001c94:     	mov	x21, x1
100001c98:     	mov	w1, #0x30               ; =48
100001c9c:     	mov	x22, x2
100001ca0:     	mov	x2, x8
100001ca4:     	mov	x24, x4
100001ca8:     	mov	x25, x3
100001cac:     	mov	x23, x5
100001cb0:     	bl	0x10000584c <_write+0x10000584c>
100001cb4:     	mov	x5, x23
100001cb8:     	mov	x2, x22
100001cbc:     	mov	x1, x21
100001cc0:     	mov	x3, x25
100001cc4:     	mov	x4, x24
100001cc8:     	mov	x0, x20
100001ccc:     	add	w8, w4, #0x1
100001cd0:     	sxth	w4, w8
100001cd4:     	cmp	x3, x2
100001cd8:     	b.hs	0x100001cec <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x17c>
100001cdc:     	cmp	w4, w5, sxth
100001ce0:     	b.le	0x100001cec <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x17c>
100001ce4:     	strb	w19, [x1, x3]
100001ce8:     	add	x3, x3, #0x1
100001cec:     	cmp	x3, x2
100001cf0:     	b.hi	0x100001d00 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x190>
100001cf4:     	stp	x1, x3, [x0]
100001cf8:     	strh	w4, [x0, #0x10]
100001cfc:     	b	0x100001bcc <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE+0x5c>
100001d00:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>

0000000100001d04 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E>:
100001d04:     	stp	x29, x30, [sp, #-0x10]!
100001d08:     	mov	x29, sp
100001d0c:     	cbz	x1, 0x100001e00 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xfc>
100001d10:     	ldrb	w8, [x0]
100001d14:     	cmp	w8, #0x30
100001d18:     	b.ls	0x100001e00 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xfc>
100001d1c:     	sxth	w8, w2
100001d20:     	cmp	w8, #0x1
100001d24:     	b.lt	0x100001d74 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0x70>
100001d28:     	and	x8, x2, #0xffff
100001d2c:     	mov	w9, #0x2                ; =2
100001d30:     	strh	w9, [x4]
100001d34:     	str	x0, [x4, #0x8]
100001d38:     	subs	x10, x8, x1
100001d3c:     	b.hs	0x100001dc0 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xbc>
100001d40:     	str	x8, [x4, #0x10]
100001d44:     	strh	w9, [x4, #0x18]
100001d48:     	adrp	x10, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100001d4c:     	add	x10, x10, #0x630
100001d50:     	mov	w11, #0x1               ; =1
100001d54:     	stp	x10, x11, [x4, #0x20]
100001d58:     	add	x10, x0, x8
100001d5c:     	strh	w9, [x4, #0x30]
100001d60:     	sub	x8, x1, x8
100001d64:     	subs	x3, x3, x8
100001d68:     	stp	x10, x8, [x4, #0x38]
100001d6c:     	b.ls	0x100001db8 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xb4>
100001d70:     	b	0x100001de8 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xe4>
100001d74:     	mov	w10, #0x2               ; =2
100001d78:     	strh	w10, [x4]
100001d7c:     	sxth	x8, w2
100001d80:     	adrp	x9, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100001d84:     	add	x9, x9, #0x631
100001d88:     	stp	x9, x10, [x4, #0x8]
100001d8c:     	neg	x9, x8
100001d90:     	strh	wzr, [x4, #0x18]
100001d94:     	str	x9, [x4, #0x20]
100001d98:     	strh	w10, [x4, #0x30]
100001d9c:     	stp	x0, x1, [x4, #0x38]
100001da0:     	subs	x10, x3, x1
100001da4:     	b.ls	0x100001db8 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xb4>
100001da8:     	cmp	x10, x9
100001dac:     	b.ls	0x100001db8 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xb4>
100001db0:     	add	x3, x10, x8
100001db4:     	b	0x100001de8 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xe4>
100001db8:     	mov	w1, #0x3                ; =3
100001dbc:     	b	0x100001df4 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xf0>
100001dc0:     	str	x1, [x4, #0x10]
100001dc4:     	strh	wzr, [x4, #0x18]
100001dc8:     	mov	w1, #0x2                ; =2
100001dcc:     	str	x10, [x4, #0x20]
100001dd0:     	cbz	x3, 0x100001df4 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E+0xf0>
100001dd4:     	strh	w1, [x4, #0x30]
100001dd8:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100001ddc:     	add	x8, x8, #0x630
100001de0:     	mov	w9, #0x1                ; =1
100001de4:     	stp	x8, x9, [x4, #0x38]
100001de8:     	strh	wzr, [x4, #0x48]
100001dec:     	str	x3, [x4, #0x50]
100001df0:     	mov	w1, #0x4                ; =4
100001df4:     	mov	x0, x4
100001df8:     	ldp	x29, x30, [sp], #0x10
100001dfc:     	ret
100001e00:     	bl	0x1000057f8 <__ZN4core9panicking5panic17hff67cc28c73a35f9E>

0000000100001e04 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E>:
100001e04:     	stp	x29, x30, [sp, #-0x10]!
100001e08:     	mov	x29, sp
100001e0c:     	sub	x9, x2, #0x1
100001e10:     	subs	x8, x9, #0xf
100001e14:     	csel	x10, xzr, x8, lo
100001e18:     	cbz	x9, 0x100002010 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x20c>
100001e1c:     	mov	x8, #0x0                ; =0
100001e20:     	add	x11, x1, #0x7
100001e24:     	and	x11, x11, #0xfffffffffffffff8
100001e28:     	sub	x11, x11, x1
100001e2c:     	adrp	x12, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100001e30:     	add	x12, x12, #0x744
100001e34:     	mov	w13, #-0x61             ; =-97
100001e38:     	mov	w14, #-0x40             ; =-64
100001e3c:     	b	0x100001e4c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x48>
100001e40:     	add	x8, x15, #0x1
100001e44:     	cmp	x8, x9
100001e48:     	b.hs	0x100002010 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x20c>
100001e4c:     	ldrsb	w15, [x1, x8]
100001e50:     	tbnz	w15, #0x1f, 0x100001ea8 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0xa4>
100001e54:     	sub	w15, w11, w8
100001e58:     	tst	x15, #0x7
100001e5c:     	b.eq	0x100001e6c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x68>
100001e60:     	add	x8, x8, #0x1
100001e64:     	b	0x100001e44 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x40>
100001e68:     	add	x8, x8, #0x10
100001e6c:     	cmp	x8, x10
100001e70:     	b.hs	0x100001e88 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x84>
100001e74:     	add	x15, x1, x8
100001e78:     	ldp	x16, x15, [x15]
100001e7c:     	orr	x15, x15, x16
100001e80:     	tst	x15, #0x8080808080808080
100001e84:     	b.eq	0x100001e68 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x64>
100001e88:     	cmp	x8, x9
100001e8c:     	b.hs	0x100001e44 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x40>
100001e90:     	ldrsb	w15, [x1, x8]
100001e94:     	tbnz	w15, #0x1f, 0x100001e44 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x40>
100001e98:     	add	x8, x8, #0x1
100001e9c:     	cmp	x9, x8
100001ea0:     	b.ne	0x100001e90 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x8c>
100001ea4:     	b	0x100002010 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x20c>
100001ea8:     	and	x15, x15, #0xff
100001eac:     	ldrb	w16, [x12, x15]
100001eb0:     	cmp	w16, #0x4
100001eb4:     	b.eq	0x100001f10 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x10c>
100001eb8:     	cmp	w16, #0x3
100001ebc:     	b.eq	0x100001ee4 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0xe0>
100001ec0:     	cmp	w16, #0x2
100001ec4:     	b.ne	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001ec8:     	add	x15, x8, #0x1
100001ecc:     	cmp	x15, x9
100001ed0:     	b.hs	0x10000201c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x218>
100001ed4:     	ldrsb	w16, [x1, x15]
100001ed8:     	cmn	w16, #0x41
100001edc:     	b.le	0x100001e40 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x3c>
100001ee0:     	b	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001ee4:     	add	x16, x8, #0x1
100001ee8:     	cmp	x16, x9
100001eec:     	b.hs	0x10000201c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x218>
100001ef0:     	ldrb	w16, [x1, x16]
100001ef4:     	cmp	w15, #0xe0
100001ef8:     	b.eq	0x100001f3c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x138>
100001efc:     	cmp	w15, #0xed
100001f00:     	b.ne	0x100001f5c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x158>
100001f04:     	cmp	w13, w16, sxtb
100001f08:     	b.ge	0x100001fec <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x1e8>
100001f0c:     	b	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001f10:     	add	x16, x8, #0x1
100001f14:     	cmp	x16, x9
100001f18:     	b.hs	0x10000201c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x218>
100001f1c:     	ldrsb	w17, [x1, x16]
100001f20:     	cmp	w15, #0xf0
100001f24:     	b.eq	0x100001f4c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x148>
100001f28:     	cmp	w15, #0xf4
100001f2c:     	b.ne	0x100001f78 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x174>
100001f30:     	cmn	w17, #0x71
100001f34:     	b.le	0x100001f98 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x194>
100001f38:     	b	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001f3c:     	and	w15, w16, #0xe0
100001f40:     	cmp	w15, #0xa0
100001f44:     	b.eq	0x100001fec <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x1e8>
100001f48:     	b	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001f4c:     	add	w15, w17, #0x70
100001f50:     	cmp	w15, #0x30
100001f54:     	b.lo	0x100001f98 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x194>
100001f58:     	b	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001f5c:     	add	w17, w15, #0x1f
100001f60:     	and	w17, w17, #0xff
100001f64:     	cmp	w17, #0xc
100001f68:     	b.hs	0x100001fcc <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x1c8>
100001f6c:     	cmp	w14, w16, sxtb
100001f70:     	b.gt	0x100001fec <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x1e8>
100001f74:     	b	0x100002024 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x220>
100001f78:     	add	w15, w15, #0xf
100001f7c:     	and	w16, w15, #0xff
100001f80:     	mov	w15, #0x1               ; =1
100001f84:     	cmp	w16, #0x2
100001f88:     	b.hi	0x100002028 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x224>
100001f8c:     	mov	w16, #0x1               ; =1
100001f90:     	cmn	w17, #0x40
100001f94:     	b.ge	0x10000202c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x228>
100001f98:     	add	x15, x8, #0x2
100001f9c:     	cmp	x15, x9
100001fa0:     	b.hs	0x10000201c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x218>
100001fa4:     	ldrsb	w15, [x1, x15]
100001fa8:     	cmn	w15, #0x41
100001fac:     	b.gt	0x100002004 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x200>
100001fb0:     	add	x15, x8, #0x3
100001fb4:     	cmp	x15, x9
100001fb8:     	b.hs	0x10000201c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x218>
100001fbc:     	ldrsb	w16, [x1, x15]
100001fc0:     	cmn	w16, #0x41
100001fc4:     	b.le	0x100001e40 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x3c>
100001fc8:     	b	0x100002048 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x244>
100001fcc:     	and	w17, w15, #0xfe
100001fd0:     	mov	w15, #0x1               ; =1
100001fd4:     	cmp	w17, #0xee
100001fd8:     	b.ne	0x100002028 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x224>
100001fdc:     	sxtb	w17, w16
100001fe0:     	mov	w16, #0x1               ; =1
100001fe4:     	cmn	w17, #0x40
100001fe8:     	b.ge	0x10000202c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x228>
100001fec:     	add	x15, x8, #0x2
100001ff0:     	cmp	x15, x9
100001ff4:     	b.hs	0x10000201c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x218>
100001ff8:     	ldrsb	w16, [x1, x15]
100001ffc:     	cmn	w16, #0x41
100002000:     	b.le	0x100001e40 <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x3c>
100002004:     	mov	w16, #0x1               ; =1
100002008:     	mov	w15, #0x2               ; =2
10000200c:     	b	0x10000202c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x228>
100002010:     	mov	x8, #0x0                ; =0
100002014:     	stp	x1, x9, [x0, #0x8]
100002018:     	b	0x10000203c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x238>
10000201c:     	mov	w16, #0x0               ; =0
100002020:     	b	0x10000202c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x228>
100002024:     	mov	w15, #0x1               ; =1
100002028:     	mov	w16, #0x1               ; =1
10000202c:     	str	x8, [x0, #0x8]
100002030:     	strb	w16, [x0, #0x10]
100002034:     	mov	w8, #0x1                ; =1
100002038:     	strb	w15, [x0, #0x11]
10000203c:     	str	x8, [x0]
100002040:     	ldp	x29, x30, [sp], #0x10
100002044:     	ret
100002048:     	mov	w16, #0x1               ; =1
10000204c:     	mov	w15, #0x3               ; =3
100002050:     	b	0x10000202c <__ZN4core3ffi5c_str4CStr6to_str17he830fa2d0fe61040E+0x228>

0000000100002054 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE>:
100002054:     	stp	x28, x27, [sp, #-0x60]!
100002058:     	stp	x26, x25, [sp, #0x10]
10000205c:     	stp	x24, x23, [sp, #0x20]
100002060:     	stp	x22, x21, [sp, #0x30]
100002064:     	stp	x20, x19, [sp, #0x40]
100002068:     	stp	x29, x30, [sp, #0x50]
10000206c:     	add	x29, sp, #0x50
100002070:     	sub	sp, sp, #0x620
100002074:     	str	xzr, [sp]
100002078:     	cbz	x2, 0x100002134 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xe0>
10000207c:     	ldrb	w23, [x1]
100002080:     	cmp	w23, #0x2d
100002084:     	b.eq	0x100002090 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3c>
100002088:     	cmp	w23, #0x2b
10000208c:     	b.ne	0x10000209c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x48>
100002090:     	subs	x2, x2, #0x1
100002094:     	b.eq	0x1000026fc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6a8>
100002098:     	add	x1, x1, #0x1
10000209c:     	cmp	x2, #0x8
1000020a0:     	b.lo	0x100002140 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xec>
1000020a4:     	mov	x19, #0x0               ; =0
1000020a8:     	mov	x10, #-0x3030303030303031 ; =-3472328296227680305
1000020ac:     	movk	x10, #0xcfd0
1000020b0:     	mov	x11, #0x606060606060606 ; =434041037028460038
1000020b4:     	orr	x11, x11, #0x4444444444444444
1000020b8:     	mov	x12, #0x64              ; =100
1000020bc:     	movk	x12, #0x4240, lsl #32
1000020c0:     	movk	x12, #0xf, lsl #48
1000020c4:     	mov	x13, #0x1               ; =1
1000020c8:     	movk	x13, #0x2710, lsl #32
1000020cc:     	mov	w14, #0xe100            ; =57600
1000020d0:     	movk	w14, #0x5f5, lsl #16
1000020d4:     	mov	w15, #0xa               ; =10
1000020d8:     	mov	x8, x1
1000020dc:     	mov	x9, x2
1000020e0:     	ldr	x16, [x8]
1000020e4:     	add	x17, x16, x11
1000020e8:     	add	x16, x16, x10
1000020ec:     	orr	x17, x17, x16
1000020f0:     	tst	x17, #0x8080808080808080
1000020f4:     	b.ne	0x10000214c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xf8>
1000020f8:     	mul	x17, x19, x14
1000020fc:     	mul	x3, x16, x15
100002100:     	add	x16, x3, x16, lsr #8
100002104:     	and	x3, x16, #0xff000000ff
100002108:     	mul	x3, x3, x12
10000210c:     	lsr	x16, x16, #16
100002110:     	and	x16, x16, #0xff000000ff
100002114:     	madd	x16, x16, x13, x3
100002118:     	add	x19, x17, x16, lsr #32
10000211c:     	sub	x9, x9, #0x8
100002120:     	add	x8, x8, #0x8
100002124:     	cmp	x9, #0x7
100002128:     	b.hi	0x1000020e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8c>
10000212c:     	cbnz	x9, 0x10000214c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xf8>
100002130:     	b	0x100002178 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x124>
100002134:     	strb	wzr, [x0, #0x1]
100002138:     	mov	w8, #0x1                ; =1
10000213c:     	b	0x1000029b0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x95c>
100002140:     	mov	x19, #0x0               ; =0
100002144:     	mov	x9, x2
100002148:     	mov	x8, x1
10000214c:     	mov	x10, #0x0               ; =0
100002150:     	mov	w11, #0xa               ; =10
100002154:     	ldrb	w12, [x8, x10]
100002158:     	sub	w13, w12, #0x30
10000215c:     	cmp	w13, #0x9
100002160:     	b.hi	0x1000021a0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x14c>
100002164:     	mul	x12, x19, x11
100002168:     	add	x19, x12, w13, uxtb
10000216c:     	add	x10, x10, #0x1
100002170:     	cmp	x9, x10
100002174:     	b.ne	0x100002154 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x100>
100002178:     	mov	x8, #0x0                ; =0
10000217c:     	mov	x10, #0x0               ; =0
100002180:     	mov	x20, #0x0               ; =0
100002184:     	mov	w9, #0x1                ; =1
100002188:     	mov	x13, x2
10000218c:     	cmp	x13, #0x14
100002190:     	b.ge	0x100002278 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x224>
100002194:     	mov	w25, #0x0               ; =0
100002198:     	tbnz	w9, #0x0, 0x100002454 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x400>
10000219c:     	b	0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
1000021a0:     	add	x11, x8, x10
1000021a4:     	sub	x8, x9, x10
1000021a8:     	cmp	w12, #0x2e
1000021ac:     	b.ne	0x100002320 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x2cc>
1000021b0:     	mvn	x12, x10
1000021b4:     	add	x12, x12, x9
1000021b8:     	add	x11, x11, #0x1
1000021bc:     	cmp	x12, #0x8
1000021c0:     	b.lo	0x100002240 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x1ec>
1000021c4:     	mov	x13, #-0x3030303030303031 ; =-3472328296227680305
1000021c8:     	movk	x13, #0xcfd0
1000021cc:     	mov	x14, #0x606060606060606 ; =434041037028460038
1000021d0:     	orr	x14, x14, #0x4444444444444444
1000021d4:     	mov	x15, #0x64              ; =100
1000021d8:     	movk	x15, #0x4240, lsl #32
1000021dc:     	movk	x15, #0xf, lsl #48
1000021e0:     	mov	x16, #0x1               ; =1
1000021e4:     	movk	x16, #0x2710, lsl #32
1000021e8:     	mov	w17, #0xe100            ; =57600
1000021ec:     	movk	w17, #0x5f5, lsl #16
1000021f0:     	mov	w3, #0xa                ; =10
1000021f4:     	ldr	x4, [x11]
1000021f8:     	add	x5, x4, x14
1000021fc:     	add	x4, x4, x13
100002200:     	orr	x5, x5, x4
100002204:     	tst	x5, #0x8080808080808080
100002208:     	b.ne	0x100002244 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x1f0>
10000220c:     	mul	x5, x19, x17
100002210:     	mul	x6, x4, x3
100002214:     	add	x4, x6, x4, lsr #8
100002218:     	and	x6, x4, #0xff000000ff
10000221c:     	mul	x6, x6, x15
100002220:     	lsr	x4, x4, #16
100002224:     	and	x4, x4, #0xff000000ff
100002228:     	madd	x4, x4, x16, x6
10000222c:     	add	x19, x5, x4, lsr #32
100002230:     	sub	x12, x12, #0x8
100002234:     	add	x11, x11, #0x8
100002238:     	cmp	x12, #0x7
10000223c:     	b.hi	0x1000021f4 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x1a0>
100002240:     	cbz	x12, 0x100002394 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x340>
100002244:     	mov	x13, x11
100002248:     	add	x11, x11, x12
10000224c:     	mov	w14, #0xa               ; =10
100002250:     	ldrb	w15, [x13]
100002254:     	sub	w15, w15, #0x30
100002258:     	cmp	w15, #0x9
10000225c:     	b.hi	0x100002390 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x33c>
100002260:     	add	x13, x13, #0x1
100002264:     	mul	x16, x19, x14
100002268:     	add	x19, x16, w15, uxtb
10000226c:     	subs	x12, x12, #0x1
100002270:     	b.ne	0x100002250 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x1fc>
100002274:     	b	0x100002394 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x340>
100002278:     	sub	x11, x13, #0x13
10000227c:     	mov	x12, x2
100002280:     	mov	x13, x1
100002284:     	b	0x1000022a0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x24c>
100002288:     	add	x13, x13, #0x1
10000228c:     	subs	w14, w14, #0x2f
100002290:     	csel	w14, wzr, w14, lo
100002294:     	sub	x11, x11, x14
100002298:     	sub	x12, x12, #0x1
10000229c:     	cbz	x12, 0x1000022b4 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x260>
1000022a0:     	ldrb	w14, [x13]
1000022a4:     	cmp	w14, #0x2e
1000022a8:     	b.eq	0x100002288 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x234>
1000022ac:     	cmp	w14, #0x30
1000022b0:     	b.eq	0x100002288 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x234>
1000022b4:     	cmp	x11, #0x1
1000022b8:     	b.lt	0x100002448 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3f4>
1000022bc:     	mov	x19, #0x0               ; =0
1000022c0:     	mov	x12, #-0x589c0001       ; =-1486618625
1000022c4:     	movk	x12, #0xb6b3, lsl #32
1000022c8:     	movk	x12, #0xde0, lsl #48
1000022cc:     	neg	x14, x2
1000022d0:     	mov	w15, #0xa               ; =10
1000022d4:     	mov	x13, x1
1000022d8:     	mov	x16, x14
1000022dc:     	ldrb	w14, [x13]
1000022e0:     	sub	w14, w14, #0x30
1000022e4:     	cmp	w14, #0x9
1000022e8:     	b.hi	0x100002340 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x2ec>
1000022ec:     	add	x13, x13, #0x1
1000022f0:     	mul	x17, x19, x15
1000022f4:     	add	x19, x17, w14, uxtb
1000022f8:     	adds	x14, x16, #0x1
1000022fc:     	cset	w17, hs
100002300:     	cmp	x19, x12
100002304:     	ccmp	w17, #0x0, #0x0, ls
100002308:     	b.eq	0x1000022d8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x284>
10000230c:     	cmp	x19, x12
100002310:     	b.ls	0x10000241c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3c8>
100002314:     	neg	x8, x8
100002318:     	sub	x8, x8, x14
10000231c:     	b	0x100002444 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3f0>
100002320:     	mov	x20, #0x0               ; =0
100002324:     	mov	x13, #0x0               ; =0
100002328:     	mov	x12, x8
10000232c:     	sub	x9, x2, x9
100002330:     	add	x10, x13, x10
100002334:     	adds	x13, x10, x9
100002338:     	b.ne	0x1000023bc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x368>
10000233c:     	b	0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
100002340:     	neg	x8, x16
100002344:     	subs	x8, x8, #0x1
100002348:     	b.eq	0x100002430 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3dc>
10000234c:     	add	x13, x13, #0x1
100002350:     	mov	w14, #0xa               ; =10
100002354:     	mov	x15, x8
100002358:     	ldrb	w16, [x13]
10000235c:     	sub	w17, w16, #0x30
100002360:     	cmp	w17, #0x9
100002364:     	b.hi	0x10000243c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3e8>
100002368:     	sub	x16, x15, #0x1
10000236c:     	add	x13, x13, #0x1
100002370:     	mul	x3, x19, x14
100002374:     	add	x19, x3, w17, uxtb
100002378:     	cmp	x19, x12
10000237c:     	ccmp	x15, #0x1, #0x4, ls
100002380:     	mov	x15, x16
100002384:     	b.ne	0x100002358 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x304>
100002388:     	sub	x8, x16, x8
10000238c:     	b	0x100002444 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3f0>
100002390:     	mov	x11, x13
100002394:     	mvn	x13, x10
100002398:     	sub	x14, x9, x12
10000239c:     	add	x13, x13, x14
1000023a0:     	sub	x14, x12, x9
1000023a4:     	add	x14, x14, x10
1000023a8:     	add	x20, x14, #0x1
1000023ac:     	sub	x9, x2, x9
1000023b0:     	add	x10, x13, x10
1000023b4:     	adds	x13, x10, x9
1000023b8:     	b.eq	0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
1000023bc:     	cbz	x12, 0x100002404 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3b0>
1000023c0:     	ldrb	w9, [x11]
1000023c4:     	orr	w9, w9, #0x20
1000023c8:     	cmp	w9, #0x65
1000023cc:     	b.ne	0x100002410 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3bc>
1000023d0:     	subs	x9, x12, #0x1
1000023d4:     	b.eq	0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
1000023d8:     	mov	x14, x11
1000023dc:     	ldrb	w10, [x14, #0x1]!
1000023e0:     	cmp	w10, #0x2d
1000023e4:     	b.eq	0x1000023f0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x39c>
1000023e8:     	cmp	w10, #0x2b
1000023ec:     	b.ne	0x100002628 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x5d4>
1000023f0:     	subs	x9, x12, #0x2
1000023f4:     	b.eq	0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
1000023f8:     	ldrb	w12, [x11, #0x2]!
1000023fc:     	mov	x14, x11
100002400:     	b	0x10000262c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x5d8>
100002404:     	mov	x10, #0x0               ; =0
100002408:     	mov	w9, #0x1                ; =1
10000240c:     	b	0x10000218c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x138>
100002410:     	mov	w9, #0x0                ; =0
100002414:     	mov	x10, #0x0               ; =0
100002418:     	b	0x10000218c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x138>
10000241c:     	cmn	x16, #0x1
100002420:     	b.eq	0x100002bd0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb7c>
100002424:     	neg	x8, x14
100002428:     	subs	x8, x8, #0x1
10000242c:     	b.ne	0x10000234c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x2f8>
100002430:     	mov	x16, #0x0               ; =0
100002434:     	neg	x8, x8
100002438:     	b	0x100002444 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x3f0>
10000243c:     	mov	x16, x15
100002440:     	sub	x8, x15, x8
100002444:     	add	x20, x8, x10
100002448:     	cmp	x11, #0x0
10000244c:     	cset	w25, gt
100002450:     	tbz	w9, #0x0, 0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
100002454:     	add	x8, x20, #0x16
100002458:     	cmp	x8, #0x3b
10000245c:     	b.hi	0x1000024e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x48c>
100002460:     	cbnz	w25, 0x1000024e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x48c>
100002464:     	mov	x8, #0x20000000000000   ; =9007199254740992
100002468:     	cmp	x19, x8
10000246c:     	b.hi	0x1000024e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x48c>
100002470:     	cmp	x20, #0x16
100002474:     	b.gt	0x100002494 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x440>
100002478:     	ucvtf	d0, x19
10000247c:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100002480:     	add	x8, x8, #0xe78
100002484:     	tbnz	x20, #0x3f, 0x100002728 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6d4>
100002488:     	ldr	d1, [x8, x20, lsl #3]
10000248c:     	fmul	d0, d1, d0
100002490:     	b	0x100002710 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6bc>
100002494:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
100002498:     	add	x8, x8, #0xf78
10000249c:     	add	x8, x8, x20, lsl #3
1000024a0:     	ldur	x8, [x8, #-0xb0]
1000024a4:     	umulh	x9, x19, x8
1000024a8:     	cmp	xzr, x9
1000024ac:     	b.ne	0x1000024e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x48c>
1000024b0:     	mul	x8, x19, x8
1000024b4:     	mov	x9, #0x20000000000000   ; =9007199254740992
1000024b8:     	cmp	x8, x9
1000024bc:     	b.hi	0x1000024e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x48c>
1000024c0:     	ucvtf	d0, x8
1000024c4:     	mov	x8, #0xd592             ; =54674
1000024c8:     	movk	x8, #0x64d, lsl #16
1000024cc:     	movk	x8, #0xf0cf, lsl #32
1000024d0:     	movk	x8, #0x4480, lsl #48
1000024d4:     	fmov	d1, x8
1000024d8:     	fmul	d0, d0, d1
1000024dc:     	b	0x100002710 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6bc>
1000024e0:     	mov	x27, x2
1000024e4:     	mov	x26, x1
1000024e8:     	mov	x24, x0
1000024ec:     	mov	x0, x20
1000024f0:     	mov	x1, x19
1000024f4:     	bl	0x100002bd4 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E>
1000024f8:     	mov	x22, x0
1000024fc:     	mov	x21, x1
100002500:     	cbz	w25, 0x100002528 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x4d4>
100002504:     	tbnz	w21, #0x1f, 0x100002528 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x4d4>
100002508:     	add	x1, x19, #0x1
10000250c:     	mov	x0, x20
100002510:     	bl	0x100002bd4 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E>
100002514:     	cmp	x22, x0
100002518:     	b.ne	0x10000252c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x4d8>
10000251c:     	cmp	w21, w1
100002520:     	b.eq	0x100002990 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x93c>
100002524:     	b	0x10000252c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x4d8>
100002528:     	tbz	w21, #0x1f, 0x100002990 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x93c>
10000252c:     	add	x8, sp, #0x310
100002530:     	add	x19, x8, #0x8
100002534:     	add	x0, sp, #0x310
100002538:     	mov	w1, #0x30d              ; =781
10000253c:     	bl	0x100005834 <_write+0x100005834>
100002540:     	mov	x15, #0x0               ; =0
100002544:     	mov	x9, x26
100002548:     	mov	x10, x27
10000254c:     	add	x14, x26, x27
100002550:     	ldrb	w12, [x9, x15]
100002554:     	subs	w16, w12, #0x30
100002558:     	b.ne	0x100002570 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x51c>
10000255c:     	add	x15, x15, #0x1
100002560:     	cmp	x10, x15
100002564:     	b.ne	0x100002550 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x4fc>
100002568:     	mov	x9, #0x0                ; =0
10000256c:     	b	0x100002940 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8ec>
100002570:     	cmp	w16, #0x9
100002574:     	b.hi	0x1000025e0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x58c>
100002578:     	mov	x12, #0x0               ; =0
10000257c:     	sub	x8, x10, #0x1
100002580:     	add	x11, x9, #0x1
100002584:     	mov	x13, x15
100002588:     	cmp	x12, #0x2ff
10000258c:     	b.hi	0x100002598 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x544>
100002590:     	strb	w16, [x19, x12]
100002594:     	ldr	x12, [sp, #0x310]
100002598:     	add	x12, x12, #0x1
10000259c:     	str	x12, [sp, #0x310]
1000025a0:     	cmp	x8, x13
1000025a4:     	b.eq	0x100002738 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6e4>
1000025a8:     	ldrb	w17, [x11, x13]
1000025ac:     	sub	w16, w17, #0x30
1000025b0:     	add	x15, x13, #0x1
1000025b4:     	cmp	w16, #0x9
1000025b8:     	b.ls	0x100002584 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x530>
1000025bc:     	sub	x11, x10, x15
1000025c0:     	add	x8, x9, #0x1
1000025c4:     	cmp	w17, #0x2e
1000025c8:     	b.ne	0x100002748 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6f4>
1000025cc:     	sub	x13, x11, #0x1
1000025d0:     	add	x8, x8, x15
1000025d4:     	mov	x11, x13
1000025d8:     	cbnz	x12, 0x100002768 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x714>
1000025dc:     	b	0x1000025f8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x5a4>
1000025e0:     	add	x8, x9, x15
1000025e4:     	sub	x11, x10, x15
1000025e8:     	cmp	w12, #0x2e
1000025ec:     	b.ne	0x100002834 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7e0>
1000025f0:     	add	x8, x8, #0x1
1000025f4:     	sub	x13, x11, #0x1
1000025f8:     	cbz	x13, 0x100002750 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6fc>
1000025fc:     	mov	x11, #0x0               ; =0
100002600:     	ldrb	w12, [x8, x11]
100002604:     	cmp	w12, #0x30
100002608:     	b.ne	0x10000275c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x708>
10000260c:     	add	x11, x11, #0x1
100002610:     	cmp	x13, x11
100002614:     	b.ne	0x100002600 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x5ac>
100002618:     	mov	x12, #0x0               ; =0
10000261c:     	mov	x11, #0x0               ; =0
100002620:     	mov	x8, x14
100002624:     	b	0x100002810 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7bc>
100002628:     	mov	x12, x10
10000262c:     	sub	w11, w12, #0x30
100002630:     	cmp	w11, #0x9
100002634:     	b.hi	0x10000268c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x638>
100002638:     	mov	x11, #0x0               ; =0
10000263c:     	mov	x12, #0x0               ; =0
100002640:     	mov	w15, #0xa               ; =10
100002644:     	ldrb	w16, [x14]
100002648:     	sub	w16, w16, #0x30
10000264c:     	cmp	w16, #0x9
100002650:     	b.hi	0x100002674 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x620>
100002654:     	add	x14, x14, #0x1
100002658:     	mul	x17, x12, x15
10000265c:     	add	x16, x17, w16, uxtb
100002660:     	cmp	x12, #0x10, lsl #12     ; =0x10000
100002664:     	csel	x11, x16, x11, lt
100002668:     	csel	x12, x16, x12, lt
10000266c:     	sub	x9, x9, #0x1
100002670:     	cbnz	x9, 0x100002644 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x5f0>
100002674:     	cmp	w10, #0x2d
100002678:     	cneg	x10, x11, eq
10000267c:     	add	x20, x10, x20
100002680:     	cmp	x9, #0x0
100002684:     	cset	w9, eq
100002688:     	b	0x10000218c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x138>
10000268c:     	cmp	x2, #0x3
100002690:     	b.eq	0x1000026c0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x66c>
100002694:     	cmp	x2, #0x8
100002698:     	b.ne	0x1000026fc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6a8>
10000269c:     	ldr	x8, [x1]
1000026a0:     	and	x8, x8, #0xdfdfdfdfdfdfdfdf
1000026a4:     	mov	x9, #0x4e49             ; =20041
1000026a8:     	movk	x9, #0x4946, lsl #16
1000026ac:     	movk	x9, #0x494e, lsl #32
1000026b0:     	movk	x9, #0x5954, lsl #48
1000026b4:     	cmp	x8, x9
1000026b8:     	b.eq	0x100002708 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6b4>
1000026bc:     	b	0x1000026fc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6a8>
1000026c0:     	ldrb	w8, [x1, #0x2]
1000026c4:     	ldrh	w9, [x1]
1000026c8:     	orr	w8, w9, w8, lsl #16
1000026cc:     	mov	w9, #0xdfdf             ; =57311
1000026d0:     	movk	w9, #0xdf, lsl #16
1000026d4:     	and	x8, x8, x9
1000026d8:     	sub	x9, x8, #0x464, lsl #12 ; =0x464000
1000026dc:     	cmp	x9, #0xe49
1000026e0:     	b.eq	0x100002708 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6b4>
1000026e4:     	mov	w9, #0x414e             ; =16718
1000026e8:     	movk	w9, #0x4e, lsl #16
1000026ec:     	cmp	x8, x9
1000026f0:     	b.ne	0x1000026fc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6a8>
1000026f4:     	mov	x8, #0x7ff8000000000000 ; =9221120237041090560
1000026f8:     	b	0x10000270c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6b8>
1000026fc:     	mov	w8, #0x1                ; =1
100002700:     	strb	w8, [x0, #0x1]
100002704:     	b	0x1000029b0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x95c>
100002708:     	mov	x8, #0x7ff0000000000000 ; =9218868437227405312
10000270c:     	fmov	d0, x8
100002710:     	mov	w8, #0x0                ; =0
100002714:     	fneg	d1, d0
100002718:     	cmp	w23, #0x2d
10000271c:     	fcsel	d0, d1, d0, eq
100002720:     	str	d0, [x0, #0x8]
100002724:     	b	0x1000029b0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x95c>
100002728:     	sub	x8, x8, x20, lsl #3
10000272c:     	ldr	d1, [x8]
100002730:     	fdiv	d0, d0, d1
100002734:     	b	0x100002710 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x6bc>
100002738:     	mov	x11, #0x0               ; =0
10000273c:     	add	x8, x9, x13
100002740:     	add	x8, x8, #0x1
100002744:     	b	0x100002818 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7c4>
100002748:     	add	x8, x8, x13
10000274c:     	b	0x100002818 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7c4>
100002750:     	mov	x12, #0x0               ; =0
100002754:     	mov	x11, #0x0               ; =0
100002758:     	b	0x100002810 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7bc>
10000275c:     	mov	x12, #0x0               ; =0
100002760:     	add	x8, x8, x11
100002764:     	sub	x11, x13, x11
100002768:     	cmp	x11, #0x8
10000276c:     	b.lo	0x1000027cc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x778>
100002770:     	mov	x14, #-0x3030303030303031 ; =-3472328296227680305
100002774:     	movk	x14, #0xcfd0
100002778:     	mov	x15, #0x606060606060606 ; =434041037028460038
10000277c:     	orr	x15, x15, #0x4444444444444444
100002780:     	add	x16, x12, #0x8
100002784:     	cmp	x16, #0x300
100002788:     	b.hs	0x1000027d0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x77c>
10000278c:     	ldr	x16, [x8]
100002790:     	add	x17, x16, x15
100002794:     	add	x16, x16, x14
100002798:     	orr	x17, x17, x16
10000279c:     	tst	x17, #0x8080808080808080
1000027a0:     	b.ne	0x1000027d0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x77c>
1000027a4:     	cmp	x12, #0x301
1000027a8:     	b.hs	0x100002bd0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb7c>
1000027ac:     	str	x16, [x19, x12]
1000027b0:     	ldr	x12, [sp, #0x310]
1000027b4:     	add	x12, x12, #0x8
1000027b8:     	str	x12, [sp, #0x310]
1000027bc:     	sub	x11, x11, #0x8
1000027c0:     	add	x8, x8, #0x8
1000027c4:     	cmp	x11, #0x7
1000027c8:     	b.hi	0x100002780 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x72c>
1000027cc:     	cbz	x11, 0x100002810 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7bc>
1000027d0:     	mov	x14, x8
1000027d4:     	b	0x1000027ec <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x798>
1000027d8:     	add	x12, x12, #0x1
1000027dc:     	str	x12, [sp, #0x310]
1000027e0:     	mov	x14, x8
1000027e4:     	sub	x11, x11, #0x1
1000027e8:     	cbz	x11, 0x100002810 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7bc>
1000027ec:     	ldrb	w15, [x8], #0x1
1000027f0:     	sub	w15, w15, #0x30
1000027f4:     	cmp	w15, #0x9
1000027f8:     	b.hi	0x100002620 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x5cc>
1000027fc:     	cmp	x12, #0x2ff
100002800:     	b.hi	0x1000027d8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x784>
100002804:     	strb	w15, [x19, x12]
100002808:     	ldr	x12, [sp, #0x310]
10000280c:     	b	0x1000027d8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x784>
100002810:     	sub	w13, w11, w13
100002814:     	str	w13, [sp, #0x618]
100002818:     	cbz	x12, 0x100002834 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7e0>
10000281c:     	subs	x13, x10, x11
100002820:     	b.lo	0x100002bd0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb7c>
100002824:     	cmp	x10, x11
100002828:     	b.ne	0x10000283c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7e8>
10000282c:     	mov	x10, #0x0               ; =0
100002830:     	b	0x100002868 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x814>
100002834:     	mov	x9, #0x0                ; =0
100002838:     	b	0x100002898 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x844>
10000283c:     	mov	x10, #0x0               ; =0
100002840:     	sub	x9, x9, #0x1
100002844:     	b	0x100002854 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x800>
100002848:     	add	x10, x10, #0x1
10000284c:     	subs	x13, x13, #0x1
100002850:     	b.eq	0x100002868 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x814>
100002854:     	ldrb	w14, [x9, x13]
100002858:     	cmp	w14, #0x2e
10000285c:     	b.eq	0x10000284c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7f8>
100002860:     	cmp	w14, #0x30
100002864:     	b.eq	0x100002848 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x7f4>
100002868:     	ldr	w13, [sp, #0x618]
10000286c:     	sub	x9, x12, x10
100002870:     	add	w10, w10, w9
100002874:     	str	x9, [sp, #0x310]
100002878:     	add	w10, w13, w10
10000287c:     	str	w10, [sp, #0x618]
100002880:     	cmp	x9, #0x300
100002884:     	b.ls	0x100002898 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x844>
100002888:     	mov	w9, #0x1                ; =1
10000288c:     	strb	w9, [sp, #0x61c]
100002890:     	mov	w9, #0x300              ; =768
100002894:     	str	x9, [sp, #0x310]
100002898:     	cbz	x11, 0x100002938 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8e4>
10000289c:     	mov	x12, x8
1000028a0:     	ldrb	w10, [x12], #0x1
1000028a4:     	orr	w10, w10, #0x20
1000028a8:     	cmp	w10, #0x65
1000028ac:     	b.ne	0x100002938 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8e4>
1000028b0:     	sub	x13, x11, #0x1
1000028b4:     	cbz	x13, 0x100002918 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8c4>
1000028b8:     	ldrb	w10, [x12]
1000028bc:     	cmp	w10, #0x2d
1000028c0:     	b.eq	0x1000028cc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x878>
1000028c4:     	cmp	w10, #0x2b
1000028c8:     	b.ne	0x1000028d8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x884>
1000028cc:     	subs	x13, x11, #0x2
1000028d0:     	b.eq	0x100002920 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8cc>
1000028d4:     	add	x12, x8, #0x2
1000028d8:     	mov	w8, #0x0                ; =0
1000028dc:     	mov	w11, #0x0               ; =0
1000028e0:     	mov	w14, #0xa               ; =10
1000028e4:     	ldrb	w15, [x12]
1000028e8:     	sub	w15, w15, #0x30
1000028ec:     	cmp	w15, #0x9
1000028f0:     	b.hi	0x100002924 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8d0>
1000028f4:     	add	x12, x12, #0x1
1000028f8:     	mul	w16, w11, w14
1000028fc:     	add	w15, w16, w15, uxtb
100002900:     	cmp	w11, #0x10, lsl #12     ; =0x10000
100002904:     	csel	w8, w15, w8, lt
100002908:     	csel	w11, w15, w11, lt
10000290c:     	sub	x13, x13, #0x1
100002910:     	cbnz	x13, 0x1000028e4 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x890>
100002914:     	b	0x100002924 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8d0>
100002918:     	mov	w8, #0x0                ; =0
10000291c:     	b	0x10000292c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x8d8>
100002920:     	mov	w8, #0x0                ; =0
100002924:     	cmp	w10, #0x2d
100002928:     	cneg	w8, w8, eq
10000292c:     	ldr	w10, [sp, #0x618]
100002930:     	add	w8, w10, w8
100002934:     	str	w8, [sp, #0x618]
100002938:     	cmp	x9, #0x12
10000293c:     	b.hi	0x100002958 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x904>
100002940:     	add	x8, sp, #0x310
100002944:     	add	x8, x8, x9
100002948:     	mov	w10, #0x13              ; =19
10000294c:     	sub	x1, x10, x9
100002950:     	add	x0, x8, #0x8
100002954:     	bl	0x100005834 <_write+0x100005834>
100002958:     	mov	x0, sp
10000295c:     	add	x1, sp, #0x310
100002960:     	mov	w2, #0x310              ; =784
100002964:     	bl	0x100005840 <_write+0x100005840>
100002968:     	mov	w21, #0x0               ; =0
10000296c:     	ldr	x8, [sp]
100002970:     	cbz	x8, 0x10000298c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x938>
100002974:     	ldr	w8, [sp, #0x308]
100002978:     	cmn	w8, #0x144
10000297c:     	b.lt	0x10000298c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x938>
100002980:     	cmp	w8, #0x135
100002984:     	b.le	0x1000029d4 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x980>
100002988:     	mov	w21, #0x7ff             ; =2047
10000298c:     	mov	x22, #0x0               ; =0
100002990:     	mov	w8, #0x0                ; =0
100002994:     	orr	x9, x22, x21, lsl #52
100002998:     	fmov	d0, x9
10000299c:     	fneg	d1, d0
1000029a0:     	cmp	w23, #0x2d
1000029a4:     	fcsel	d0, d1, d0, eq
1000029a8:     	mov	x0, x24
1000029ac:     	str	d0, [x24, #0x8]
1000029b0:     	strb	w8, [x0]
1000029b4:     	add	sp, sp, #0x620
1000029b8:     	ldp	x29, x30, [sp, #0x50]
1000029bc:     	ldp	x20, x19, [sp, #0x40]
1000029c0:     	ldp	x22, x21, [sp, #0x30]
1000029c4:     	ldp	x24, x23, [sp, #0x20]
1000029c8:     	ldp	x26, x25, [sp, #0x10]
1000029cc:     	ldp	x28, x27, [sp], #0x60
1000029d0:     	ret
1000029d4:     	adrp	x20, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000029d8:     	add	x20, x20, #0xe5e
1000029dc:     	cmp	w8, #0x1
1000029e0:     	b.lt	0x100002a24 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x9d0>
1000029e4:     	mov	w22, #0x0               ; =0
1000029e8:     	cmp	w8, #0x13
1000029ec:     	b.hs	0x1000029f8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x9a4>
1000029f0:     	ldrb	w19, [x20, w8, uxtw]
1000029f4:     	b	0x1000029fc <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x9a8>
1000029f8:     	mov	w19, #0x3c              ; =60
1000029fc:     	mov	x0, sp
100002a00:     	mov	x1, x19
100002a04:     	bl	0x10000133c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E>
100002a08:     	ldr	w8, [sp, #0x308]
100002a0c:     	cmn	w8, #0x800
100002a10:     	b.le	0x100002b2c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xad8>
100002a14:     	add	w22, w22, w19
100002a18:     	cmp	w8, #0x1
100002a1c:     	b.ge	0x1000029e8 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x994>
100002a20:     	b	0x100002a28 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x9d4>
100002a24:     	mov	w22, #0x0               ; =0
100002a28:     	mov	x9, sp
100002a2c:     	add	x21, x9, #0x8
100002a30:     	mov	w25, #0x1               ; =1
100002a34:     	cbz	w8, 0x100002a4c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x9f8>
100002a38:     	neg	w8, w8
100002a3c:     	cmp	w8, #0x13
100002a40:     	b.hs	0x100002a64 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xa10>
100002a44:     	ldrb	w19, [x20, w8, uxtw]
100002a48:     	b	0x100002a68 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xa14>
100002a4c:     	ldrb	w8, [sp, #0x8]
100002a50:     	cmp	w8, #0x4
100002a54:     	b.hi	0x100002a8c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xa38>
100002a58:     	cmp	w8, #0x2
100002a5c:     	cinc	x19, x25, lo
100002a60:     	b	0x100002a68 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xa14>
100002a64:     	mov	w19, #0x3c              ; =60
100002a68:     	mov	x0, sp
100002a6c:     	mov	x1, x19
100002a70:     	bl	0x100000d2c <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE>
100002a74:     	ldr	w8, [sp, #0x308]
100002a78:     	cmp	w8, #0x7ff
100002a7c:     	b.gt	0x100002988 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x934>
100002a80:     	sub	w22, w22, w19
100002a84:     	cmp	w8, #0x1
100002a88:     	b.lt	0x100002a34 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x9e0>
100002a8c:     	sub	w20, w22, #0x1
100002a90:     	cmn	w20, #0x3ff
100002a94:     	b.gt	0x100002ac4 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xa70>
100002a98:     	mov	w22, #-0x3fe            ; =-1022
100002a9c:     	mov	w25, #0x3c              ; =60
100002aa0:     	sub	w8, w22, w20
100002aa4:     	cmp	w8, #0x3c
100002aa8:     	csel	w19, w8, w25, lo
100002aac:     	mov	x0, sp
100002ab0:     	mov	x1, x19
100002ab4:     	bl	0x10000133c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E>
100002ab8:     	add	w20, w19, w20
100002abc:     	cmn	w20, #0x3fe
100002ac0:     	b.lo	0x100002aa0 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xa4c>
100002ac4:     	add	w8, w20, #0x3ff
100002ac8:     	cmp	w8, #0x7fe
100002acc:     	b.gt	0x100002988 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x934>
100002ad0:     	mov	x0, sp
100002ad4:     	mov	w1, #0x35               ; =53
100002ad8:     	bl	0x100000d2c <__ZN4core3num7dec2flt7decimal7Decimal10left_shift17ha03b1c67c20f97cfE>
100002adc:     	ldr	x9, [sp]
100002ae0:     	cbz	x9, 0x100002b34 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xae0>
100002ae4:     	ldr	w8, [sp, #0x308]
100002ae8:     	tbnz	w8, #0x1f, 0x100002b34 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xae0>
100002aec:     	cmp	w8, #0x12
100002af0:     	b.hi	0x100002b90 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb3c>
100002af4:     	mov	x0, #0x0                ; =0
100002af8:     	cbz	w8, 0x100002b40 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xaec>
100002afc:     	mov	x10, #0x0               ; =0
100002b00:     	b	0x100002b10 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xabc>
100002b04:     	add	x10, x10, #0x1
100002b08:     	cmp	x8, x10
100002b0c:     	b.eq	0x100002b40 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xaec>
100002b10:     	add	x11, x0, x0, lsl #2
100002b14:     	lsl	x0, x11, #1
100002b18:     	cmp	x10, x9
100002b1c:     	b.hs	0x100002b04 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xab0>
100002b20:     	ldrb	w11, [x21, x10]
100002b24:     	add	x0, x0, x11
100002b28:     	b	0x100002b04 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xab0>
100002b2c:     	mov	w21, #0x0               ; =0
100002b30:     	b	0x10000298c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x938>
100002b34:     	mov	x22, #0x0               ; =0
100002b38:     	add	w21, w20, #0x3fe
100002b3c:     	b	0x100002990 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x93c>
100002b40:     	cmp	x9, x8
100002b44:     	b.ls	0x100002b88 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb34>
100002b48:     	ldrb	w10, [x21, x8]
100002b4c:     	add	x11, x8, #0x1
100002b50:     	cmp	x11, x9
100002b54:     	b.ne	0x100002b7c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb28>
100002b58:     	cmp	w10, #0x5
100002b5c:     	b.ne	0x100002b7c <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb28>
100002b60:     	ldrb	w9, [sp, #0x30c]
100002b64:     	cbnz	w9, 0x100002b84 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb30>
100002b68:     	cbz	w8, 0x100002b88 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb34>
100002b6c:     	add	x8, x8, x21
100002b70:     	ldurb	w8, [x8, #-0x1]
100002b74:     	tbnz	w8, #0x0, 0x100002b84 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb30>
100002b78:     	b	0x100002b88 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb34>
100002b7c:     	cmp	w10, #0x4
100002b80:     	b.ls	0x100002b88 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb34>
100002b84:     	add	x0, x0, #0x1
100002b88:     	lsr	x8, x0, #53
100002b8c:     	cbz	x8, 0x100002bb4 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0xb60>
100002b90:     	mov	x0, sp
100002b94:     	mov	w1, #0x1                ; =1
100002b98:     	bl	0x10000133c <__ZN4core3num7dec2flt7decimal7Decimal11right_shift17h5df054b371f1bef2E>
100002b9c:     	mov	x0, sp
100002ba0:     	bl	0x100000c68 <__ZN4core3num7dec2flt7decimal7Decimal5round17h758fc841119e2559E>
100002ba4:     	add	w8, w20, #0x400
100002ba8:     	cmp	w8, #0x7fe
100002bac:     	b.gt	0x100002988 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x934>
100002bb0:     	add	w20, w20, #0x1
100002bb4:     	lsr	x8, x0, #52
100002bb8:     	cmp	x8, #0x0
100002bbc:     	mov	w8, #0x3fe              ; =1022
100002bc0:     	cinc	w8, w8, ne
100002bc4:     	add	w21, w8, w20
100002bc8:     	and	x22, x0, #0xfffffffffffff
100002bcc:     	b	0x100002990 <__ZN4core3num7dec2flt60_$LT$impl$u20$core..str..traits..FromStr$u20$for$u20$f64$GT$8from_str17hd68f2af54e8a24deE+0x93c>
100002bd0:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>

0000000100002bd4 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E>:
100002bd4:     	stp	x29, x30, [sp, #-0x10]!
100002bd8:     	mov	x29, sp
100002bdc:     	mov	x9, x1
100002be0:     	mov	x8, #0x0                ; =0
100002be4:     	mov	w1, #0x0                ; =0
100002be8:     	cmn	x0, #0x156
100002bec:     	b.lt	0x100002c68 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x94>
100002bf0:     	cbz	x9, 0x100002c68 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x94>
100002bf4:     	cmp	x0, #0x134
100002bf8:     	b.le	0x100002c08 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x34>
100002bfc:     	mov	x8, #0x0                ; =0
100002c00:     	mov	w1, #0x7ff              ; =2047
100002c04:     	b	0x100002c68 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x94>
100002c08:     	clz	x10, x9
100002c0c:     	lsl	x11, x9, x10
100002c10:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100002c14:     	add	x8, x8, #0x848
100002c18:     	add	x12, x8, x0, lsl #4
100002c1c:     	ldr	x9, [x12, #0x1560]
100002c20:     	mul	x8, x9, x11
100002c24:     	umulh	x9, x9, x11
100002c28:     	mvn	w13, w9
100002c2c:     	tst	x13, #0x1ff
100002c30:     	b.ne	0x100002c4c <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x78>
100002c34:     	mov	w13, #0x1560            ; =5472
100002c38:     	add	x12, x12, x13
100002c3c:     	ldr	x12, [x12, #0x8]
100002c40:     	umulh	x11, x12, x11
100002c44:     	adds	x8, x11, x8
100002c48:     	cinc	x9, x9, hs
100002c4c:     	add	x11, x0, #0x1b
100002c50:     	cmp	x11, #0x53
100002c54:     	b.lo	0x100002c74 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0xa0>
100002c58:     	cmn	x8, #0x1
100002c5c:     	b.ne	0x100002c74 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0xa0>
100002c60:     	mov	x8, #0x0                ; =0
100002c64:     	mov	w1, #-0x1               ; =-1
100002c68:     	mov	x0, x8
100002c6c:     	ldp	x29, x30, [sp], #0x10
100002c70:     	ret
100002c74:     	lsr	x13, x9, #63
100002c78:     	add	x12, x13, #0x9
100002c7c:     	lsr	x11, x9, x12
100002c80:     	mov	w14, #0x526a            ; =21098
100002c84:     	movk	w14, #0x3, lsl #16
100002c88:     	mul	w14, w0, w14
100002c8c:     	sub	w10, w13, w10
100002c90:     	add	w10, w10, w14, asr #16
100002c94:     	add	w10, w10, #0x3f
100002c98:     	cmn	w10, #0x3fe
100002c9c:     	b.ge	0x100002cb4 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0xe0>
100002ca0:     	cmn	w10, #0x43d
100002ca4:     	b.hs	0x100002d10 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x13c>
100002ca8:     	mov	w1, #0x0                ; =0
100002cac:     	mov	x8, #0x0                ; =0
100002cb0:     	b	0x100002c68 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x94>
100002cb4:     	and	x13, x11, #0x3
100002cb8:     	lsl	x12, x11, x12
100002cbc:     	cmp	x12, x9
100002cc0:     	ccmp	x13, #0x1, #0x0, eq
100002cc4:     	ccmp	x8, #0x2, #0x2, eq
100002cc8:     	add	x8, x0, #0x4
100002ccc:     	ccmp	x8, #0x1c, #0x2, lo
100002cd0:     	and	x8, x11, #0xfffffffffffffc
100002cd4:     	csel	x8, x8, x11, lo
100002cd8:     	and	x9, x8, #0x1
100002cdc:     	add	x9, x9, x8
100002ce0:     	lsr	x8, x9, #54
100002ce4:     	cmp	x8, #0x0
100002ce8:     	mov	w11, #0x3ff             ; =1023
100002cec:     	cinc	w11, w11, ne
100002cf0:     	add	w1, w11, w10
100002cf4:     	cmp	w1, #0x7fe
100002cf8:     	b.hi	0x100002bfc <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x28>
100002cfc:     	lsr	x9, x9, #1
100002d00:     	and	x9, x9, #0xffefffffffffffff
100002d04:     	cmp	x8, #0x0
100002d08:     	csel	x8, xzr, x9, ne
100002d0c:     	b	0x100002c68 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x94>
100002d10:     	mov	w8, #0x2                ; =2
100002d14:     	sub	w8, w8, w10
100002d18:     	lsr	x8, x11, x8
100002d1c:     	and	x9, x8, #0x1
100002d20:     	add	x9, x9, x8
100002d24:     	lsr	x8, x9, #1
100002d28:     	lsr	x9, x9, #53
100002d2c:     	cmp	x9, #0x0
100002d30:     	cset	w1, ne
100002d34:     	b	0x100002c68 <__ZN4core3num7dec2flt6lemire13compute_float17h638db1ab34f11579E+0x94>

0000000100002d38 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E>:
100002d38:     	sub	sp, sp, #0x70
100002d3c:     	stp	x26, x25, [sp, #0x20]
100002d40:     	stp	x24, x23, [sp, #0x30]
100002d44:     	stp	x22, x21, [sp, #0x40]
100002d48:     	stp	x20, x19, [sp, #0x50]
100002d4c:     	stp	x29, x30, [sp, #0x60]
100002d50:     	add	x29, sp, #0x60
100002d54:     	mov	x2, x1
100002d58:     	mov	x19, x0
100002d5c:     	ldr	x8, [x0]
100002d60:     	cbz	x8, 0x100002d98 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x60>
100002d64:     	ldr	x22, [x19, #0x8]
100002d68:     	ldp	x1, x21, [x2]
100002d6c:     	ldp	x25, x26, [x2, #0x10]
100002d70:     	stp	x1, x21, [sp]
100002d74:     	stp	x25, x26, [sp, #0x10]
100002d78:     	ldr	w23, [x19, #0x30]
100002d7c:     	ldrb	w24, [x19, #0x38]
100002d80:     	ldrb	w8, [x19, #0x34]
100002d84:     	tbnz	w8, #0x3, 0x100002db8 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x80>
100002d88:     	mov	x20, x23
100002d8c:     	mov	x8, x24
100002d90:     	cbnz	x26, 0x100002df0 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0xb8>
100002d94:     	b	0x100002e64 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x12c>
100002d98:     	ldp	x0, x1, [x19, #0x20]
100002d9c:     	ldp	x29, x30, [sp, #0x60]
100002da0:     	ldp	x20, x19, [sp, #0x50]
100002da4:     	ldp	x22, x21, [sp, #0x40]
100002da8:     	ldp	x24, x23, [sp, #0x30]
100002dac:     	ldp	x26, x25, [sp, #0x20]
100002db0:     	add	sp, sp, #0x70
100002db4:     	b	0x100002f50 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E>
100002db8:     	ldp	x0, x8, [x19, #0x20]
100002dbc:     	ldr	x8, [x8, #0x18]
100002dc0:     	mov	x2, x21
100002dc4:     	blr	x8
100002dc8:     	tbnz	w0, #0x0, 0x100002eec <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1b4>
100002dcc:     	mov	w8, #0x1                ; =1
100002dd0:     	stp	x8, xzr, [sp]
100002dd4:     	subs	x9, x22, x21
100002dd8:     	csel	x22, xzr, x9, lo
100002ddc:     	mov	w20, #0x30              ; =48
100002de0:     	str	w20, [x19, #0x30]
100002de4:     	strb	w8, [x19, #0x38]
100002de8:     	mov	x21, #0x0               ; =0
100002dec:     	cbz	x26, 0x100002e64 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x12c>
100002df0:     	add	x10, x26, x26, lsl #1
100002df4:     	add	x9, x25, #0x8
100002df8:     	lsl	x10, x10, #3
100002dfc:     	mov	w11, #0x1               ; =1
100002e00:     	mov	w12, #0x2               ; =2
100002e04:     	mov	w13, #0x4               ; =4
100002e08:     	b	0x100002e20 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0xe8>
100002e0c:     	ldr	x14, [x9]
100002e10:     	add	x21, x14, x21
100002e14:     	add	x9, x9, #0x18
100002e18:     	subs	x10, x10, #0x18
100002e1c:     	b.eq	0x100002e64 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x12c>
100002e20:     	ldurh	w14, [x9, #-0x8]
100002e24:     	cbz	w14, 0x100002e0c <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0xd4>
100002e28:     	cmp	w14, #0x1
100002e2c:     	b.ne	0x100002e5c <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x124>
100002e30:     	ldurh	w14, [x9, #-0x6]
100002e34:     	cmp	w14, #0x64
100002e38:     	cinc	x15, x12, hs
100002e3c:     	cmp	w14, #0xa
100002e40:     	csel	x15, x11, x15, lo
100002e44:     	lsr	w16, w14, #4
100002e48:     	cmp	w16, #0x271
100002e4c:     	cinc	x16, x13, hs
100002e50:     	cmp	w14, #0x3e8
100002e54:     	csel	x14, x15, x16, lo
100002e58:     	b	0x100002e10 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0xd8>
100002e5c:     	ldr	x14, [x9, #0x8]
100002e60:     	b	0x100002e10 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0xd8>
100002e64:     	subs	x25, x22, x21
100002e68:     	b.ls	0x100002e80 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x148>
100002e6c:     	cmp	w8, #0x1
100002e70:     	b.gt	0x100002e90 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x158>
100002e74:     	cbnz	w8, 0x100002ea8 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x170>
100002e78:     	mov	w8, w8
100002e7c:     	b	0x100002eb0 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x178>
100002e80:     	ldp	x0, x1, [x19, #0x20]
100002e84:     	mov	x2, sp
100002e88:     	bl	0x100002f50 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E>
100002e8c:     	b	0x100002f2c <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1f4>
100002e90:     	cmp	w8, #0x2
100002e94:     	b.ne	0x100002ea8 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x170>
100002e98:     	lsr	x8, x25, #1
100002e9c:     	add	x9, x25, #0x1
100002ea0:     	lsr	x25, x9, #1
100002ea4:     	b	0x100002eb0 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x178>
100002ea8:     	mov	x8, x25
100002eac:     	mov	x25, #0x0               ; =0
100002eb0:     	ldp	x21, x22, [x19, #0x20]
100002eb4:     	add	x26, x8, #0x1
100002eb8:     	subs	x26, x26, #0x1
100002ebc:     	b.eq	0x100002ed8 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1a0>
100002ec0:     	ldr	x8, [x22, #0x20]
100002ec4:     	mov	x0, x21
100002ec8:     	mov	x1, x20
100002ecc:     	blr	x8
100002ed0:     	tbz	w0, #0x0, 0x100002eb8 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x180>
100002ed4:     	b	0x100002eec <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1b4>
100002ed8:     	mov	x2, sp
100002edc:     	mov	x0, x21
100002ee0:     	mov	x1, x22
100002ee4:     	bl	0x100002f50 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E>
100002ee8:     	tbz	w0, #0x0, 0x100002ef4 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1bc>
100002eec:     	mov	w0, #0x1                ; =1
100002ef0:     	b	0x100002f34 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1fc>
100002ef4:     	mov	x26, #0x0               ; =0
100002ef8:     	cmp	x25, x26
100002efc:     	b.eq	0x100002f20 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1e8>
100002f00:     	add	x26, x26, #0x1
100002f04:     	ldr	x8, [x22, #0x20]
100002f08:     	mov	x0, x21
100002f0c:     	mov	x1, x20
100002f10:     	blr	x8
100002f14:     	cbz	w0, 0x100002ef8 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1c0>
100002f18:     	sub	x8, x26, #0x1
100002f1c:     	b	0x100002f24 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E+0x1ec>
100002f20:     	mov	x8, x25
100002f24:     	cmp	x8, x25
100002f28:     	cset	w0, lo
100002f2c:     	str	w23, [x19, #0x30]
100002f30:     	strb	w24, [x19, #0x38]
100002f34:     	ldp	x29, x30, [sp, #0x60]
100002f38:     	ldp	x20, x19, [sp, #0x50]
100002f3c:     	ldp	x22, x21, [sp, #0x40]
100002f40:     	ldp	x24, x23, [sp, #0x30]
100002f44:     	ldp	x26, x25, [sp, #0x20]
100002f48:     	add	sp, sp, #0x70
100002f4c:     	ret

0000000100002f50 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E>:
100002f50:     	sub	sp, sp, #0x70
100002f54:     	stp	x28, x27, [sp, #0x10]
100002f58:     	stp	x26, x25, [sp, #0x20]
100002f5c:     	stp	x24, x23, [sp, #0x30]
100002f60:     	stp	x22, x21, [sp, #0x40]
100002f64:     	stp	x20, x19, [sp, #0x50]
100002f68:     	stp	x29, x30, [sp, #0x60]
100002f6c:     	add	x29, sp, #0x60
100002f70:     	mov	x21, x2
100002f74:     	mov	x19, x1
100002f78:     	mov	x20, x0
100002f7c:     	ldr	x2, [x2, #0x8]
100002f80:     	cbz	x2, 0x100002fa0 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x50>
100002f84:     	ldr	x1, [x21]
100002f88:     	ldr	x8, [x19, #0x18]
100002f8c:     	mov	x0, x20
100002f90:     	blr	x8
100002f94:     	tbz	w0, #0x0, 0x100002fa0 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x50>
100002f98:     	mov	w0, #0x1                ; =1
100002f9c:     	b	0x100003190 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x240>
100002fa0:     	ldr	x9, [x21, #0x18]
100002fa4:     	cbz	x9, 0x10000318c <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x23c>
100002fa8:     	ldr	x8, [x21, #0x10]
100002fac:     	mov	w10, #0x18              ; =24
100002fb0:     	adrp	x21, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100002fb4:     	add	x21, x21, #0x704
100002fb8:     	madd	x23, x9, x10, x8
100002fbc:     	mov	w24, #0x1               ; =1
100002fc0:     	add	x27, sp, #0x8
100002fc4:     	mov	w25, #0x199a            ; =6554
100002fc8:     	mov	w26, #0xa               ; =10
100002fcc:     	mov	x28, x8
100002fd0:     	b	0x100002ff4 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0xa4>
100002fd4:     	ldr	x8, [x19, #0x18]
100002fd8:     	add	x1, sp, #0x8
100002fdc:     	mov	x0, x20
100002fe0:     	blr	x8
100002fe4:     	tbnz	w0, #0x0, 0x100002f98 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x48>
100002fe8:     	mov	x8, x28
100002fec:     	cmp	x28, x23
100002ff0:     	b.eq	0x10000318c <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x23c>
100002ff4:     	ldrh	w9, [x28], #0x18
100002ff8:     	cbz	w9, 0x100003104 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x1b4>
100002ffc:     	cmp	w9, #0x1
100003000:     	b.ne	0x100003150 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x200>
100003004:     	ldrh	w10, [x8, #0x2]
100003008:     	strb	wzr, [sp, #0xc]
10000300c:     	str	wzr, [sp, #0x8]
100003010:     	cmp	w10, #0x64
100003014:     	mov	w8, #0x2                ; =2
100003018:     	cinc	x8, x8, hs
10000301c:     	cmp	w10, #0xa
100003020:     	csel	x9, x24, x8, lo
100003024:     	lsr	w8, w10, #4
100003028:     	cmp	w8, #0x271
10000302c:     	mov	w11, #0x4               ; =4
100003030:     	cinc	x11, x11, hs
100003034:     	cmp	w10, #0x3e8
100003038:     	csel	x2, x9, x11, lo
10000303c:     	add	x9, x27, x2
100003040:     	mov	w11, #0xcccd            ; =52429
100003044:     	mul	w11, w10, w11
100003048:     	lsr	w11, w11, #19
10000304c:     	mov	w12, #0xf6              ; =246
100003050:     	madd	w12, w11, w12, w10
100003054:     	orr	w12, w12, #0x30
100003058:     	mov	x13, x9
10000305c:     	strb	w12, [x13, #-0x1]!
100003060:     	cmp	x27, x13
100003064:     	b.eq	0x100002fd4 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x84>
100003068:     	mul	w12, w11, w25
10000306c:     	lsr	w12, w12, #16
100003070:     	msub	w11, w12, w26, w11
100003074:     	orr	w11, w11, #0x30
100003078:     	mov	x12, x9
10000307c:     	strb	w11, [x12, #-0x2]!
100003080:     	cmp	x27, x12
100003084:     	b.eq	0x100002fd4 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x84>
100003088:     	lsr	w11, w10, #2
10000308c:     	mov	w12, #0x147b            ; =5243
100003090:     	mul	w11, w11, w12
100003094:     	lsr	w11, w11, #17
100003098:     	mul	w12, w11, w25
10000309c:     	lsr	w12, w12, #16
1000030a0:     	msub	w11, w12, w26, w11
1000030a4:     	orr	w11, w11, #0x30
1000030a8:     	mov	x12, x9
1000030ac:     	strb	w11, [x12, #-0x3]!
1000030b0:     	cmp	x27, x12
1000030b4:     	b.eq	0x100002fd4 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x84>
1000030b8:     	lsr	w10, w10, #3
1000030bc:     	mov	w11, #0x20c5            ; =8389
1000030c0:     	mul	w10, w10, w11
1000030c4:     	lsr	w10, w10, #20
1000030c8:     	mov	w11, #0x67              ; =103
1000030cc:     	mul	w11, w10, w11
1000030d0:     	lsr	w11, w11, #10
1000030d4:     	msub	w10, w11, w26, w10
1000030d8:     	orr	w10, w10, #0x30
1000030dc:     	mov	x11, x9
1000030e0:     	strb	w10, [x11, #-0x4]!
1000030e4:     	cmp	x27, x11
1000030e8:     	b.eq	0x100002fd4 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x84>
1000030ec:     	mov	w10, #0x347             ; =839
1000030f0:     	mul	w8, w8, w10
1000030f4:     	lsr	w8, w8, #19
1000030f8:     	orr	w8, w8, #0x30
1000030fc:     	sturb	w8, [x9, #-0x5]
100003100:     	b	0x100002fd4 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x84>
100003104:     	ldr	x22, [x8, #0x8]
100003108:     	cmp	x22, #0x41
10000310c:     	b.lo	0x100003168 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x218>
100003110:     	ldr	x24, [x19, #0x18]
100003114:     	mov	x0, x20
100003118:     	mov	x1, x21
10000311c:     	mov	w2, #0x40               ; =64
100003120:     	blr	x24
100003124:     	tbnz	w0, #0x0, 0x100002f98 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x48>
100003128:     	sub	x22, x22, #0x40
10000312c:     	cmp	x22, #0x40
100003130:     	b.hi	0x100003114 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x1c4>
100003134:     	mov	x0, x20
100003138:     	mov	x1, x21
10000313c:     	mov	x2, x22
100003140:     	blr	x24
100003144:     	mov	w24, #0x1               ; =1
100003148:     	tbz	w0, #0x0, 0x100002fe8 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x98>
10000314c:     	b	0x100002f98 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x48>
100003150:     	ldp	x1, x2, [x8, #0x8]
100003154:     	ldr	x8, [x19, #0x18]
100003158:     	mov	x0, x20
10000315c:     	blr	x8
100003160:     	tbz	w0, #0x0, 0x100002fe8 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x98>
100003164:     	b	0x100002f98 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x48>
100003168:     	cbz	x22, 0x100002fe8 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x98>
10000316c:     	ldr	x24, [x19, #0x18]
100003170:     	mov	x0, x20
100003174:     	mov	x1, x21
100003178:     	mov	x2, x22
10000317c:     	blr	x24
100003180:     	mov	w24, #0x1               ; =1
100003184:     	tbz	w0, #0x0, 0x100002fe8 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x98>
100003188:     	b	0x100002f98 <__ZN4core3fmt9Formatter21write_formatted_parts17hf2985baf3c359124E+0x48>
10000318c:     	mov	w0, #0x0                ; =0
100003190:     	ldp	x29, x30, [sp, #0x60]
100003194:     	ldp	x20, x19, [sp, #0x50]
100003198:     	ldp	x22, x21, [sp, #0x40]
10000319c:     	ldp	x24, x23, [sp, #0x30]
1000031a0:     	ldp	x26, x25, [sp, #0x20]
1000031a4:     	ldp	x28, x27, [sp, #0x10]
1000031a8:     	add	sp, sp, #0x70
1000031ac:     	ret

00000001000031b0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E>:
1000031b0:     	stp	x28, x27, [sp, #-0x60]!
1000031b4:     	stp	x26, x25, [sp, #0x10]
1000031b8:     	stp	x24, x23, [sp, #0x20]
1000031bc:     	stp	x22, x21, [sp, #0x30]
1000031c0:     	stp	x20, x19, [sp, #0x40]
1000031c4:     	stp	x29, x30, [sp, #0x50]
1000031c8:     	add	x29, sp, #0x50
1000031cc:     	sub	sp, sp, #0x7a0
1000031d0:     	str	xzr, [sp]
1000031d4:     	mov	x19, x2
1000031d8:     	fmov	x8, d0
1000031dc:     	lsr	x9, x8, #52
1000031e0:     	ands	w11, w9, #0x7ff
1000031e4:     	ubfiz	x9, x8, #1, #52
1000031e8:     	mov	x10, #0x10000000000000  ; =4503599627370496
1000031ec:     	bfxil	x10, x8, #0, #52
1000031f0:     	csel	x22, x9, x10, eq
1000031f4:     	fcmp	d0, d0
1000031f8:     	b.vs	0x1000041a8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff8>
1000031fc:     	and	x12, x22, #0x1
100003200:     	and	x13, x8, #0x7ff0000000000000
100003204:     	and	x9, x8, #0xfffffffffffff
100003208:     	cbz	x9, 0x100003218 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x68>
10000320c:     	cbnz	x13, 0x100003234 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x84>
100003210:     	sub	w9, w11, #0x433
100003214:     	b	0x100003254 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xa4>
100003218:     	mov	x14, #0x7ff0000000000000 ; =9218868437227405312
10000321c:     	cmp	x13, x14
100003220:     	mov	w9, #0x3                ; =3
100003224:     	cinc	w10, w9, ne
100003228:     	cbz	x13, 0x1000034ac <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x2fc>
10000322c:     	cmp	x13, x14
100003230:     	b.eq	0x100003258 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xa8>
100003234:     	lsl	x9, x22, #1
100003238:     	mov	x10, #0x10000000000000  ; =4503599627370496
10000323c:     	mov	x13, #0x40000000000000  ; =18014398509481984
100003240:     	cmp	x22, x10
100003244:     	csel	x22, x13, x9, eq
100003248:     	mov	w9, #-0x435             ; =-1077
10000324c:     	cinc	w9, w9, ne
100003250:     	add	w9, w9, w11
100003254:     	eor	w10, w12, #0x1
100003258:     	adrp	x11, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
10000325c:     	add	x11, x11, #0x634
100003260:     	adrp	x12, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100003264:     	add	x12, x12, #0x633
100003268:     	cmp	x8, #0x0
10000326c:     	csel	x11, x12, x11, lt
100003270:     	mov	w13, #0x1               ; =1
100003274:     	lsr	x14, x8, #63
100003278:     	cmp	x8, #0x0
10000327c:     	csinc	x8, x12, xzr, lt
100003280:     	tst	w1, #0x1
100003284:     	csel	x24, x13, x14, ne
100003288:     	csel	x25, x11, x8, ne
10000328c:     	sub	w8, w10, #0x2
100003290:     	and	w8, w8, #0xff
100003294:     	mov	w10, #0x3               ; =3
100003298:     	cmp	w8, #0x3
10000329c:     	csel	w8, w8, w10, lo
1000032a0:     	cmp	w8, #0x1
1000032a4:     	b.gt	0x1000032bc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x10c>
1000032a8:     	cbnz	w8, 0x100003484 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x2d4>
1000032ac:     	mov	w8, #0x2                ; =2
1000032b0:     	adrp	x9, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000032b4:     	add	x9, x9, #0x635
1000032b8:     	b	0x100003490 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x2e0>
1000032bc:     	cmp	w8, #0x2
1000032c0:     	b.eq	0x1000036c8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x518>
1000032c4:     	sxth	w23, w9
1000032c8:     	cmp	w23, #0x0
1000032cc:     	mov	w8, #0x5                ; =5
1000032d0:     	mov	x10, #-0xc              ; =-12
1000032d4:     	csel	x8, x10, x8, lt
1000032d8:     	sxth	x26, w9
1000032dc:     	mul	x8, x8, x26
1000032e0:     	lsr	x10, x8, #6
1000032e4:     	cmp	x10, #0xfb
1000032e8:     	b.hs	0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
1000032ec:     	cmp	x19, #0x8, lsl #12      ; =0x8000
1000032f0:     	mov	w10, #-0x8000           ; =-32768
1000032f4:     	csneg	w10, w10, w19, hs
1000032f8:     	cbz	x22, 0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
1000032fc:     	lsr	x8, x8, #4
100003300:     	add	x28, x8, #0x15
100003304:     	sxth	w20, w10
100003308:     	lsl	x10, x22, #32
10000330c:     	lsr	x27, x22, #32
100003310:     	sub	w11, w9, #0x20
100003314:     	cmp	x27, #0x0
100003318:     	csel	x10, x10, x22, eq
10000331c:     	lsl	x12, x10, #16
100003320:     	lsr	x13, x10, #48
100003324:     	csel	w9, w11, w9, eq
100003328:     	sub	w11, w9, #0x10
10000332c:     	cmp	x13, #0x0
100003330:     	csel	x10, x12, x10, eq
100003334:     	lsl	x12, x10, #8
100003338:     	lsr	x13, x10, #56
10000333c:     	csel	w9, w11, w9, eq
100003340:     	sub	w11, w9, #0x8
100003344:     	cmp	x13, #0x0
100003348:     	csel	x10, x12, x10, eq
10000334c:     	lsl	x12, x10, #4
100003350:     	lsr	x13, x10, #60
100003354:     	csel	w9, w11, w9, eq
100003358:     	sub	w11, w9, #0x4
10000335c:     	cmp	x13, #0x0
100003360:     	csel	x10, x12, x10, eq
100003364:     	csel	w9, w11, w9, eq
100003368:     	sub	w11, w9, #0x2
10000336c:     	lsr	x12, x10, #62
100003370:     	lsl	x13, x10, #2
100003374:     	cmp	x12, #0x0
100003378:     	csel	x10, x13, x10, eq
10000337c:     	csel	w9, w11, w9, eq
100003380:     	lsr	x11, x10, #63
100003384:     	eor	w11, w11, #0x1
100003388:     	mov	w12, #-0x60             ; =-96
10000338c:     	sub	w9, w9, w11
100003390:     	sub	w12, w12, w9
100003394:     	sxth	w12, w12
100003398:     	mov	w13, #0x50              ; =80
10000339c:     	mov	w14, #0x53b0            ; =21424
1000033a0:     	movk	w14, #0x1, lsl #16
1000033a4:     	madd	w12, w12, w13, w14
1000033a8:     	mov	w13, #0xc993            ; =51603
1000033ac:     	movk	w13, #0x7b4d, lsl #16
1000033b0:     	umull	x12, w12, w13
1000033b4:     	lsl	x11, x10, x11
1000033b8:     	lsr	x10, x12, #38
1000033bc:     	and	x10, x10, #0x1fffff0
1000033c0:     	adrp	x12, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000033c4:     	add	x12, x12, #0xf8
1000033c8:     	add	x10, x12, x10
1000033cc:     	ldr	x12, [x10]
1000033d0:     	ldrh	w13, [x10, #0x8]
1000033d4:     	lsr	x14, x11, #32
1000033d8:     	and	x15, x11, #0xffffffff
1000033dc:     	lsr	x16, x12, #32
1000033e0:     	and	x17, x12, #0xffffffff
1000033e4:     	umull	x15, w16, w15
1000033e8:     	umull	x17, w17, w14
1000033ec:     	umull	x11, w12, w11
1000033f0:     	lsr	x11, x11, #32
1000033f4:     	add	x11, x11, w17, uxtw
1000033f8:     	add	x11, x11, w15, uxtw
1000033fc:     	mov	w12, #-0x80000000       ; =-2147483648
100003400:     	add	x11, x11, x12
100003404:     	lsr	x12, x17, #32
100003408:     	umaddl	x12, w16, w14, x12
10000340c:     	add	x12, x12, x15, lsr #32
100003410:     	add	x12, x12, x11, lsr #32
100003414:     	mov	w11, #-0x40             ; =-64
100003418:     	sub	w9, w11, w9
10000341c:     	sub	w13, w9, w13
100003420:     	mov	w9, #0x1                ; =1
100003424:     	lsl	x7, x9, x13
100003428:     	sub	x9, x7, #0x1
10000342c:     	ands	x6, x12, x9
100003430:     	str	x0, [sp, #0x10]
100003434:     	b.eq	0x10000370c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x55c>
100003438:     	ldrh	w15, [x10, #0xa]
10000343c:     	lsr	x10, x12, x13
100003440:     	lsr	w11, w10, #4
100003444:     	cmp	w11, #0x271
100003448:     	b.hs	0x1000034b0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x300>
10000344c:     	cmp	w10, #0x9
100003450:     	cset	w11, hi
100003454:     	mov	w14, #0xa               ; =10
100003458:     	csinc	w14, w14, wzr, hi
10000345c:     	mov	w16, #0x3e8             ; =1000
100003460:     	mov	w17, #0x64              ; =100
100003464:     	cmp	w10, #0x3e8
100003468:     	csel	w16, w17, w16, lo
10000346c:     	mov	w17, #0x2               ; =2
100003470:     	cinc	w17, w17, hs
100003474:     	cmp	w10, #0x64
100003478:     	csel	w14, w14, w16, lo
10000347c:     	csel	w16, w11, w17, lo
100003480:     	b	0x100003528 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x378>
100003484:     	mov	w8, #0x2                ; =2
100003488:     	adrp	x9, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
10000348c:     	add	x9, x9, #0x638
100003490:     	strh	w8, [sp, #0x6e0]
100003494:     	mov	w8, #0x3                ; =3
100003498:     	str	x9, [sp, #0x6e8]
10000349c:     	str	x8, [sp, #0x6f0]
1000034a0:     	add	x8, sp, #0x6e0
1000034a4:     	mov	w1, #0x1                ; =1
1000034a8:     	b	0x10000416c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xfbc>
1000034ac:     	b	0x100003258 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xa8>
1000034b0:     	mov	w11, #0x4240            ; =16960
1000034b4:     	movk	w11, #0xf, lsl #16
1000034b8:     	lsr	w14, w10, #5
1000034bc:     	mov	w16, #0x86a0            ; =34464
1000034c0:     	movk	w16, #0x1, lsl #16
1000034c4:     	mov	w17, #0x2710            ; =10000
1000034c8:     	cmp	w14, #0xc35
1000034cc:     	csel	w14, w17, w16, lo
1000034d0:     	mov	w16, #0x4               ; =4
1000034d4:     	cinc	w16, w16, hs
1000034d8:     	mov	w17, #0xe100            ; =57600
1000034dc:     	movk	w17, #0x5f5, lsl #16
1000034e0:     	mov	w0, #0x9680             ; =38528
1000034e4:     	movk	w0, #0x98, lsl #16
1000034e8:     	cmp	w10, w0
1000034ec:     	csel	w0, w11, w0, lo
1000034f0:     	mov	w1, #0x6                ; =6
1000034f4:     	cinc	w1, w1, hs
1000034f8:     	mov	w2, #0xca00             ; =51712
1000034fc:     	movk	w2, #0x3b9a, lsl #16
100003500:     	cmp	w10, w2
100003504:     	csel	w2, w17, w2, lo
100003508:     	mov	w3, #0x8                ; =8
10000350c:     	cinc	w3, w3, hs
100003510:     	cmp	w10, w17
100003514:     	csel	w17, w0, w2, lo
100003518:     	csel	w0, w1, w3, lo
10000351c:     	cmp	w10, w11
100003520:     	csel	w14, w14, w17, lo
100003524:     	csel	w16, w16, w0, lo
100003528:     	and	x11, x13, #0x3f
10000352c:     	and	w17, w16, #0xff
100003530:     	sub	w15, w17, w15
100003534:     	add	w15, w15, #0x1
100003538:     	sxth	w4, w15
10000353c:     	subs	w15, w4, w20
100003540:     	b.le	0x1000035b0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x400>
100003544:     	mov	x12, #0x0               ; =0
100003548:     	and	x13, x13, #0xffff
10000354c:     	sxtw	x17, w4
100003550:     	sub	x17, x17, w20, sxtw
100003554:     	sxth	x15, w15
100003558:     	cmp	x17, x28
10000355c:     	csel	x3, x15, x28, lo
100003560:     	and	x15, x16, #0xff
100003564:     	sub	x16, x3, #0x1
100003568:     	add	x17, sp, #0x18
10000356c:     	mov	w0, #0xcccd             ; =52429
100003570:     	movk	w0, #0xcccc, lsl #16
100003574:     	udiv	w1, w10, w14
100003578:     	msub	w10, w1, w14, w10
10000357c:     	add	w1, w1, #0x30
100003580:     	strb	w1, [x17, x12]
100003584:     	cmp	x16, x12
100003588:     	b.eq	0x1000035f8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x448>
10000358c:     	cmp	x15, x12
100003590:     	b.eq	0x100003634 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x484>
100003594:     	umull	x1, w14, w0
100003598:     	lsr	x1, x1, #35
10000359c:     	add	x12, x12, #0x1
1000035a0:     	cmp	w14, #0xa
1000035a4:     	mov	x14, x1
1000035a8:     	b.hs	0x100003574 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x3c4>
1000035ac:     	bl	0x10000581c <__ZN4core9panicking11panic_const23panic_const_div_by_zero17h71be41e2a26e0e82E>
1000035b0:     	mov	x8, #-0x3333333333333334 ; =-3689348814741910324
1000035b4:     	movk	x8, #0xcccd
1000035b8:     	umulh	x8, x12, x8
1000035bc:     	lsr	x6, x8, #3
1000035c0:     	mov	w8, w14
1000035c4:     	lsl	x8, x8, x11
1000035c8:     	str	x7, [sp]
1000035cc:     	add	x0, sp, #0x418
1000035d0:     	add	x1, sp, #0x18
1000035d4:     	mov	x2, x28
1000035d8:     	mov	x3, #0x0                ; =0
1000035dc:     	mov	x5, x20
1000035e0:     	mov	x7, x8
1000035e4:     	bl	0x100001b70 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE>
1000035e8:     	ldr	x8, [sp, #0x418]
1000035ec:     	ldr	x0, [sp, #0x10]
1000035f0:     	cbnz	x8, 0x1000036b4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x504>
1000035f4:     	b	0x100003710 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x560>
1000035f8:     	lsl	x9, x10, x11
1000035fc:     	mov	w8, w14
100003600:     	lsl	x8, x8, x11
100003604:     	str	x7, [sp]
100003608:     	add	x0, sp, #0x418
10000360c:     	add	x1, sp, #0x18
100003610:     	add	x6, x9, x6
100003614:     	mov	x2, x28
100003618:     	mov	x5, x20
10000361c:     	mov	x7, x8
100003620:     	bl	0x100001b70 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE>
100003624:     	ldr	x8, [sp, #0x418]
100003628:     	ldr	x0, [sp, #0x10]
10000362c:     	cbnz	x8, 0x1000036b4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x504>
100003630:     	b	0x100003710 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x560>
100003634:     	sub	w10, w13, #0x1
100003638:     	and	x10, x10, #0x3f
10000363c:     	mov	x13, #-0x14             ; =-20
100003640:     	sub	x13, x13, x8
100003644:     	add	x12, x12, #0x1
100003648:     	mov	w8, #0x1                ; =1
10000364c:     	add	x14, sp, #0x18
100003650:     	lsr	x15, x8, x10
100003654:     	cbnz	x15, 0x10000370c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x55c>
100003658:     	add	x15, x13, x12
10000365c:     	cmp	x15, #0x1
100003660:     	b.eq	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
100003664:     	add	x15, x6, x6, lsl #2
100003668:     	lsl	x15, x15, #1
10000366c:     	and	x6, x15, x9
100003670:     	add	x8, x8, x8, lsl #2
100003674:     	lsl	x8, x8, #1
100003678:     	lsr	x15, x15, x11
10000367c:     	add	w15, w15, #0x30
100003680:     	strb	w15, [x14, x12]
100003684:     	add	x12, x12, #0x1
100003688:     	cmp	x3, x12
10000368c:     	b.ne	0x100003650 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x4a0>
100003690:     	str	x8, [sp]
100003694:     	add	x0, sp, #0x418
100003698:     	add	x1, sp, #0x18
10000369c:     	mov	x2, x28
1000036a0:     	mov	x5, x20
1000036a4:     	bl	0x100001b70 <__ZN4core3num7flt2dec8strategy5grisu16format_exact_opt14possibly_round17ha32060d16fc65e2cE>
1000036a8:     	ldr	x8, [sp, #0x418]
1000036ac:     	ldr	x0, [sp, #0x10]
1000036b0:     	cbz	x8, 0x100003710 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x560>
1000036b4:     	ldr	x23, [sp, #0x420]
1000036b8:     	ldrh	w22, [sp, #0x428]
1000036bc:     	cmp	w20, w22, sxth
1000036c0:     	b.lt	0x10000414c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf9c>
1000036c4:     	mov	w8, #0x2                ; =2
1000036c8:     	strh	w8, [sp, #0x6e0]
1000036cc:     	cbz	x19, 0x1000036f0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x540>
1000036d0:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000036d4:     	add	x8, x8, #0x631
1000036d8:     	mov	w1, #0x2                ; =2
1000036dc:     	str	x8, [sp, #0x6e8]
1000036e0:     	str	x1, [sp, #0x6f0]
1000036e4:     	strh	wzr, [sp, #0x6f8]
1000036e8:     	str	x19, [sp, #0x700]
1000036ec:     	b	0x100003704 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x554>
1000036f0:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000036f4:     	add	x8, x8, #0x63b
1000036f8:     	mov	w1, #0x1                ; =1
1000036fc:     	str	x8, [sp, #0x6e8]
100003700:     	str	x1, [sp, #0x6f0]
100003704:     	add	x8, sp, #0x6e0
100003708:     	b	0x10000416c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xfbc>
10000370c:     	str	xzr, [sp, #0x418]
100003710:     	add	x21, sp, #0x580
100003714:     	cmp	x27, #0x0
100003718:     	csel	w8, wzr, w27, eq
10000371c:     	str	w22, [sp, #0x430]
100003720:     	str	w8, [sp, #0x434]
100003724:     	add	x8, sp, #0x430
100003728:     	movi.2d	v0, #0000000000000000
10000372c:     	stur	q0, [x8, #0x8]
100003730:     	add	x9, sp, #0x4d8
100003734:     	sub	x10, x22, #0x1
100003738:     	stur	q0, [x8, #0x18]
10000373c:     	clz	x10, x10
100003740:     	sub	x10, x26, x10
100003744:     	stur	q0, [x8, #0x28]
100003748:     	mov	w11, #0x4d42            ; =19778
10000374c:     	movk	w11, #0x4d10, lsl #16
100003750:     	mov	x12, #0x5080            ; =20608
100003754:     	movk	x12, #0x4413, lsl #16
100003758:     	movk	x12, #0x13, lsl #32
10000375c:     	stur	q0, [x8, #0x38]
100003760:     	smaddl	x10, w10, w11, x12
100003764:     	lsr	x26, x10, #32
100003768:     	stur	q0, [x8, #0x48]
10000376c:     	sbfx	x22, x10, #32, #16
100003770:     	mov	w10, #0x1               ; =1
100003774:     	stur	q0, [x8, #0x58]
100003778:     	cinc	x11, x10, ne
10000377c:     	stur	q0, [x8, #0x68]
100003780:     	stur	q0, [x8, #0x78]
100003784:     	stur	q0, [x8, #0x88]
100003788:     	str	x11, [sp, #0x4d0]
10000378c:     	str	xzr, [sp, #0x4c8]
100003790:     	add	x8, sp, #0x469
100003794:     	stur	q0, [x8, #0xff]
100003798:     	stur	q0, [x9, #0x84]
10000379c:     	stur	q0, [x9, #0x74]
1000037a0:     	stur	q0, [x9, #0x64]
1000037a4:     	stur	q0, [x9, #0x54]
1000037a8:     	stur	q0, [x9, #0x44]
1000037ac:     	stur	q0, [x9, #0x34]
1000037b0:     	stur	q0, [x9, #0x24]
1000037b4:     	stur	q0, [x9, #0x14]
1000037b8:     	stur	q0, [x9, #0x4]
1000037bc:     	cmp	w23, #0x0
1000037c0:     	cneg	w1, w23, mi
1000037c4:     	str	x10, [sp, #0x578]
1000037c8:     	add	x23, sp, #0x430
1000037cc:     	add	x27, sp, #0x4d8
1000037d0:     	csel	x0, x27, x23, lt
1000037d4:     	str	w10, [sp, #0x4d8]
1000037d8:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
1000037dc:     	neg	w8, w26
1000037e0:     	cmp	w22, #0x0
1000037e4:     	csel	x8, x26, x8, ge
1000037e8:     	csel	x0, x27, x23, ge
1000037ec:     	and	x1, x8, #0xffff
1000037f0:     	bl	0x1000016bc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E>
1000037f4:     	ldr	x0, [sp, #0x10]
1000037f8:     	ldr	x27, [sp, #0x578]
1000037fc:     	add	x8, sp, #0x439
100003800:     	ldur	q0, [x8, #0xff]
100003804:     	add	x8, sp, #0x449
100003808:     	ldur	q1, [x8, #0xff]
10000380c:     	stp	q0, q1, [x21, #0x1c0]
100003810:     	add	x8, sp, #0x459
100003814:     	ldur	q0, [x8, #0xff]
100003818:     	add	x8, sp, #0x469
10000381c:     	ldur	q1, [x8, #0xff]
100003820:     	stp	q0, q1, [x21, #0x1e0]
100003824:     	add	x8, sp, #0x3f9
100003828:     	ldur	q0, [x8, #0xff]
10000382c:     	add	x8, sp, #0x409
100003830:     	ldur	q1, [x8, #0xff]
100003834:     	stp	q0, q1, [x21, #0x180]
100003838:     	add	x8, sp, #0x419
10000383c:     	ldur	q0, [x8, #0xff]
100003840:     	add	x8, sp, #0x429
100003844:     	ldur	q1, [x8, #0xff]
100003848:     	stp	q0, q1, [x21, #0x1a0]
10000384c:     	add	x8, sp, #0x3d9
100003850:     	ldur	q0, [x8, #0xff]
100003854:     	add	x8, sp, #0x3e9
100003858:     	ldur	q1, [x8, #0xff]
10000385c:     	stp	q0, q1, [x21, #0x160]
100003860:     	str	x27, [sp, #0x780]
100003864:     	cmp	x27, #0x28
100003868:     	b.hi	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
10000386c:     	add	x8, sp, #0x6e0
100003870:     	sub	x8, x8, #0x4
100003874:     	mov	x10, #0x5a53            ; =23123
100003878:     	movk	x10, #0xa09b, lsl #16
10000387c:     	movk	x10, #0xb82f, lsl #32
100003880:     	movk	x10, #0x44, lsl #48
100003884:     	mov	x11, #-0xca00           ; =-51712
100003888:     	movk	x11, #0xc465, lsl #16
10000388c:     	mov	x9, x28
100003890:     	mov	x12, x27
100003894:     	cbz	x12, 0x1000038c4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x714>
100003898:     	mov	x13, #0x0               ; =0
10000389c:     	lsl	x12, x12, #2
1000038a0:     	ldr	w14, [x8, x12]
1000038a4:     	orr	x13, x14, x13, lsl #32
1000038a8:     	lsr	x14, x13, #9
1000038ac:     	umulh	x14, x14, x10
1000038b0:     	lsr	x14, x14, #11
1000038b4:     	madd	x13, x14, x11, x13
1000038b8:     	str	w14, [x8, x12]
1000038bc:     	subs	x12, x12, #0x4
1000038c0:     	b.ne	0x1000038a0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x6f0>
1000038c4:     	sub	x9, x9, #0x9
1000038c8:     	cmp	x9, #0x9
1000038cc:     	b.ls	0x1000038e0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x730>
1000038d0:     	ldr	x12, [sp, #0x780]
1000038d4:     	cmp	x12, #0x29
1000038d8:     	b.lo	0x100003894 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x6e4>
1000038dc:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>
1000038e0:     	adrp	x8, 0x100005000 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe44>
1000038e4:     	add	x8, x8, #0xff8
1000038e8:     	ldr	w8, [x8, x9, lsl #2]
1000038ec:     	cbz	w8, 0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
1000038f0:     	ldr	x9, [sp, #0x780]
1000038f4:     	cmp	x9, #0x29
1000038f8:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
1000038fc:     	str	x28, [sp, #0x8]
100003900:     	cbz	x9, 0x10000394c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x79c>
100003904:     	mov	x10, #0x0               ; =0
100003908:     	lsl	x9, x9, #2
10000390c:     	add	x11, sp, #0x6e0
100003910:     	sub	x11, x11, #0x4
100003914:     	ldr	w12, [x11, x9]
100003918:     	orr	x10, x12, x10, lsl #32
10000391c:     	udiv	x12, x10, x8
100003920:     	msub	x10, x12, x8, x10
100003924:     	str	w12, [x11, x9]
100003928:     	subs	x9, x9, #0x4
10000392c:     	b.ne	0x100003914 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x764>
100003930:     	ldr	x8, [sp, #0x780]
100003934:     	ldr	x28, [sp, #0x4d0]
100003938:     	cmp	x8, x28
10000393c:     	csel	x8, x8, x28, hi
100003940:     	cmp	x8, #0x28
100003944:     	b.ls	0x100003964 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x7b4>
100003948:     	b	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
10000394c:     	mov	x8, #0x0                ; =0
100003950:     	ldr	x28, [sp, #0x4d0]
100003954:     	cmp	x8, x28
100003958:     	csel	x8, x8, x28, hi
10000395c:     	cmp	x8, #0x28
100003960:     	b.hi	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003964:     	cbz	x8, 0x1000039b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x808>
100003968:     	mov	w9, #0x0                ; =0
10000396c:     	add	x10, sp, #0x430
100003970:     	add	x11, sp, #0x6e0
100003974:     	mov	x12, x8
100003978:     	ldr	w13, [x11]
10000397c:     	ldr	w14, [x10], #0x4
100003980:     	and	w9, w9, #0x1
100003984:     	cmp	w9, #0x1
100003988:     	adcs	w13, w13, w14
10000398c:     	cset	w9, hs
100003990:     	str	w13, [x11], #0x4
100003994:     	subs	x12, x12, #0x1
100003998:     	b.ne	0x100003978 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x7c8>
10000399c:     	tbz	w9, #0x0, 0x1000039b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x808>
1000039a0:     	cmp	x8, #0x28
1000039a4:     	b.eq	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
1000039a8:     	add	x9, sp, #0x6e0
1000039ac:     	mov	w10, #0x1               ; =1
1000039b0:     	str	w10, [x9, x8, lsl #2]
1000039b4:     	add	x8, x8, #0x1
1000039b8:     	str	x8, [sp, #0x780]
1000039bc:     	cmp	x8, x27
1000039c0:     	csel	x8, x8, x27, hi
1000039c4:     	cmp	x8, #0x29
1000039c8:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
1000039cc:     	lsl	x8, x8, #2
1000039d0:     	add	x9, sp, #0x6e0
1000039d4:     	add	x10, sp, #0x4d8
1000039d8:     	cbz	x8, 0x100003a24 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x874>
1000039dc:     	add	x11, x9, x8
1000039e0:     	ldur	w11, [x11, #-0x4]
1000039e4:     	add	x12, x10, x8
1000039e8:     	ldur	w12, [x12, #-0x4]
1000039ec:     	cmp	w12, w11
1000039f0:     	cset	w11, ne
1000039f4:     	csinv	w11, w11, wzr, ls
1000039f8:     	sub	x8, x8, #0x4
1000039fc:     	cbz	w11, 0x1000039d8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x828>
100003a00:     	and	w8, w11, #0xff
100003a04:     	cmp	w8, #0x2
100003a08:     	b.hs	0x100003a38 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x888>
100003a0c:     	add	w22, w26, #0x1
100003a10:     	cmp	w20, w22, sxth
100003a14:     	b.le	0x100003a88 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x8d8>
100003a18:     	mov	w8, #0x0                ; =0
100003a1c:     	mov	x23, #0x0               ; =0
100003a20:     	b	0x100003fb4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe04>
100003a24:     	cmp	x8, #0x0
100003a28:     	csetm	w11, ne
100003a2c:     	and	w8, w11, #0xff
100003a30:     	cmp	w8, #0x2
100003a34:     	b.lo	0x100003a0c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x85c>
100003a38:     	cbz	x28, 0x100003a7c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x8cc>
100003a3c:     	mov	x8, #0x0                ; =0
100003a40:     	lsl	x9, x28, #2
100003a44:     	add	x10, sp, #0x430
100003a48:     	mov	w11, #0xa               ; =10
100003a4c:     	ldr	w12, [x10]
100003a50:     	umaddl	x8, w12, w11, x8
100003a54:     	str	w8, [x10], #0x4
100003a58:     	lsr	x8, x8, #32
100003a5c:     	subs	x9, x9, #0x4
100003a60:     	b.ne	0x100003a4c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x89c>
100003a64:     	cbz	w8, 0x100003a7c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x8cc>
100003a68:     	cmp	x28, #0x28
100003a6c:     	b.eq	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
100003a70:     	add	x9, sp, #0x430
100003a74:     	str	w8, [x9, x28, lsl #2]
100003a78:     	add	x28, x28, #0x1
100003a7c:     	str	x28, [sp, #0x4d0]
100003a80:     	cmp	w20, w22, sxth
100003a84:     	b.gt	0x100003a18 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x868>
100003a88:     	mov	x8, x22
100003a8c:     	sxth	x8, w22
100003a90:     	sub	x8, x8, w20, sxtw
100003a94:     	sub	w9, w22, w20
100003a98:     	sxth	x9, w9
100003a9c:     	ldr	x10, [sp, #0x8]
100003aa0:     	cmp	x8, x10
100003aa4:     	csel	x23, x9, x10, lo
100003aa8:     	cbz	x23, 0x100003fb0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe00>
100003aac:     	add	x8, sp, #0x439
100003ab0:     	ldur	q0, [x8, #0xff]
100003ab4:     	add	x8, sp, #0x449
100003ab8:     	ldur	q1, [x8, #0xff]
100003abc:     	stp	q0, q1, [x21, #0x60]
100003ac0:     	add	x8, sp, #0x459
100003ac4:     	ldur	q0, [x8, #0xff]
100003ac8:     	add	x8, sp, #0x469
100003acc:     	ldur	q1, [x8, #0xff]
100003ad0:     	stp	q0, q1, [x21, #0x80]
100003ad4:     	add	x8, sp, #0x3f9
100003ad8:     	ldur	q0, [x8, #0xff]
100003adc:     	add	x8, sp, #0x409
100003ae0:     	ldur	q1, [x8, #0xff]
100003ae4:     	stp	q0, q1, [x21, #0x20]
100003ae8:     	add	x8, sp, #0x419
100003aec:     	ldur	q0, [x8, #0xff]
100003af0:     	add	x8, sp, #0x429
100003af4:     	ldur	q1, [x8, #0xff]
100003af8:     	stp	q0, q1, [x21, #0x40]
100003afc:     	add	x8, sp, #0x3d9
100003b00:     	ldur	q0, [x8, #0xff]
100003b04:     	add	x8, sp, #0x3e9
100003b08:     	ldur	q1, [x8, #0xff]
100003b0c:     	stp	q0, q1, [x21]
100003b10:     	str	x27, [sp, #0x620]
100003b14:     	add	x0, sp, #0x580
100003b18:     	mov	w1, #0x1                ; =1
100003b1c:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100003b20:     	add	x8, sp, #0x439
100003b24:     	ldur	q0, [x8, #0xff]
100003b28:     	add	x8, sp, #0x449
100003b2c:     	ldur	q1, [x8, #0xff]
100003b30:     	stp	q0, q1, [x21, #0x110]
100003b34:     	add	x8, sp, #0x459
100003b38:     	ldur	q0, [x8, #0xff]
100003b3c:     	add	x8, sp, #0x469
100003b40:     	ldur	q1, [x8, #0xff]
100003b44:     	stp	q0, q1, [x21, #0x130]
100003b48:     	add	x8, sp, #0x3f9
100003b4c:     	ldur	q0, [x8, #0xff]
100003b50:     	add	x8, sp, #0x409
100003b54:     	ldur	q1, [x8, #0xff]
100003b58:     	stp	q0, q1, [x21, #0xd0]
100003b5c:     	add	x8, sp, #0x419
100003b60:     	ldur	q0, [x8, #0xff]
100003b64:     	add	x8, sp, #0x429
100003b68:     	ldur	q1, [x8, #0xff]
100003b6c:     	stp	q0, q1, [x21, #0xf0]
100003b70:     	add	x8, sp, #0x3d9
100003b74:     	ldur	q0, [x8, #0xff]
100003b78:     	add	x8, sp, #0x3e9
100003b7c:     	ldur	q1, [x8, #0xff]
100003b80:     	stp	q0, q1, [x21, #0xb0]
100003b84:     	str	x27, [sp, #0x6d0]
100003b88:     	add	x26, sp, #0x630
100003b8c:     	add	x0, sp, #0x630
100003b90:     	mov	w1, #0x2                ; =2
100003b94:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100003b98:     	add	x8, sp, #0x439
100003b9c:     	ldur	q0, [x8, #0xff]
100003ba0:     	add	x8, sp, #0x449
100003ba4:     	ldur	q1, [x8, #0xff]
100003ba8:     	stp	q0, q1, [x21, #0x1c0]
100003bac:     	add	x8, sp, #0x459
100003bb0:     	ldur	q0, [x8, #0xff]
100003bb4:     	add	x8, sp, #0x469
100003bb8:     	ldur	q1, [x8, #0xff]
100003bbc:     	stp	q0, q1, [x21, #0x1e0]
100003bc0:     	add	x8, sp, #0x3f9
100003bc4:     	ldur	q0, [x8, #0xff]
100003bc8:     	add	x8, sp, #0x409
100003bcc:     	ldur	q1, [x8, #0xff]
100003bd0:     	stp	q0, q1, [x21, #0x180]
100003bd4:     	add	x8, sp, #0x419
100003bd8:     	ldur	q0, [x8, #0xff]
100003bdc:     	add	x8, sp, #0x429
100003be0:     	ldur	q1, [x8, #0xff]
100003be4:     	stp	q0, q1, [x21, #0x1a0]
100003be8:     	add	x8, sp, #0x3d9
100003bec:     	ldur	q0, [x8, #0xff]
100003bf0:     	add	x8, sp, #0x3e9
100003bf4:     	ldur	q1, [x8, #0xff]
100003bf8:     	stp	q0, q1, [x21, #0x160]
100003bfc:     	str	x27, [sp, #0x780]
100003c00:     	add	x21, sp, #0x6e0
100003c04:     	add	x0, sp, #0x6e0
100003c08:     	mov	w1, #0x3                ; =3
100003c0c:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100003c10:     	ldr	x0, [sp, #0x10]
100003c14:     	mov	x12, #0x0               ; =0
100003c18:     	ldr	x8, [sp, #0x780]
100003c1c:     	ldr	x9, [sp, #0x6d0]
100003c20:     	ldr	x10, [sp, #0x620]
100003c24:     	add	x11, sp, #0x4d8
100003c28:     	sub	x11, x11, #0x4
100003c2c:     	add	x13, sp, #0x430
100003c30:     	sub	x14, x13, #0x4
100003c34:     	add	x15, sp, #0x18
100003c38:     	mov	w16, #0xa               ; =10
100003c3c:     	cmp	x28, #0x29
100003c40:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003c44:     	mov	x17, x12
100003c48:     	mov	x1, #0x0                ; =0
100003c4c:     	add	x12, x12, #0x1
100003c50:     	lsl	x2, x28, #2
100003c54:     	cmp	x2, x1
100003c58:     	b.eq	0x100003f78 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xdc8>
100003c5c:     	ldr	w3, [x13, x1]
100003c60:     	add	x1, x1, #0x4
100003c64:     	cbz	w3, 0x100003c54 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xaa4>
100003c68:     	cmp	x28, x8
100003c6c:     	csel	x2, x28, x8, hi
100003c70:     	cmp	x2, #0x29
100003c74:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003c78:     	lsl	x1, x2, #2
100003c7c:     	cbz	x1, 0x100003cfc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xb4c>
100003c80:     	add	x3, x13, x1
100003c84:     	ldur	w3, [x3, #-0x4]
100003c88:     	add	x4, x21, x1
100003c8c:     	ldur	w4, [x4, #-0x4]
100003c90:     	cmp	w4, w3
100003c94:     	cset	w3, ne
100003c98:     	csinv	w3, w3, wzr, ls
100003c9c:     	sub	x1, x1, #0x4
100003ca0:     	cbz	w3, 0x100003c7c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xacc>
100003ca4:     	and	w1, w3, #0xff
100003ca8:     	cmp	w1, #0x2
100003cac:     	b.hs	0x100003d10 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xb60>
100003cb0:     	mov	w3, #0x1                ; =1
100003cb4:     	add	x1, sp, #0x6e0
100003cb8:     	add	x4, sp, #0x430
100003cbc:     	mov	x5, x2
100003cc0:     	ldr	w6, [x4]
100003cc4:     	ldr	w7, [x1], #0x4
100003cc8:     	mvn	w7, w7
100003ccc:     	and	w3, w3, #0x1
100003cd0:     	cmp	w3, #0x1
100003cd4:     	adcs	w6, w6, w7
100003cd8:     	cset	w3, hs
100003cdc:     	str	w6, [x4], #0x4
100003ce0:     	subs	x5, x5, #0x1
100003ce4:     	b.ne	0x100003cc0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xb10>
100003ce8:     	tbz	w3, #0x0, 0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
100003cec:     	str	x2, [sp, #0x4d0]
100003cf0:     	mov	w1, #0x8                ; =8
100003cf4:     	mov	x28, x2
100003cf8:     	b	0x100003d14 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xb64>
100003cfc:     	cmp	x1, #0x0
100003d00:     	csetm	w3, ne
100003d04:     	and	w1, w3, #0xff
100003d08:     	cmp	w1, #0x2
100003d0c:     	b.lo	0x100003cb0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xb00>
100003d10:     	mov	w1, #0x0                ; =0
100003d14:     	cmp	x28, x9
100003d18:     	csel	x2, x28, x9, hi
100003d1c:     	cmp	x2, #0x29
100003d20:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003d24:     	lsl	x3, x2, #2
100003d28:     	cbz	x3, 0x100003da8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xbf8>
100003d2c:     	add	x4, x13, x3
100003d30:     	ldur	w4, [x4, #-0x4]
100003d34:     	add	x5, x26, x3
100003d38:     	ldur	w5, [x5, #-0x4]
100003d3c:     	cmp	w5, w4
100003d40:     	cset	w4, ne
100003d44:     	csinv	w4, w4, wzr, ls
100003d48:     	sub	x3, x3, #0x4
100003d4c:     	cbz	w4, 0x100003d28 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xb78>
100003d50:     	and	w3, w4, #0xff
100003d54:     	cmp	w3, #0x1
100003d58:     	b.hi	0x100003dbc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xc0c>
100003d5c:     	cbz	x2, 0x100003d9c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xbec>
100003d60:     	mov	w4, #0x1                ; =1
100003d64:     	add	x3, sp, #0x630
100003d68:     	add	x5, sp, #0x430
100003d6c:     	mov	x6, x2
100003d70:     	ldr	w7, [x5]
100003d74:     	ldr	w28, [x3], #0x4
100003d78:     	mvn	w28, w28
100003d7c:     	and	w4, w4, #0x1
100003d80:     	cmp	w4, #0x1
100003d84:     	adcs	w7, w7, w28
100003d88:     	cset	w4, hs
100003d8c:     	str	w7, [x5], #0x4
100003d90:     	subs	x6, x6, #0x1
100003d94:     	b.ne	0x100003d70 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xbc0>
100003d98:     	tbz	w4, #0x0, 0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
100003d9c:     	str	x2, [sp, #0x4d0]
100003da0:     	orr	w1, w1, #0x4
100003da4:     	b	0x100003dc0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xc10>
100003da8:     	cmp	x3, #0x0
100003dac:     	csetm	w4, ne
100003db0:     	and	w3, w4, #0xff
100003db4:     	cmp	w3, #0x1
100003db8:     	b.ls	0x100003d5c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xbac>
100003dbc:     	mov	x2, x28
100003dc0:     	cmp	x2, x10
100003dc4:     	csel	x3, x2, x10, hi
100003dc8:     	cmp	x3, #0x29
100003dcc:     	add	x7, sp, #0x580
100003dd0:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003dd4:     	lsl	x4, x3, #2
100003dd8:     	cbz	x4, 0x100003e58 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xca8>
100003ddc:     	add	x5, x13, x4
100003de0:     	ldur	w5, [x5, #-0x4]
100003de4:     	add	x6, x7, x4
100003de8:     	ldur	w6, [x6, #-0x4]
100003dec:     	cmp	w6, w5
100003df0:     	cset	w5, ne
100003df4:     	csinv	w5, w5, wzr, ls
100003df8:     	sub	x4, x4, #0x4
100003dfc:     	cbz	w5, 0x100003dd8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xc28>
100003e00:     	and	w4, w5, #0xff
100003e04:     	cmp	w4, #0x1
100003e08:     	b.hi	0x100003e6c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xcbc>
100003e0c:     	cbz	x3, 0x100003e4c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xc9c>
100003e10:     	mov	w4, #0x1                ; =1
100003e14:     	add	x2, sp, #0x580
100003e18:     	add	x5, sp, #0x430
100003e1c:     	mov	x6, x3
100003e20:     	ldr	w7, [x5]
100003e24:     	ldr	w28, [x2], #0x4
100003e28:     	mvn	w28, w28
100003e2c:     	and	w4, w4, #0x1
100003e30:     	cmp	w4, #0x1
100003e34:     	adcs	w7, w7, w28
100003e38:     	cset	w4, hs
100003e3c:     	str	w7, [x5], #0x4
100003e40:     	subs	x6, x6, #0x1
100003e44:     	b.ne	0x100003e20 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xc70>
100003e48:     	tbz	w4, #0x0, 0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
100003e4c:     	str	x3, [sp, #0x4d0]
100003e50:     	add	w1, w1, #0x2
100003e54:     	b	0x100003e70 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xcc0>
100003e58:     	cmp	x4, #0x0
100003e5c:     	csetm	w5, ne
100003e60:     	and	w4, w5, #0xff
100003e64:     	cmp	w4, #0x1
100003e68:     	b.ls	0x100003e0c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xc5c>
100003e6c:     	mov	x3, x2
100003e70:     	cmp	x3, x27
100003e74:     	csel	x28, x3, x27, hi
100003e78:     	cmp	x28, #0x29
100003e7c:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003e80:     	lsl	x2, x28, #2
100003e84:     	cbz	x2, 0x100003efc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd4c>
100003e88:     	ldr	w4, [x14, x2]
100003e8c:     	ldr	w5, [x11, x2]
100003e90:     	cmp	w5, w4
100003e94:     	cset	w4, ne
100003e98:     	csinv	w4, w4, wzr, ls
100003e9c:     	sub	x2, x2, #0x4
100003ea0:     	cbz	w4, 0x100003e84 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xcd4>
100003ea4:     	and	w2, w4, #0xff
100003ea8:     	cmp	w2, #0x1
100003eac:     	b.hi	0x100003f10 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd60>
100003eb0:     	cbz	x28, 0x100003ef0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd40>
100003eb4:     	mov	w3, #0x1                ; =1
100003eb8:     	add	x2, sp, #0x4d8
100003ebc:     	add	x4, sp, #0x430
100003ec0:     	mov	x5, x28
100003ec4:     	ldr	w6, [x4]
100003ec8:     	ldr	w7, [x2], #0x4
100003ecc:     	mvn	w7, w7
100003ed0:     	and	w3, w3, #0x1
100003ed4:     	cmp	w3, #0x1
100003ed8:     	adcs	w6, w6, w7
100003edc:     	cset	w3, hs
100003ee0:     	str	w6, [x4], #0x4
100003ee4:     	subs	x5, x5, #0x1
100003ee8:     	b.ne	0x100003ec4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd14>
100003eec:     	tbz	w3, #0x0, 0x1000041b8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x1008>
100003ef0:     	str	x28, [sp, #0x4d0]
100003ef4:     	add	w1, w1, #0x1
100003ef8:     	b	0x100003f14 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd64>
100003efc:     	cmp	x2, #0x0
100003f00:     	csetm	w4, ne
100003f04:     	and	w2, w4, #0xff
100003f08:     	cmp	w2, #0x1
100003f0c:     	b.ls	0x100003eb0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd00>
100003f10:     	mov	x28, x3
100003f14:     	ldr	x2, [sp, #0x8]
100003f18:     	cmp	x17, x2
100003f1c:     	b.eq	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
100003f20:     	add	w1, w1, #0x30
100003f24:     	strb	w1, [x15, x17]
100003f28:     	cbz	x28, 0x100003f64 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xdb4>
100003f2c:     	mov	x17, #0x0               ; =0
100003f30:     	lsl	x1, x28, #2
100003f34:     	add	x2, sp, #0x430
100003f38:     	ldr	w3, [x2]
100003f3c:     	umaddl	x17, w3, w16, x17
100003f40:     	str	w17, [x2], #0x4
100003f44:     	lsr	x17, x17, #32
100003f48:     	subs	x1, x1, #0x4
100003f4c:     	b.ne	0x100003f38 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xd88>
100003f50:     	cbz	w17, 0x100003f64 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xdb4>
100003f54:     	cmp	x28, #0x28
100003f58:     	b.eq	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
100003f5c:     	str	w17, [x13, x28, lsl #2]
100003f60:     	add	x28, x28, #0x1
100003f64:     	str	x28, [sp, #0x4d0]
100003f68:     	cmp	x12, x23
100003f6c:     	b.ne	0x100003c3c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xa8c>
100003f70:     	mov	w8, #0x1                ; =1
100003f74:     	b	0x100003fb4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe04>
100003f78:     	ldr	x8, [sp, #0x8]
100003f7c:     	cmp	x23, x8
100003f80:     	b.hi	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100003f84:     	subs	x2, x23, x17
100003f88:     	b.eq	0x100003fa0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xdf0>
100003f8c:     	add	x8, sp, #0x18
100003f90:     	add	x0, x8, x17
100003f94:     	mov	w1, #0x30               ; =48
100003f98:     	bl	0x10000584c <_write+0x10000584c>
100003f9c:     	ldr	x0, [sp, #0x10]
100003fa0:     	add	x8, sp, #0x18
100003fa4:     	cmp	w20, w22, sxth
100003fa8:     	b.lt	0x10000414c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf9c>
100003fac:     	b	0x1000036c4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x514>
100003fb0:     	mov	w8, #0x0                ; =0
100003fb4:     	cbz	x27, 0x100003ff8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe48>
100003fb8:     	mov	x9, #0x0                ; =0
100003fbc:     	lsl	x10, x27, #2
100003fc0:     	add	x11, sp, #0x4d8
100003fc4:     	ldr	w12, [x11]
100003fc8:     	add	x12, x12, x12, lsl #2
100003fcc:     	add	x9, x12, x9
100003fd0:     	str	w9, [x11], #0x4
100003fd4:     	lsr	x9, x9, #32
100003fd8:     	subs	x10, x10, #0x4
100003fdc:     	b.ne	0x100003fc4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe14>
100003fe0:     	cbz	w9, 0x100003ff8 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe48>
100003fe4:     	cmp	x27, #0x28
100003fe8:     	b.eq	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
100003fec:     	add	x10, sp, #0x4d8
100003ff0:     	str	w9, [x10, x27, lsl #2]
100003ff4:     	add	x27, x27, #0x1
100003ff8:     	str	x27, [sp, #0x578]
100003ffc:     	cmp	x28, x27
100004000:     	csel	x9, x28, x27, hi
100004004:     	cmp	x9, #0x29
100004008:     	b.hs	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
10000400c:     	lsl	x9, x9, #2
100004010:     	add	x10, sp, #0x430
100004014:     	add	x11, sp, #0x4d8
100004018:     	ldr	x26, [sp, #0x8]
10000401c:     	cbz	x9, 0x100004054 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xea4>
100004020:     	add	x12, x10, x9
100004024:     	ldur	w12, [x12, #-0x4]
100004028:     	add	x13, x11, x9
10000402c:     	ldur	w13, [x13, #-0x4]
100004030:     	cmp	w13, w12
100004034:     	cset	w12, ne
100004038:     	csinv	w12, w12, wzr, ls
10000403c:     	sub	x9, x9, #0x4
100004040:     	cbz	w12, 0x10000401c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xe6c>
100004044:     	and	w8, w12, #0xff
100004048:     	cmp	w8, #0x1
10000404c:     	b.eq	0x100004078 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xec8>
100004050:     	b	0x100004138 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf88>
100004054:     	cmp	x9, #0x0
100004058:     	csel	w8, wzr, w8, ne
10000405c:     	tbz	w8, #0x0, 0x100004138 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf88>
100004060:     	sub	x8, x23, #0x1
100004064:     	cmp	x8, x26
100004068:     	b.hs	0x1000041a4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xff4>
10000406c:     	add	x9, sp, #0x18
100004070:     	ldrb	w8, [x9, x8]
100004074:     	tbz	w8, #0x0, 0x100004138 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf88>
100004078:     	cmp	x23, x26
10000407c:     	b.hi	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100004080:     	mov	x8, #0x0                ; =0
100004084:     	add	x9, sp, #0x18
100004088:     	cmp	x23, x8
10000408c:     	b.eq	0x1000040e0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf30>
100004090:     	add	x10, x9, x23
100004094:     	ldurb	w10, [x10, #-0x1]
100004098:     	add	x8, x8, #0x1
10000409c:     	sub	x9, x9, #0x1
1000040a0:     	cmp	w10, #0x39
1000040a4:     	b.eq	0x100004088 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xed8>
1000040a8:     	ldrb	w10, [x9, x23]
1000040ac:     	add	w10, w10, #0x1
1000040b0:     	strb	w10, [x9, x23]
1000040b4:     	sub	x10, x23, x8
1000040b8:     	add	x10, x10, #0x1
1000040bc:     	cmp	x10, x23
1000040c0:     	b.hs	0x100004138 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf88>
1000040c4:     	sub	x2, x8, #0x1
1000040c8:     	add	x8, x9, x23
1000040cc:     	add	x0, x8, #0x1
1000040d0:     	mov	w1, #0x30               ; =48
1000040d4:     	bl	0x10000584c <_write+0x10000584c>
1000040d8:     	ldr	x0, [sp, #0x10]
1000040dc:     	b	0x100004138 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf88>
1000040e0:     	mov	w21, #0x31              ; =49
1000040e4:     	cbz	x23, 0x100004114 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf64>
1000040e8:     	strb	w21, [sp, #0x18]
1000040ec:     	subs	x2, x23, #0x1
1000040f0:     	b.ne	0x1000040fc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf4c>
1000040f4:     	mov	w21, #0x30              ; =48
1000040f8:     	b	0x100004114 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf64>
1000040fc:     	add	x8, sp, #0x18
100004100:     	mov	w21, #0x30              ; =48
100004104:     	add	x0, x8, #0x1
100004108:     	mov	w1, #0x30               ; =48
10000410c:     	bl	0x10000584c <_write+0x10000584c>
100004110:     	ldr	x0, [sp, #0x10]
100004114:     	add	w8, w22, #0x1
100004118:     	cmp	w20, w22, sxth
10000411c:     	b.gt	0x100004134 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf84>
100004120:     	cmp	x23, x26
100004124:     	b.hs	0x100004134 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xf84>
100004128:     	add	x9, sp, #0x18
10000412c:     	strb	w21, [x9, x23]
100004130:     	add	x23, x23, #0x1
100004134:     	mov	x22, x8
100004138:     	cmp	x23, x26
10000413c:     	b.hi	0x1000038dc <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x72c>
100004140:     	add	x8, sp, #0x18
100004144:     	cmp	w20, w22, sxth
100004148:     	b.ge	0x1000036c4 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0x514>
10000414c:     	add	x4, sp, #0x6e0
100004150:     	mov	x0, x8
100004154:     	mov	x1, x23
100004158:     	mov	x2, x22
10000415c:     	mov	x3, x19
100004160:     	bl	0x100001d04 <__ZN4core3num7flt2dec17digits_to_dec_str17h7c8a76a6f102bf81E>
100004164:     	mov	x8, x0
100004168:     	ldr	x0, [sp, #0x10]
10000416c:     	str	x25, [sp, #0x630]
100004170:     	str	x24, [sp, #0x638]
100004174:     	str	x8, [sp, #0x640]
100004178:     	str	x1, [sp, #0x648]
10000417c:     	add	x1, sp, #0x630
100004180:     	bl	0x100002d38 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E>
100004184:     	add	sp, sp, #0x7a0
100004188:     	ldp	x29, x30, [sp, #0x50]
10000418c:     	ldp	x20, x19, [sp, #0x40]
100004190:     	ldp	x22, x21, [sp, #0x30]
100004194:     	ldp	x24, x23, [sp, #0x20]
100004198:     	ldp	x26, x25, [sp, #0x10]
10000419c:     	ldp	x28, x27, [sp], #0x60
1000041a0:     	ret
1000041a4:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>
1000041a8:     	mov	x24, #0x0               ; =0
1000041ac:     	mov	w10, #0x2               ; =2
1000041b0:     	mov	w25, #0x1               ; =1
1000041b4:     	b	0x10000328c <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E+0xdc>
1000041b8:     	bl	0x1000057f8 <__ZN4core9panicking5panic17hff67cc28c73a35f9E>

00000001000041bc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E>:
1000041bc:     	stp	x28, x27, [sp, #-0x60]!
1000041c0:     	stp	x26, x25, [sp, #0x10]
1000041c4:     	stp	x24, x23, [sp, #0x20]
1000041c8:     	stp	x22, x21, [sp, #0x30]
1000041cc:     	stp	x20, x19, [sp, #0x40]
1000041d0:     	stp	x29, x30, [sp, #0x50]
1000041d4:     	add	x29, sp, #0x50
1000041d8:     	sub	sp, sp, #0x600
1000041dc:     	str	xzr, [sp]
1000041e0:     	fmov	x10, d0
1000041e4:     	lsr	x8, x10, #52
1000041e8:     	ands	w8, w8, #0x7ff
1000041ec:     	ubfiz	x9, x10, #1, #52
1000041f0:     	mov	x11, #0x10000000000000  ; =4503599627370496
1000041f4:     	bfxil	x11, x10, #0, #52
1000041f8:     	csel	x9, x9, x11, eq
1000041fc:     	fcmp	d0, d0
100004200:     	b.vs	0x1000054b0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f4>
100004204:     	and	x11, x9, #0x1
100004208:     	and	x12, x10, #0x7ff0000000000000
10000420c:     	and	x13, x10, #0xfffffffffffff
100004210:     	cbz	x13, 0x100004228 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6c>
100004214:     	cbnz	x12, 0x100004240 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x84>
100004218:     	sub	w15, w8, #0x433
10000421c:     	eor	w14, w11, #0x1
100004220:     	mov	w24, #0x1               ; =1
100004224:     	b	0x10000426c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xb0>
100004228:     	mov	x13, #0x7ff0000000000000 ; =9218868437227405312
10000422c:     	cmp	x12, x13
100004230:     	b.ne	0x10000423c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x80>
100004234:     	mov	w14, #0x3               ; =3
100004238:     	b	0x10000426c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xb0>
10000423c:     	cbz	x12, 0x10000488c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6d0>
100004240:     	lsl	x12, x9, #1
100004244:     	mov	x13, #0x10000000000000  ; =4503599627370496
100004248:     	mov	x14, #0x40000000000000  ; =18014398509481984
10000424c:     	cmp	x9, x13
100004250:     	csel	x9, x14, x12, eq
100004254:     	mov	w12, #0x1               ; =1
100004258:     	cinc	x24, x12, eq
10000425c:     	mov	w12, #-0x435            ; =-1077
100004260:     	cinc	w12, w12, ne
100004264:     	add	w15, w12, w8
100004268:     	eor	w14, w11, #0x1
10000426c:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100004270:     	add	x8, x8, #0x634
100004274:     	adrp	x11, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100004278:     	add	x11, x11, #0x633
10000427c:     	cmp	x10, #0x0
100004280:     	csel	x8, x11, x8, lt
100004284:     	mov	w12, #0x1               ; =1
100004288:     	csinc	x11, x11, xzr, lt
10000428c:     	lsr	x10, x10, #63
100004290:     	tst	w1, #0x1
100004294:     	csel	x19, x8, x11, ne
100004298:     	csel	x4, x12, x10, ne
10000429c:     	add	x22, sp, #0x330
1000042a0:     	sub	w8, w14, #0x2
1000042a4:     	and	w8, w8, #0xff
1000042a8:     	mov	w10, #0x3               ; =3
1000042ac:     	cmp	w8, #0x3
1000042b0:     	csel	w8, w8, w10, lo
1000042b4:     	cmp	w8, #0x1
1000042b8:     	b.gt	0x1000042d4 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x118>
1000042bc:     	cbnz	w8, 0x1000042f8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x13c>
1000042c0:     	mov	w8, #0x2                ; =2
1000042c4:     	strh	w8, [x22, #0x210]
1000042c8:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000042cc:     	add	x8, x8, #0x635
1000042d0:     	b	0x100004308 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x14c>
1000042d4:     	cmp	w8, #0x2
1000042d8:     	b.ne	0x10000434c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x190>
1000042dc:     	strh	w8, [x22, #0x210]
1000042e0:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000042e4:     	add	x8, x8, #0x63b
1000042e8:     	str	x8, [x22, #0x218]
1000042ec:     	mov	w8, #0x1                ; =1
1000042f0:     	str	x8, [x22, #0x220]
1000042f4:     	b	0x100004318 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x15c>
1000042f8:     	mov	w8, #0x2                ; =2
1000042fc:     	strh	w8, [x22, #0x210]
100004300:     	adrp	x8, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100004304:     	add	x8, x8, #0x638
100004308:     	str	x8, [x22, #0x218]
10000430c:     	mov	w8, #0x3                ; =3
100004310:     	str	x8, [x22, #0x220]
100004314:     	mov	w8, #0x1                ; =1
100004318:     	stp	x19, x4, [x22, #0x160]
10000431c:     	add	x9, sp, #0x540
100004320:     	stp	x9, x8, [x22, #0x170]
100004324:     	add	x1, sp, #0x490
100004328:     	bl	0x100002d38 <__ZN4core3fmt9Formatter19pad_formatted_parts17h0ed2d250ff4687b9E>
10000432c:     	add	sp, sp, #0x600
100004330:     	ldp	x29, x30, [sp, #0x50]
100004334:     	ldp	x20, x19, [sp, #0x40]
100004338:     	ldp	x22, x21, [sp, #0x30]
10000433c:     	ldp	x24, x23, [sp, #0x20]
100004340:     	ldp	x26, x25, [sp, #0x10]
100004344:     	ldp	x28, x27, [sp], #0x60
100004348:     	ret
10000434c:     	cbz	x9, 0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
100004350:     	add	x8, x9, x24
100004354:     	lsl	x10, x8, #32
100004358:     	sub	w11, w15, #0x20
10000435c:     	lsr	x12, x8, #32
100004360:     	cmp	x12, #0x0
100004364:     	csel	x8, x10, x8, eq
100004368:     	csel	w10, w11, w15, eq
10000436c:     	lsl	x11, x8, #16
100004370:     	sub	w12, w10, #0x10
100004374:     	lsr	x13, x8, #48
100004378:     	cmp	x13, #0x0
10000437c:     	csel	x8, x11, x8, eq
100004380:     	csel	w10, w12, w10, eq
100004384:     	lsl	x11, x8, #8
100004388:     	sub	w12, w10, #0x8
10000438c:     	lsr	x13, x8, #56
100004390:     	cmp	x13, #0x0
100004394:     	csel	x8, x11, x8, eq
100004398:     	csel	w10, w12, w10, eq
10000439c:     	lsl	x11, x8, #4
1000043a0:     	sub	w12, w10, #0x4
1000043a4:     	lsr	x13, x8, #60
1000043a8:     	cmp	x13, #0x0
1000043ac:     	csel	x8, x11, x8, eq
1000043b0:     	csel	w10, w12, w10, eq
1000043b4:     	lsl	x11, x8, #2
1000043b8:     	sub	w12, w10, #0x2
1000043bc:     	lsr	x13, x8, #62
1000043c0:     	cmp	x13, #0x0
1000043c4:     	csel	x8, x11, x8, eq
1000043c8:     	csel	w10, w12, w10, eq
1000043cc:     	lsr	x11, x8, #63
1000043d0:     	eor	w11, w11, #0x1
1000043d4:     	sub	w12, w10, w11
1000043d8:     	sub	w10, w15, w12
1000043dc:     	tbnz	w10, #0xf, 0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
1000043e0:     	sub	x25, x9, #0x1
1000043e4:     	sxth	w10, w10
1000043e8:     	lsl	x11, x25, x10
1000043ec:     	lsr	x13, x11, x10
1000043f0:     	cmp	x13, x25
1000043f4:     	b.ne	0x1000054c0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1304>
1000043f8:     	str	x15, [sp, #0x50]
1000043fc:     	str	x0, [sp, #0x68]
100004400:     	str	w14, [sp, #0x78]
100004404:     	and	x13, x10, #0x3f
100004408:     	lsl	x10, x9, x13
10000440c:     	lsr	x13, x10, x13
100004410:     	cmp	x13, x9
100004414:     	b.ne	0x1000054c0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1304>
100004418:     	mvn	x13, x8
10000441c:     	lsr	x13, x13, #63
100004420:     	lsl	x8, x8, x13
100004424:     	mov	w13, #-0x60             ; =-96
100004428:     	sub	w13, w13, w12
10000442c:     	sxth	w13, w13
100004430:     	mov	w14, #0x50              ; =80
100004434:     	mov	w15, #0x53b0            ; =21424
100004438:     	movk	w15, #0x1, lsl #16
10000443c:     	madd	w13, w13, w14, w15
100004440:     	mov	w14, #0xc993            ; =51603
100004444:     	movk	w14, #0x7b4d, lsl #16
100004448:     	umull	x13, w13, w14
10000444c:     	lsr	x13, x13, #38
100004450:     	and	x13, x13, #0x1fffff0
100004454:     	adrp	x14, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100004458:     	add	x14, x14, #0xf8
10000445c:     	add	x13, x14, x13
100004460:     	ldr	x14, [x13]
100004464:     	ldrh	w17, [x13, #0x8]
100004468:     	ldrh	w6, [x13, #0xa]
10000446c:     	lsr	x15, x8, #32
100004470:     	and	x13, x8, #0xffffffff
100004474:     	lsr	x16, x14, #32
100004478:     	and	x1, x14, #0xffffffff
10000447c:     	umull	x13, w16, w13
100004480:     	umull	x0, w1, w15
100004484:     	umull	x8, w14, w8
100004488:     	lsr	x8, x8, #32
10000448c:     	and	x2, x0, #0xffffffff
100004490:     	and	x3, x13, #0xffffffff
100004494:     	stp	x2, x8, [sp, #0x20]
100004498:     	add	x8, x2, x8
10000449c:     	mov	w2, #-0x80000000        ; =-2147483648
1000044a0:     	str	x3, [sp, #0x18]
1000044a4:     	add	x3, x3, x2
1000044a8:     	add	x8, x8, x3
1000044ac:     	lsr	x3, x0, #32
1000044b0:     	lsr	x20, x13, #32
1000044b4:     	lsr	x13, x11, #32
1000044b8:     	neg	w12, w12
1000044bc:     	sub	w12, w12, w17
1000044c0:     	and	x17, x11, #0xffffffff
1000044c4:     	umull	x7, w16, w13
1000044c8:     	umull	x17, w16, w17
1000044cc:     	umull	x13, w1, w13
1000044d0:     	umull	x11, w14, w11
1000044d4:     	lsr	x11, x11, #32
1000044d8:     	add	x11, x11, w13, uxtw
1000044dc:     	add	x11, x11, w17, uxtw
1000044e0:     	add	x0, x11, x2
1000044e4:     	lsr	x30, x13, #32
1000044e8:     	lsr	x11, x17, #32
1000044ec:     	lsr	x0, x0, #32
1000044f0:     	lsr	x5, x10, #32
1000044f4:     	and	x13, x10, #0xffffffff
1000044f8:     	umull	x13, w16, w13
1000044fc:     	umull	x17, w1, w5
100004500:     	umull	x10, w14, w10
100004504:     	lsr	x10, x10, #32
100004508:     	add	x10, x10, w17, uxtw
10000450c:     	add	x10, x10, w13, uxtw
100004510:     	add	x14, x10, x2
100004514:     	lsr	x10, x17, #32
100004518:     	str	x10, [sp, #0x10]
10000451c:     	umaddl	x10, w16, w5, x10
100004520:     	lsr	x26, x13, #32
100004524:     	add	x10, x10, x26
100004528:     	lsr	x27, x14, #32
10000452c:     	stp	x20, x3, [sp, #0x30]
100004530:     	umaddl	x13, w16, w15, x3
100004534:     	add	x13, x13, x20
100004538:     	add	x8, x13, x8, lsr #32
10000453c:     	add	x20, x8, #0x1
100004540:     	and	w21, w12, #0x3f
100004544:     	lsr	x28, x20, x12
100004548:     	ubfx	x8, x28, #4, #28
10000454c:     	mov	w13, #0x1               ; =1
100004550:     	lsl	x14, x13, x12
100004554:     	sub	x23, x14, #0x1
100004558:     	and	x13, x20, x23
10000455c:     	cmp	w8, #0x271
100004560:     	stp	x19, x4, [sp, #0x58]
100004564:     	stp	x25, x24, [sp, #0x40]
100004568:     	b.hs	0x1000045a4 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x3e8>
10000456c:     	cmp	w28, #0x9
100004570:     	cset	w8, hi
100004574:     	mov	w12, #0xa               ; =10
100004578:     	csinc	w12, w12, wzr, hi
10000457c:     	mov	w17, #0x3e8             ; =1000
100004580:     	mov	w1, #0x64               ; =100
100004584:     	cmp	w28, #0x3e8
100004588:     	csel	w17, w1, w17, lo
10000458c:     	mov	w1, #0x2                ; =2
100004590:     	cinc	w1, w1, hs
100004594:     	cmp	w28, #0x64
100004598:     	csel	w3, w12, w17, lo
10000459c:     	csel	w8, w8, w1, lo
1000045a0:     	b	0x10000461c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x460>
1000045a4:     	mov	w8, #0x4240             ; =16960
1000045a8:     	movk	w8, #0xf, lsl #16
1000045ac:     	lsr	w12, w28, #5
1000045b0:     	mov	w17, #0x86a0            ; =34464
1000045b4:     	movk	w17, #0x1, lsl #16
1000045b8:     	mov	w1, #0x2710             ; =10000
1000045bc:     	cmp	w12, #0xc35
1000045c0:     	csel	w12, w1, w17, lo
1000045c4:     	mov	w17, #0x4               ; =4
1000045c8:     	cinc	w17, w17, hs
1000045cc:     	mov	w1, #0xe100             ; =57600
1000045d0:     	movk	w1, #0x5f5, lsl #16
1000045d4:     	mov	w2, #0x9680             ; =38528
1000045d8:     	movk	w2, #0x98, lsl #16
1000045dc:     	cmp	w28, w2
1000045e0:     	csel	w2, w8, w2, lo
1000045e4:     	mov	w3, #0x6                ; =6
1000045e8:     	cinc	w3, w3, hs
1000045ec:     	mov	w4, #0xca00             ; =51712
1000045f0:     	movk	w4, #0x3b9a, lsl #16
1000045f4:     	cmp	w28, w4
1000045f8:     	csel	w4, w1, w4, lo
1000045fc:     	mov	w19, #0x8               ; =8
100004600:     	cinc	w19, w19, hs
100004604:     	cmp	w28, w1
100004608:     	csel	w1, w2, w4, lo
10000460c:     	csel	w2, w3, w19, lo
100004610:     	cmp	w28, w8
100004614:     	csel	w3, w12, w1, lo
100004618:     	csel	w8, w17, w2, lo
10000461c:     	mov	x12, #0x0               ; =0
100004620:     	add	x19, sp, #0x288
100004624:     	add	x25, sp, #0x90
100004628:     	umull	x17, w16, w15
10000462c:     	str	x17, [sp, #0x8]
100004630:     	umull	x4, w16, w5
100004634:     	add	x10, x10, x27
100004638:     	and	w17, w8, #0xff
10000463c:     	sub	w17, w17, w6
100004640:     	add	w17, w17, #0x1
100004644:     	str	x17, [sp, #0x70]
100004648:     	add	x17, x30, x7
10000464c:     	add	x11, x17, x11
100004650:     	add	x30, x11, x0
100004654:     	sub	x11, x20, x30
100004658:     	str	x11, [sp]
10000465c:     	add	x1, x11, #0x1
100004660:     	and	x7, x1, x23
100004664:     	and	x6, x8, #0xff
100004668:     	add	x8, sp, #0x7f
10000466c:     	mov	w2, #0xcccd             ; =52429
100004670:     	movk	w2, #0xcccc, lsl #16
100004674:     	udiv	w11, w28, w3
100004678:     	msub	w28, w11, w3, w28
10000467c:     	add	w0, w11, #0x30
100004680:     	strb	w0, [x8, x12]
100004684:     	lsl	x11, x28, x21
100004688:     	add	x17, x11, x13
10000468c:     	subs	x24, x1, x17
100004690:     	b.hi	0x1000046b8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x4fc>
100004694:     	cmp	x6, x12
100004698:     	b.eq	0x1000047b0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x5f4>
10000469c:     	umull	x11, w3, w2
1000046a0:     	lsr	x11, x11, #35
1000046a4:     	add	x12, x12, #0x1
1000046a8:     	cmp	w3, #0xa
1000046ac:     	mov	x3, x11
1000046b0:     	b.hs	0x100004674 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x4b8>
1000046b4:     	bl	0x10000581c <__ZN4core9panicking11panic_const23panic_const_div_by_zero17h71be41e2a26e0e82E>
1000046b8:     	mov	w8, w3
1000046bc:     	lsl	x14, x8, x21
1000046c0:     	sub	x8, x20, x10
1000046c4:     	add	x7, x8, #0x1
1000046c8:     	sub	x10, x8, #0x1
1000046cc:     	cmp	x24, x14
1000046d0:     	cset	w21, lo
1000046d4:     	cmp	x10, x17
1000046d8:     	ccmp	x24, x14, #0x0, hi
1000046dc:     	b.lo	0x10000489c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6e0>
1000046e0:     	ldp	x2, x8, [sp, #0x8]
1000046e4:     	add	x8, x8, x26
1000046e8:     	add	x8, x8, x27
1000046ec:     	add	x17, x8, x4
1000046f0:     	neg	x17, x17
1000046f4:     	add	x1, x13, x11
1000046f8:     	sub	x20, x17, x1
1000046fc:     	ldp	x1, x17, [sp, #0x20]
100004700:     	add	x17, x17, x1
100004704:     	ldr	x1, [sp, #0x18]
100004708:     	add	x17, x17, x1
10000470c:     	mov	w1, #-0x80000000        ; =-2147483648
100004710:     	add	x17, x17, x1
100004714:     	lsr	x17, x17, #32
100004718:     	ldp	x6, x4, [sp, #0x30]
10000471c:     	add	x1, x4, x6
100004720:     	add	x1, x1, x17
100004724:     	add	x2, x1, x2
100004728:     	add	x3, x13, x14
10000472c:     	add	x8, x8, x3
100004730:     	sub	x15, x5, x15
100004734:     	mul	x15, x16, x15
100004738:     	add	x8, x8, x15
10000473c:     	sub	x8, x8, x4
100004740:     	sub	x8, x8, x6
100004744:     	sub	x15, x8, x17
100004748:     	add	x8, x3, x11
10000474c:     	add	x8, x30, x8
100004750:     	mov	w16, #0x2               ; =2
100004754:     	sub	x16, x16, x8
100004758:     	add	x17, sp, #0x7f
10000475c:     	add	x8, x11, x3
100004760:     	cmp	x8, x10
100004764:     	b.lo	0x100004778 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x5bc>
100004768:     	add	x1, x20, x2
10000476c:     	add	x4, x11, x15
100004770:     	cmp	x1, x4
100004774:     	b.lo	0x100004894 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6d8>
100004778:     	sub	w0, w0, #0x1
10000477c:     	strb	w0, [x17, x12]
100004780:     	add	x1, x16, x2
100004784:     	cmp	x1, x14
100004788:     	cset	w21, lo
10000478c:     	add	x13, x13, x14
100004790:     	cmp	x8, x10
100004794:     	b.hs	0x100004898 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6dc>
100004798:     	sub	x2, x2, x14
10000479c:     	add	x15, x15, x14
1000047a0:     	add	x3, x3, x14
1000047a4:     	cmp	x1, x14
1000047a8:     	b.hs	0x10000475c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x5a0>
1000047ac:     	b	0x100004898 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6dc>
1000047b0:     	mov	w1, #0x1                ; =1
1000047b4:     	add	x0, sp, #0x7f
1000047b8:     	cmp	x12, #0x10
1000047bc:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
1000047c0:     	mov	x15, x1
1000047c4:     	mov	x17, x7
1000047c8:     	add	x8, x13, x13, lsl #2
1000047cc:     	lsl	x8, x8, #1
1000047d0:     	and	x13, x8, x23
1000047d4:     	add	x16, x1, x1, lsl #2
1000047d8:     	lsl	x1, x16, #1
1000047dc:     	add	x11, x7, x7, lsl #2
1000047e0:     	lsl	x7, x11, #1
1000047e4:     	lsr	x8, x8, x21
1000047e8:     	add	w11, w8, #0x30
1000047ec:     	add	x8, x0, x12
1000047f0:     	strb	w11, [x8, #0x1]
1000047f4:     	add	x12, x12, #0x1
1000047f8:     	subs	x8, x7, x13
1000047fc:     	b.ls	0x1000047b8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x5fc>
100004800:     	sub	x10, x20, x10
100004804:     	mul	x0, x1, x10
100004808:     	add	x10, x0, x1
10000480c:     	cmp	x8, x14
100004810:     	cset	w4, lo
100004814:     	b.lo	0x1000048dc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x720>
100004818:     	sub	x0, x0, x1
10000481c:     	subs	x1, x0, x13
100004820:     	b.ls	0x1000048dc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x720>
100004824:     	mov	x2, #0x0                ; =0
100004828:     	sub	x3, x14, x0
10000482c:     	mov	w8, #0xa                ; =10
100004830:     	add	x4, x14, x13
100004834:     	neg	x4, x4
100004838:     	madd	x5, x17, x8, x4
10000483c:     	add	x6, sp, #0x7f
100004840:     	add	x17, x13, x14
100004844:     	cmp	x17, x0
100004848:     	b.lo	0x10000485c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x6a0>
10000484c:     	add	x8, x1, x2
100004850:     	add	x4, x3, x13
100004854:     	cmp	x8, x4
100004858:     	b.lo	0x1000048d8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x71c>
10000485c:     	sub	w11, w11, #0x1
100004860:     	strb	w11, [x6, x12]
100004864:     	add	x8, x5, x2
100004868:     	cmp	x8, x14
10000486c:     	cset	w4, lo
100004870:     	cmp	x17, x0
100004874:     	b.hs	0x1000048e0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x724>
100004878:     	sub	x2, x2, x14
10000487c:     	mov	x13, x17
100004880:     	cmp	x8, x14
100004884:     	b.hs	0x100004840 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x684>
100004888:     	b	0x1000048e0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x724>
10000488c:     	mov	w14, #0x4               ; =4
100004890:     	b	0x10000426c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xb0>
100004894:     	mov	w21, #0x0               ; =0
100004898:     	add	x17, x11, x13
10000489c:     	subs	x8, x7, x17
1000048a0:     	b.ls	0x1000048bc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x700>
1000048a4:     	tbnz	w21, #0x0, 0x1000048bc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x700>
1000048a8:     	add	x10, x17, x14
1000048ac:     	subs	x10, x10, x7
1000048b0:     	b.lo	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
1000048b4:     	cmp	x8, x10
1000048b8:     	b.hs	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
1000048bc:     	cmp	x17, #0x2
1000048c0:     	b.lo	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
1000048c4:     	ldr	x8, [sp]
1000048c8:     	sub	x8, x8, #0x3
1000048cc:     	cmp	x17, x8
1000048d0:     	b.ls	0x10000491c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x760>
1000048d4:     	b	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
1000048d8:     	mov	w4, #0x0                ; =0
1000048dc:     	mov	x17, x13
1000048e0:     	subs	x8, x10, x17
1000048e4:     	b.ls	0x100004900 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x744>
1000048e8:     	tbnz	w4, #0x0, 0x100004900 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x744>
1000048ec:     	add	x11, x17, x14
1000048f0:     	subs	x10, x11, x10
1000048f4:     	b.lo	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
1000048f8:     	cmp	x8, x10
1000048fc:     	b.hs	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
100004900:     	lsl	x8, x16, #2
100004904:     	cmp	x8, x17
100004908:     	b.hi	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
10000490c:     	mov	x8, #-0x28              ; =-40
100004910:     	madd	x8, x15, x8, x7
100004914:     	cmp	x17, x8
100004918:     	b.hi	0x10000492c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x770>
10000491c:     	add	x23, x12, #0x1
100004920:     	ldp	x19, x4, [sp, #0x58]
100004924:     	ldp	x0, x21, [sp, #0x68]
100004928:     	b	0x1000053a0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x11e4>
10000492c:     	lsr	x8, x9, #32
100004930:     	cmp	x8, #0x0
100004934:     	csel	w8, wzr, w8, eq
100004938:     	stp	w9, w8, [sp, #0x90]
10000493c:     	ldp	x8, x11, [sp, #0x40]
100004940:     	add	x8, x8, x11
100004944:     	movi.2d	v0, #0000000000000000
100004948:     	stur	q0, [sp, #0x98]
10000494c:     	clz	x8, x8
100004950:     	ldr	x21, [sp, #0x50]
100004954:     	sxth	x9, w21
100004958:     	stur	q0, [sp, #0xa8]
10000495c:     	sub	x8, x9, x8
100004960:     	mov	w9, #0x4d42             ; =19778
100004964:     	movk	w9, #0x4d10, lsl #16
100004968:     	stur	q0, [sp, #0xb8]
10000496c:     	mov	x10, #0x5080            ; =20608
100004970:     	movk	x10, #0x4413, lsl #16
100004974:     	movk	x10, #0x13, lsl #32
100004978:     	smaddl	x20, w8, w9, x10
10000497c:     	stur	q0, [sp, #0xc8]
100004980:     	mov	w8, #0x1                ; =1
100004984:     	cinc	x9, x8, ne
100004988:     	stur	q0, [sp, #0xd8]
10000498c:     	stur	q0, [sp, #0xe8]
100004990:     	stur	q0, [sp, #0xf8]
100004994:     	stur	q0, [x25, #0x78]
100004998:     	stur	q0, [x25, #0x88]
10000499c:     	stp	xzr, x9, [x25, #0x98]
1000049a0:     	str	x8, [x25, #0x148]
1000049a4:     	str	w8, [x25, #0xa8]
1000049a8:     	stur	q0, [x25, #0xac]
1000049ac:     	stur	q0, [x25, #0xbc]
1000049b0:     	stur	q0, [x25, #0xcc]
1000049b4:     	stur	q0, [x25, #0xdc]
1000049b8:     	stur	q0, [x25, #0xec]
1000049bc:     	stur	q0, [x25, #0xfc]
1000049c0:     	add	x9, sp, #0x138
1000049c4:     	stur	q0, [x9, #0x64]
1000049c8:     	stur	q0, [x9, #0x74]
1000049cc:     	stur	q0, [x9, #0x84]
1000049d0:     	str	q0, [x9, #0x90]
1000049d4:     	str	x8, [x9, #0x148]
1000049d8:     	str	w11, [x9, #0xa8]
1000049dc:     	stur	q0, [x9, #0xac]
1000049e0:     	stur	q0, [x9, #0xbc]
1000049e4:     	stur	q0, [x9, #0xcc]
1000049e8:     	stur	q0, [x9, #0xdc]
1000049ec:     	stur	q0, [x9, #0xec]
1000049f0:     	stur	q0, [x9, #0xfc]
1000049f4:     	add	x9, sp, #0x1e0
1000049f8:     	stur	q0, [x9, #0x64]
1000049fc:     	stur	q0, [x9, #0x74]
100004a00:     	stur	q0, [x9, #0x84]
100004a04:     	str	q0, [x9, #0x90]
100004a08:     	str	q0, [x19, #0x90]
100004a0c:     	stur	q0, [x19, #0x84]
100004a10:     	stur	q0, [x19, #0x74]
100004a14:     	stur	q0, [x19, #0x64]
100004a18:     	stur	q0, [x19, #0x54]
100004a1c:     	stur	q0, [x19, #0x44]
100004a20:     	stur	q0, [x19, #0x34]
100004a24:     	stur	q0, [x19, #0x24]
100004a28:     	stur	q0, [x19, #0x14]
100004a2c:     	stur	q0, [x19, #0x4]
100004a30:     	str	x8, [x19, #0xa0]
100004a34:     	str	w8, [x19]
100004a38:     	tbnz	w21, #0xf, 0x100004a74 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x8b8>
100004a3c:     	add	x0, sp, #0x90
100004a40:     	and	x1, x21, #0xffff
100004a44:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004a48:     	add	x0, sp, #0x138
100004a4c:     	and	x1, x21, #0xffff
100004a50:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004a54:     	add	x0, sp, #0x1e0
100004a58:     	and	x1, x21, #0xffff
100004a5c:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004a60:     	lsr	x21, x20, #32
100004a64:     	tbnz	x20, #0x2f, 0x100004a8c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x8d0>
100004a68:     	ubfx	x1, x20, #32, #16
100004a6c:     	add	x0, sp, #0x288
100004a70:     	b	0x100004ab0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x8f4>
100004a74:     	neg	w8, w21
100004a78:     	add	x0, sp, #0x288
100004a7c:     	and	x1, x8, #0xffff
100004a80:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004a84:     	lsr	x21, x20, #32
100004a88:     	tbz	x20, #0x2f, 0x100004a68 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x8ac>
100004a8c:     	neg	w20, w21
100004a90:     	add	x0, sp, #0x90
100004a94:     	and	x1, x20, #0xffff
100004a98:     	bl	0x1000016bc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E>
100004a9c:     	add	x0, sp, #0x138
100004aa0:     	and	x1, x20, #0xffff
100004aa4:     	bl	0x1000016bc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E>
100004aa8:     	add	x0, sp, #0x1e0
100004aac:     	and	x1, x20, #0xffff
100004ab0:     	bl	0x1000016bc <__ZN4core3num7flt2dec8strategy6dragon9mul_pow1017h69e5819adae67887E>
100004ab4:     	ldr	x20, [x25, #0xa0]
100004ab8:     	ldr	q0, [sp, #0xf0]
100004abc:     	ldp	q1, q2, [x25, #0x70]
100004ac0:     	stp	q0, q1, [x22, #0x270]
100004ac4:     	ldr	q0, [x25, #0x90]
100004ac8:     	stp	q2, q0, [x22, #0x290]
100004acc:     	ldp	q0, q1, [sp, #0xb0]
100004ad0:     	stp	q0, q1, [x22, #0x230]
100004ad4:     	ldp	q0, q1, [sp, #0xd0]
100004ad8:     	stp	q0, q1, [x22, #0x250]
100004adc:     	ldp	q0, q1, [sp, #0x90]
100004ae0:     	stp	q0, q1, [x22, #0x210]
100004ae4:     	add	x8, sp, #0x1e0
100004ae8:     	ldr	x28, [x8, #0xa0]
100004aec:     	cmp	x20, x28
100004af0:     	csel	x8, x20, x28, hi
100004af4:     	str	x20, [x22, #0x2b0]
100004af8:     	cmp	x8, #0x28
100004afc:     	ldr	w15, [sp, #0x78]
100004b00:     	b.hi	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004b04:     	cbz	x8, 0x100004b58 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x99c>
100004b08:     	mov	w9, #0x0                ; =0
100004b0c:     	add	x10, sp, #0x1e0
100004b10:     	add	x11, sp, #0x540
100004b14:     	mov	x12, x8
100004b18:     	ldr	w13, [x11]
100004b1c:     	ldr	w14, [x10], #0x4
100004b20:     	and	w9, w9, #0x1
100004b24:     	cmp	w9, #0x1
100004b28:     	adcs	w13, w13, w14
100004b2c:     	cset	w9, hs
100004b30:     	str	w13, [x11], #0x4
100004b34:     	subs	x12, x12, #0x1
100004b38:     	b.ne	0x100004b18 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x95c>
100004b3c:     	tbz	w9, #0x0, 0x100004b58 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x99c>
100004b40:     	cmp	x8, #0x28
100004b44:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100004b48:     	add	x9, sp, #0x540
100004b4c:     	mov	w10, #0x1               ; =1
100004b50:     	str	w10, [x9, x8, lsl #2]
100004b54:     	add	x8, x8, #0x1
100004b58:     	str	x8, [x22, #0x2b0]
100004b5c:     	ldr	x24, [x19, #0xa0]
100004b60:     	cmp	x24, x8
100004b64:     	csel	x8, x24, x8, hi
100004b68:     	cmp	x8, #0x29
100004b6c:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004b70:     	lsl	x8, x8, #2
100004b74:     	add	x9, sp, #0x288
100004b78:     	add	x10, sp, #0x540
100004b7c:     	cbz	x8, 0x100004bb8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x9fc>
100004b80:     	add	x11, x9, x8
100004b84:     	ldur	w11, [x11, #-0x4]
100004b88:     	add	x12, x10, x8
100004b8c:     	ldur	w12, [x12, #-0x4]
100004b90:     	cmp	w12, w11
100004b94:     	cset	w11, ne
100004b98:     	csinv	w11, w11, wzr, ls
100004b9c:     	sub	x8, x8, #0x4
100004ba0:     	cbz	w11, 0x100004b7c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x9c0>
100004ba4:     	cmp	w15, w11, sxtb
100004ba8:     	b.le	0x100004bc8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xa0c>
100004bac:     	add	w21, w21, #0x1
100004bb0:     	str	x21, [sp, #0x70]
100004bb4:     	b	0x100004cbc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xb00>
100004bb8:     	cmp	x8, #0x0
100004bbc:     	csetm	w11, ne
100004bc0:     	cmp	w15, w11, sxtb
100004bc4:     	b.gt	0x100004bac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x9f0>
100004bc8:     	cbz	x20, 0x100004c0c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xa50>
100004bcc:     	mov	x8, #0x0                ; =0
100004bd0:     	lsl	x9, x20, #2
100004bd4:     	add	x10, sp, #0x90
100004bd8:     	mov	w11, #0xa               ; =10
100004bdc:     	ldr	w12, [x10]
100004be0:     	umaddl	x8, w12, w11, x8
100004be4:     	str	w8, [x10], #0x4
100004be8:     	lsr	x8, x8, #32
100004bec:     	subs	x9, x9, #0x4
100004bf0:     	b.ne	0x100004bdc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xa20>
100004bf4:     	cbz	w8, 0x100004c0c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xa50>
100004bf8:     	cmp	x20, #0x28
100004bfc:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100004c00:     	add	x9, sp, #0x90
100004c04:     	str	w8, [x9, x20, lsl #2]
100004c08:     	add	x20, x20, #0x1
100004c0c:     	str	x20, [x25, #0xa0]
100004c10:     	add	x8, sp, #0x138
100004c14:     	ldr	x8, [x8, #0xa0]
100004c18:     	cmp	x8, #0x29
100004c1c:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004c20:     	cbz	x8, 0x100004c64 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xaa8>
100004c24:     	mov	x9, #0x0                ; =0
100004c28:     	lsl	x10, x8, #2
100004c2c:     	add	x11, sp, #0x138
100004c30:     	mov	w12, #0xa               ; =10
100004c34:     	ldr	w13, [x11]
100004c38:     	umaddl	x9, w13, w12, x9
100004c3c:     	str	w9, [x11], #0x4
100004c40:     	lsr	x9, x9, #32
100004c44:     	subs	x10, x10, #0x4
100004c48:     	b.ne	0x100004c34 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xa78>
100004c4c:     	cbz	w9, 0x100004c64 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xaa8>
100004c50:     	cmp	x8, #0x28
100004c54:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100004c58:     	add	x10, sp, #0x138
100004c5c:     	str	w9, [x10, x8, lsl #2]
100004c60:     	add	x8, x8, #0x1
100004c64:     	add	x9, sp, #0x138
100004c68:     	str	x8, [x9, #0xa0]
100004c6c:     	cbz	x28, 0x100004cb0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xaf4>
100004c70:     	mov	x8, #0x0                ; =0
100004c74:     	lsl	x9, x28, #2
100004c78:     	add	x10, sp, #0x1e0
100004c7c:     	mov	w11, #0xa               ; =10
100004c80:     	ldr	w12, [x10]
100004c84:     	umaddl	x8, w12, w11, x8
100004c88:     	str	w8, [x10], #0x4
100004c8c:     	lsr	x8, x8, #32
100004c90:     	subs	x9, x9, #0x4
100004c94:     	b.ne	0x100004c80 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xac4>
100004c98:     	cbz	w8, 0x100004cb0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xaf4>
100004c9c:     	cmp	x28, #0x28
100004ca0:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100004ca4:     	add	x9, sp, #0x1e0
100004ca8:     	str	w8, [x9, x28, lsl #2]
100004cac:     	add	x28, x28, #0x1
100004cb0:     	str	x21, [sp, #0x70]
100004cb4:     	add	x8, sp, #0x1e0
100004cb8:     	str	x28, [x8, #0xa0]
100004cbc:     	ldp	q0, q1, [x19, #0x60]
100004cc0:     	stp	q0, q1, [x22, #0x60]
100004cc4:     	ldp	q0, q1, [x19, #0x80]
100004cc8:     	stp	q0, q1, [x22, #0x80]
100004ccc:     	ldp	q0, q1, [x19, #0x20]
100004cd0:     	stp	q0, q1, [x22, #0x20]
100004cd4:     	ldp	q0, q1, [x19, #0x40]
100004cd8:     	stp	q0, q1, [x22, #0x40]
100004cdc:     	ldp	q0, q1, [x19]
100004ce0:     	stp	q0, q1, [x22]
100004ce4:     	str	x24, [x22, #0xa0]
100004ce8:     	add	x21, sp, #0x330
100004cec:     	add	x0, sp, #0x330
100004cf0:     	mov	w1, #0x1                ; =1
100004cf4:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004cf8:     	ldp	q0, q1, [x19, #0x60]
100004cfc:     	stp	q0, q1, [x22, #0x110]
100004d00:     	ldp	q0, q1, [x19, #0x80]
100004d04:     	stp	q0, q1, [x22, #0x130]
100004d08:     	ldp	q0, q1, [x19, #0x20]
100004d0c:     	stp	q0, q1, [x22, #0xd0]
100004d10:     	ldp	q0, q1, [x19, #0x40]
100004d14:     	stp	q0, q1, [x22, #0xf0]
100004d18:     	ldp	q0, q1, [x19]
100004d1c:     	stp	q0, q1, [x22, #0xb0]
100004d20:     	str	x24, [x22, #0x150]
100004d24:     	add	x26, sp, #0x3e0
100004d28:     	add	x0, sp, #0x3e0
100004d2c:     	mov	w1, #0x2                ; =2
100004d30:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004d34:     	ldp	q0, q1, [x19, #0x60]
100004d38:     	stp	q0, q1, [x22, #0x1c0]
100004d3c:     	ldp	q0, q1, [x19, #0x80]
100004d40:     	stp	q0, q1, [x22, #0x1e0]
100004d44:     	ldp	q0, q1, [x19, #0x20]
100004d48:     	stp	q0, q1, [x22, #0x180]
100004d4c:     	ldp	q0, q1, [x19, #0x40]
100004d50:     	stp	q0, q1, [x22, #0x1a0]
100004d54:     	ldp	q0, q1, [x19]
100004d58:     	stp	q0, q1, [x22, #0x160]
100004d5c:     	str	x24, [x22, #0x200]
100004d60:     	add	x27, sp, #0x490
100004d64:     	add	x0, sp, #0x490
100004d68:     	mov	w1, #0x3                ; =3
100004d6c:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
100004d70:     	ldr	x8, [x22, #0x200]
100004d74:     	cmp	x20, x8
100004d78:     	csel	x2, x20, x8, hi
100004d7c:     	cmp	x2, #0x28
100004d80:     	ldr	w30, [sp, #0x78]
100004d84:     	b.hi	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004d88:     	mov	x23, #0x0               ; =0
100004d8c:     	ldr	x9, [x22, #0x150]
100004d90:     	add	x10, sp, #0x7f
100004d94:     	mov	w11, #0xa               ; =10
100004d98:     	add	x12, sp, #0x1e0
100004d9c:     	ldr	x13, [x22, #0xa0]
100004da0:     	add	x14, sp, #0x138
100004da4:     	add	x15, sp, #0x90
100004da8:     	add	x16, sp, #0x288
100004dac:     	add	x17, sp, #0x540
100004db0:     	b	0x100004dd4 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc18>
100004db4:     	str	w0, [x12, x28, lsl #2]
100004db8:     	add	x28, x28, #0x1
100004dbc:     	add	x0, sp, #0x1e0
100004dc0:     	str	x28, [x0, #0xa0]
100004dc4:     	cmp	x20, x8
100004dc8:     	csel	x2, x20, x8, hi
100004dcc:     	cmp	x2, #0x28
100004dd0:     	b.hi	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004dd4:     	mov	x19, x23
100004dd8:     	lsl	x0, x2, #2
100004ddc:     	cbz	x0, 0x100004e5c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xca0>
100004de0:     	add	x1, x15, x0
100004de4:     	ldur	w1, [x1, #-0x4]
100004de8:     	add	x3, x27, x0
100004dec:     	ldur	w3, [x3, #-0x4]
100004df0:     	cmp	w3, w1
100004df4:     	cset	w1, ne
100004df8:     	csinv	w1, w1, wzr, ls
100004dfc:     	sub	x0, x0, #0x4
100004e00:     	cbz	w1, 0x100004ddc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc20>
100004e04:     	and	w0, w1, #0xff
100004e08:     	cmp	w0, #0x1
100004e0c:     	b.hi	0x100004e70 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xcb4>
100004e10:     	cbz	x2, 0x100004e50 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc94>
100004e14:     	mov	w1, #0x1                ; =1
100004e18:     	add	x0, sp, #0x490
100004e1c:     	add	x3, sp, #0x90
100004e20:     	mov	x4, x2
100004e24:     	ldr	w5, [x3]
100004e28:     	ldr	w6, [x0], #0x4
100004e2c:     	mvn	w6, w6
100004e30:     	and	w1, w1, #0x1
100004e34:     	cmp	w1, #0x1
100004e38:     	adcs	w5, w5, w6
100004e3c:     	cset	w1, hs
100004e40:     	str	w5, [x3], #0x4
100004e44:     	subs	x4, x4, #0x1
100004e48:     	b.ne	0x100004e24 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc68>
100004e4c:     	tbz	w1, #0x0, 0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
100004e50:     	str	x2, [x25, #0xa0]
100004e54:     	mov	w1, #0x8                ; =8
100004e58:     	b	0x100004e78 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xcbc>
100004e5c:     	cmp	x0, #0x0
100004e60:     	csetm	w1, ne
100004e64:     	and	w0, w1, #0xff
100004e68:     	cmp	w0, #0x1
100004e6c:     	b.ls	0x100004e10 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc54>
100004e70:     	mov	w1, #0x0                ; =0
100004e74:     	mov	x2, x20
100004e78:     	cmp	x2, x9
100004e7c:     	csel	x3, x2, x9, hi
100004e80:     	cmp	x3, #0x29
100004e84:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004e88:     	lsl	x0, x3, #2
100004e8c:     	cbz	x0, 0x100004f0c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd50>
100004e90:     	add	x4, x15, x0
100004e94:     	ldur	w4, [x4, #-0x4]
100004e98:     	add	x5, x26, x0
100004e9c:     	ldur	w5, [x5, #-0x4]
100004ea0:     	cmp	w5, w4
100004ea4:     	cset	w4, ne
100004ea8:     	csinv	w4, w4, wzr, ls
100004eac:     	sub	x0, x0, #0x4
100004eb0:     	cbz	w4, 0x100004e8c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xcd0>
100004eb4:     	and	w0, w4, #0xff
100004eb8:     	cmp	w0, #0x1
100004ebc:     	b.hi	0x100004f20 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd64>
100004ec0:     	cbz	x3, 0x100004f00 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd44>
100004ec4:     	mov	w2, #0x1                ; =1
100004ec8:     	add	x0, sp, #0x3e0
100004ecc:     	add	x4, sp, #0x90
100004ed0:     	mov	x5, x3
100004ed4:     	ldr	w6, [x4]
100004ed8:     	ldr	w7, [x0], #0x4
100004edc:     	mvn	w7, w7
100004ee0:     	and	w2, w2, #0x1
100004ee4:     	cmp	w2, #0x1
100004ee8:     	adcs	w6, w6, w7
100004eec:     	cset	w2, hs
100004ef0:     	str	w6, [x4], #0x4
100004ef4:     	subs	x5, x5, #0x1
100004ef8:     	b.ne	0x100004ed4 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd18>
100004efc:     	tbz	w2, #0x0, 0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
100004f00:     	str	x3, [x25, #0xa0]
100004f04:     	orr	w1, w1, #0x4
100004f08:     	b	0x100004f24 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd68>
100004f0c:     	cmp	x0, #0x0
100004f10:     	csetm	w4, ne
100004f14:     	and	w0, w4, #0xff
100004f18:     	cmp	w0, #0x1
100004f1c:     	b.ls	0x100004ec0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd04>
100004f20:     	mov	x3, x2
100004f24:     	cmp	x3, x13
100004f28:     	csel	x2, x3, x13, hi
100004f2c:     	cmp	x2, #0x29
100004f30:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004f34:     	lsl	x0, x2, #2
100004f38:     	cbz	x0, 0x100004fb8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xdfc>
100004f3c:     	add	x4, x15, x0
100004f40:     	ldur	w4, [x4, #-0x4]
100004f44:     	add	x5, x21, x0
100004f48:     	ldur	w5, [x5, #-0x4]
100004f4c:     	cmp	w5, w4
100004f50:     	cset	w4, ne
100004f54:     	csinv	w4, w4, wzr, ls
100004f58:     	sub	x0, x0, #0x4
100004f5c:     	cbz	w4, 0x100004f38 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xd7c>
100004f60:     	and	w0, w4, #0xff
100004f64:     	cmp	w0, #0x1
100004f68:     	b.hi	0x100004fcc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe10>
100004f6c:     	cbz	x2, 0x100004fac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xdf0>
100004f70:     	mov	w3, #0x1                ; =1
100004f74:     	add	x0, sp, #0x330
100004f78:     	add	x4, sp, #0x90
100004f7c:     	mov	x5, x2
100004f80:     	ldr	w6, [x4]
100004f84:     	ldr	w7, [x0], #0x4
100004f88:     	mvn	w7, w7
100004f8c:     	and	w3, w3, #0x1
100004f90:     	cmp	w3, #0x1
100004f94:     	adcs	w6, w6, w7
100004f98:     	cset	w3, hs
100004f9c:     	str	w6, [x4], #0x4
100004fa0:     	subs	x5, x5, #0x1
100004fa4:     	b.ne	0x100004f80 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xdc4>
100004fa8:     	tbz	w3, #0x0, 0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
100004fac:     	str	x2, [x25, #0xa0]
100004fb0:     	add	w1, w1, #0x2
100004fb4:     	b	0x100004fd0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe14>
100004fb8:     	cmp	x0, #0x0
100004fbc:     	csetm	w4, ne
100004fc0:     	and	w0, w4, #0xff
100004fc4:     	cmp	w0, #0x1
100004fc8:     	b.ls	0x100004f6c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xdb0>
100004fcc:     	mov	x2, x3
100004fd0:     	cmp	x2, x24
100004fd4:     	csel	x20, x2, x24, hi
100004fd8:     	cmp	x20, #0x29
100004fdc:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100004fe0:     	lsl	x0, x20, #2
100004fe4:     	cbz	x0, 0x100005064 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xea8>
100004fe8:     	add	x3, x15, x0
100004fec:     	ldur	w3, [x3, #-0x4]
100004ff0:     	add	x4, x16, x0
100004ff4:     	ldur	w4, [x4, #-0x4]
100004ff8:     	cmp	w4, w3
100004ffc:     	cset	w3, ne
100005000:     	csinv	w3, w3, wzr, ls
100005004:     	sub	x0, x0, #0x4
100005008:     	cbz	w3, 0x100004fe4 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe28>
10000500c:     	and	w0, w3, #0xff
100005010:     	cmp	w0, #0x1
100005014:     	b.hi	0x100005078 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xebc>
100005018:     	cbz	x20, 0x100005058 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe9c>
10000501c:     	mov	w2, #0x1                ; =1
100005020:     	add	x0, sp, #0x288
100005024:     	add	x3, sp, #0x90
100005028:     	mov	x4, x20
10000502c:     	ldr	w5, [x3]
100005030:     	ldr	w6, [x0], #0x4
100005034:     	mvn	w6, w6
100005038:     	and	w2, w2, #0x1
10000503c:     	cmp	w2, #0x1
100005040:     	adcs	w5, w5, w6
100005044:     	cset	w2, hs
100005048:     	str	w5, [x3], #0x4
10000504c:     	subs	x4, x4, #0x1
100005050:     	b.ne	0x10000502c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe70>
100005054:     	tbz	w2, #0x0, 0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
100005058:     	str	x20, [x25, #0xa0]
10000505c:     	add	w1, w1, #0x1
100005060:     	b	0x10000507c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xec0>
100005064:     	cmp	x0, #0x0
100005068:     	csetm	w3, ne
10000506c:     	and	w0, w3, #0xff
100005070:     	cmp	w0, #0x1
100005074:     	b.ls	0x100005018 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe5c>
100005078:     	mov	x20, x2
10000507c:     	cmp	x19, #0x11
100005080:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100005084:     	add	w0, w1, #0x30
100005088:     	strb	w0, [x10, x19]
10000508c:     	add	x0, sp, #0x138
100005090:     	ldr	x1, [x0, #0xa0]
100005094:     	cmp	x20, x1
100005098:     	csel	x0, x20, x1, hi
10000509c:     	cmp	x0, #0x29
1000050a0:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
1000050a4:     	add	x23, x19, #0x1
1000050a8:     	lsl	x0, x0, #2
1000050ac:     	cbz	x0, 0x1000050d8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xf1c>
1000050b0:     	add	x2, x15, x0
1000050b4:     	ldur	w2, [x2, #-0x4]
1000050b8:     	add	x3, x14, x0
1000050bc:     	ldur	w3, [x3, #-0x4]
1000050c0:     	cmp	w3, w2
1000050c4:     	cset	w2, ne
1000050c8:     	csinv	w2, w2, wzr, ls
1000050cc:     	sub	x0, x0, #0x4
1000050d0:     	cbz	w2, 0x1000050ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xef0>
1000050d4:     	b	0x1000050e0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xf24>
1000050d8:     	cmp	x0, #0x0
1000050dc:     	csetm	w2, ne
1000050e0:     	ldr	q0, [sp, #0xf0]
1000050e4:     	ldp	q1, q2, [x25, #0x70]
1000050e8:     	stp	q0, q1, [x22, #0x270]
1000050ec:     	ldr	q0, [x25, #0x90]
1000050f0:     	stp	q2, q0, [x22, #0x290]
1000050f4:     	ldp	q0, q1, [sp, #0xb0]
1000050f8:     	stp	q0, q1, [x22, #0x230]
1000050fc:     	ldp	q0, q1, [sp, #0xd0]
100005100:     	stp	q0, q1, [x22, #0x250]
100005104:     	ldp	q0, q1, [sp, #0x90]
100005108:     	stp	q0, q1, [x22, #0x210]
10000510c:     	cmp	x20, x28
100005110:     	csel	x0, x20, x28, hi
100005114:     	str	x20, [x22, #0x2b0]
100005118:     	cmp	x0, #0x28
10000511c:     	b.hi	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100005120:     	cbz	x0, 0x10000517c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xfc0>
100005124:     	mov	w3, #0x0                ; =0
100005128:     	add	x4, sp, #0x1e0
10000512c:     	add	x5, sp, #0x540
100005130:     	mov	x6, x0
100005134:     	ldr	w7, [x5]
100005138:     	ldr	w30, [x4], #0x4
10000513c:     	and	w3, w3, #0x1
100005140:     	cmp	w3, #0x1
100005144:     	adcs	w7, w7, w30
100005148:     	cset	w3, hs
10000514c:     	str	w7, [x5], #0x4
100005150:     	subs	x6, x6, #0x1
100005154:     	b.ne	0x100005134 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xf78>
100005158:     	tbz	w3, #0x0, 0x100005178 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xfbc>
10000515c:     	cmp	x0, #0x28
100005160:     	ldr	w30, [sp, #0x78]
100005164:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100005168:     	mov	w3, #0x1                ; =1
10000516c:     	str	w3, [x17, x0, lsl #2]
100005170:     	add	x0, x0, #0x1
100005174:     	b	0x10000517c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xfc0>
100005178:     	ldr	w30, [sp, #0x78]
10000517c:     	str	x0, [x22, #0x2b0]
100005180:     	cmp	x24, x0
100005184:     	csel	x0, x24, x0, hi
100005188:     	cmp	x0, #0x29
10000518c:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
100005190:     	lsl	x3, x0, #2
100005194:     	cbz	x3, 0x1000051c8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x100c>
100005198:     	add	x0, x16, x3
10000519c:     	ldur	w0, [x0, #-0x4]
1000051a0:     	add	x4, x17, x3
1000051a4:     	ldur	w4, [x4, #-0x4]
1000051a8:     	cmp	w4, w0
1000051ac:     	cset	w0, ne
1000051b0:     	csinv	w0, w0, wzr, ls
1000051b4:     	sub	x3, x3, #0x4
1000051b8:     	cbz	w0, 0x100005194 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xfd8>
1000051bc:     	cmp	w30, w2, sxtb
1000051c0:     	b.le	0x1000051d8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x101c>
1000051c4:     	b	0x10000529c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10e0>
1000051c8:     	cmp	x3, #0x0
1000051cc:     	csetm	w0, ne
1000051d0:     	cmp	w30, w2, sxtb
1000051d4:     	b.gt	0x10000529c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10e0>
1000051d8:     	cmp	w30, w0, sxtb
1000051dc:     	b.gt	0x10000529c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10e0>
1000051e0:     	cbz	x20, 0x10000521c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1060>
1000051e4:     	mov	x0, #0x0                ; =0
1000051e8:     	lsl	x2, x20, #2
1000051ec:     	add	x3, sp, #0x90
1000051f0:     	ldr	w4, [x3]
1000051f4:     	umaddl	x0, w4, w11, x0
1000051f8:     	str	w0, [x3], #0x4
1000051fc:     	lsr	x0, x0, #32
100005200:     	subs	x2, x2, #0x4
100005204:     	b.ne	0x1000051f0 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1034>
100005208:     	cbz	w0, 0x10000521c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1060>
10000520c:     	cmp	x20, #0x28
100005210:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100005214:     	str	w0, [x15, x20, lsl #2]
100005218:     	add	x20, x20, #0x1
10000521c:     	str	x20, [x25, #0xa0]
100005220:     	cbz	x1, 0x10000525c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10a0>
100005224:     	mov	x0, #0x0                ; =0
100005228:     	lsl	x2, x1, #2
10000522c:     	add	x3, sp, #0x138
100005230:     	ldr	w4, [x3]
100005234:     	umaddl	x0, w4, w11, x0
100005238:     	str	w0, [x3], #0x4
10000523c:     	lsr	x0, x0, #32
100005240:     	subs	x2, x2, #0x4
100005244:     	b.ne	0x100005230 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1074>
100005248:     	cbz	w0, 0x10000525c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10a0>
10000524c:     	cmp	x1, #0x28
100005250:     	b.eq	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100005254:     	str	w0, [x14, x1, lsl #2]
100005258:     	add	x1, x1, #0x1
10000525c:     	add	x0, sp, #0x138
100005260:     	str	x1, [x0, #0xa0]
100005264:     	cbz	x28, 0x100004dbc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc00>
100005268:     	mov	x0, #0x0                ; =0
10000526c:     	lsl	x1, x28, #2
100005270:     	add	x2, sp, #0x1e0
100005274:     	ldr	w3, [x2]
100005278:     	umaddl	x0, w3, w11, x0
10000527c:     	str	w0, [x2], #0x4
100005280:     	lsr	x0, x0, #32
100005284:     	subs	x1, x1, #0x4
100005288:     	b.ne	0x100005274 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10b8>
10000528c:     	cbz	w0, 0x100004dbc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xc00>
100005290:     	cmp	x28, #0x28
100005294:     	b.ne	0x100004db4 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xbf8>
100005298:     	bl	0x1000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>
10000529c:     	cmp	w30, w0, sxtb
1000052a0:     	ldp	x0, x21, [sp, #0x68]
1000052a4:     	b.le	0x100005394 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x11d8>
1000052a8:     	cmp	w30, w2, sxtb
1000052ac:     	b.le	0x10000532c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1170>
1000052b0:     	add	x20, sp, #0x90
1000052b4:     	add	x0, sp, #0x90
1000052b8:     	mov	w1, #0x1                ; =1
1000052bc:     	bl	0x100001a44 <__ZN4core3num6bignum8Big32x408mul_pow217h61862294584b67c5E>
1000052c0:     	ldr	x8, [x25, #0xa0]
1000052c4:     	cmp	x8, x24
1000052c8:     	csel	x8, x8, x24, hi
1000052cc:     	cmp	x8, #0x29
1000052d0:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
1000052d4:     	lsl	x8, x8, #2
1000052d8:     	add	x9, sp, #0x288
1000052dc:     	sub	x9, x9, #0x4
1000052e0:     	sub	x10, x20, #0x4
1000052e4:     	ldr	x0, [sp, #0x68]
1000052e8:     	cbz	x8, 0x100005318 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x115c>
1000052ec:     	ldr	w11, [x10, x8]
1000052f0:     	ldr	w12, [x9, x8]
1000052f4:     	cmp	w12, w11
1000052f8:     	cset	w11, ne
1000052fc:     	csinv	w11, w11, wzr, ls
100005300:     	sub	x8, x8, #0x4
100005304:     	cbz	w11, 0x1000052e8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x112c>
100005308:     	and	w8, w11, #0xff
10000530c:     	cmp	w8, #0x2
100005310:     	b.lo	0x10000532c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1170>
100005314:     	b	0x100005394 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x11d8>
100005318:     	cmp	x8, #0x0
10000531c:     	csetm	w11, ne
100005320:     	and	w8, w11, #0xff
100005324:     	cmp	w8, #0x2
100005328:     	b.hs	0x100005394 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x11d8>
10000532c:     	mov	x8, #0x0                ; =0
100005330:     	add	x9, sp, #0x7f
100005334:     	add	x9, x9, x19
100005338:     	add	x10, x19, x8
10000533c:     	cmn	x10, #0x1
100005340:     	b.eq	0x100005464 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12a8>
100005344:     	ldrb	w10, [x9, x8]
100005348:     	sub	x8, x8, #0x1
10000534c:     	cmp	w10, #0x39
100005350:     	b.eq	0x100005338 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x117c>
100005354:     	add	x9, sp, #0x7f
100005358:     	add	x10, x19, x8
10000535c:     	add	x11, x10, x9
100005360:     	ldrb	w12, [x11, #0x1]
100005364:     	add	w12, w12, #0x1
100005368:     	strb	w12, [x11, #0x1]
10000536c:     	add	x10, x10, #0x2
100005370:     	cmp	x10, x19
100005374:     	b.hi	0x100005394 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x11d8>
100005378:     	add	x9, x9, x19
10000537c:     	add	x9, x9, x8
100005380:     	add	x0, x9, #0x2
100005384:     	mvn	x2, x8
100005388:     	mov	w1, #0x30               ; =48
10000538c:     	bl	0x10000584c <_write+0x10000584c>
100005390:     	ldr	x0, [sp, #0x68]
100005394:     	cmp	x19, #0x11
100005398:     	b.hs	0x1000054a8 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12ec>
10000539c:     	ldp	x19, x4, [sp, #0x58]
1000053a0:     	ldrb	w8, [sp, #0x7f]
1000053a4:     	cmp	w8, #0x30
1000053a8:     	b.ls	0x1000054ac <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12f0>
1000053ac:     	sxth	w8, w21
1000053b0:     	cmp	w8, #0x1
1000053b4:     	b.lt	0x10000540c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1250>
1000053b8:     	mov	x8, x21
1000053bc:     	and	x8, x21, #0xffff
1000053c0:     	mov	w9, #0x2                ; =2
1000053c4:     	strh	w9, [x22, #0x210]
1000053c8:     	add	x11, sp, #0x7f
1000053cc:     	str	x11, [x22, #0x218]
1000053d0:     	subs	x10, x23, x8
1000053d4:     	b.ls	0x10000544c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x1290>
1000053d8:     	str	x8, [x22, #0x220]
1000053dc:     	strh	w9, [x22, #0x228]
1000053e0:     	adrp	x12, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
1000053e4:     	add	x12, x12, #0x630
1000053e8:     	str	x12, [x22, #0x230]
1000053ec:     	mov	w12, #0x1               ; =1
1000053f0:     	str	x12, [x22, #0x238]
1000053f4:     	add	x8, x11, x8
1000053f8:     	strh	w9, [x22, #0x240]
1000053fc:     	str	x8, [x22, #0x248]
100005400:     	mov	w8, #0x3                ; =3
100005404:     	str	x10, [x22, #0x250]
100005408:     	b	0x100004318 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x15c>
10000540c:     	mov	x8, #0x0                ; =0
100005410:     	mov	w9, #0x2                ; =2
100005414:     	strh	w9, [x22, #0x210]
100005418:     	adrp	x10, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
10000541c:     	add	x10, x10, #0x631
100005420:     	str	x10, [x22, #0x218]
100005424:     	str	x9, [x22, #0x220]
100005428:     	sub	x8, x8, w21, sxth
10000542c:     	strh	wzr, [x22, #0x228]
100005430:     	str	x8, [x22, #0x230]
100005434:     	strh	w9, [x22, #0x240]
100005438:     	add	x8, sp, #0x7f
10000543c:     	str	x8, [x22, #0x248]
100005440:     	str	x23, [x22, #0x250]
100005444:     	mov	w8, #0x3                ; =3
100005448:     	b	0x100004318 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x15c>
10000544c:     	str	x23, [x22, #0x220]
100005450:     	sub	x8, x8, x23
100005454:     	strh	wzr, [x22, #0x228]
100005458:     	str	x8, [x22, #0x230]
10000545c:     	mov	w8, #0x2                ; =2
100005460:     	b	0x100004318 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x15c>
100005464:     	mov	w8, #0x31               ; =49
100005468:     	strb	w8, [sp, #0x7f]
10000546c:     	cbz	x19, 0x100005490 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x12d4>
100005470:     	add	x8, sp, #0x7f
100005474:     	add	x0, x8, #0x1
100005478:     	mov	w1, #0x30               ; =48
10000547c:     	mov	x2, x19
100005480:     	bl	0x10000584c <_write+0x10000584c>
100005484:     	ldr	x0, [sp, #0x68]
100005488:     	cmp	x19, #0xf
10000548c:     	b.hi	0x100005298 <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x10dc>
100005490:     	add	x8, sp, #0x7f
100005494:     	mov	w9, #0x30               ; =48
100005498:     	strb	w9, [x8, x23]
10000549c:     	add	x23, x19, #0x2
1000054a0:     	add	w21, w21, #0x1
1000054a4:     	b	0x10000539c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0x11e0>
1000054a8:     	bl	0x1000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>
1000054ac:     	bl	0x1000057f8 <__ZN4core9panicking5panic17hff67cc28c73a35f9E>
1000054b0:     	mov	x4, #0x0                ; =0
1000054b4:     	mov	w14, #0x2               ; =2
1000054b8:     	mov	w19, #0x1               ; =1
1000054bc:     	b	0x10000429c <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E+0xe0>
1000054c0:     	bl	0x100005804 <__ZN4core9panicking13assert_failed17hc382478364c09037E>

00000001000054c4 <__ZN4core3fmt5float52_$LT$impl$u20$core..fmt..Display$u20$for$u20$f64$GT$3fmt17h8a93f864ab8372e5E>:
1000054c4:     	stp	x29, x30, [sp, #-0x10]!
1000054c8:     	mov	x29, sp
1000054cc:     	mov	x8, x1
1000054d0:     	ldr	d0, [x0]
1000054d4:     	ldr	w9, [x1, #0x34]
1000054d8:     	ldr	x10, [x1, #0x10]
1000054dc:     	cbz	x10, 0x1000054f4 <__ZN4core3fmt5float52_$LT$impl$u20$core..fmt..Display$u20$for$u20$f64$GT$3fmt17h8a93f864ab8372e5E+0x30>
1000054e0:     	ldr	x2, [x8, #0x18]
1000054e4:     	and	w1, w9, #0x1
1000054e8:     	mov	x0, x8
1000054ec:     	ldp	x29, x30, [sp], #0x10
1000054f0:     	b	0x1000031b0 <__ZN4core3fmt5float29float_to_decimal_common_exact17hc85b035023a03863E>
1000054f4:     	and	w1, w9, #0x1
1000054f8:     	mov	x0, x8
1000054fc:     	ldp	x29, x30, [sp], #0x10
100005500:     	b	0x1000041bc <__ZN4core3fmt5float32float_to_decimal_common_shortest17hba38c08fad32c4f0E>

0000000100005504 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE>:
100005504:     	sub	sp, sp, #0x40
100005508:     	stp	x29, x30, [sp, #0x30]
10000550c:     	add	x29, sp, #0x30
100005510:     	mov	x8, x1
100005514:     	ldr	x9, [x0]
100005518:     	cmp	x9, #0x0
10000551c:     	cneg	x11, x9, mi
100005520:     	lsr	x12, x11, #4
100005524:     	adrp	x10, 0x100006000 <__ZN4core3num7flt2dec8strategy6dragon8TWOPOW1017he92c8f938fff6b81E+0x8>
100005528:     	add	x10, x10, #0x63c
10000552c:     	cmp	x12, #0x271
100005530:     	b.lo	0x1000055b4 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0xb0>
100005534:     	mov	x12, #0x0               ; =0
100005538:     	mov	x13, #0x594b            ; =22859
10000553c:     	movk	x13, #0x3886, lsl #16
100005540:     	movk	x13, #0xc5d6, lsl #32
100005544:     	movk	x13, #0x346d, lsl #48
100005548:     	mov	w14, #0xd8f0            ; =55536
10000554c:     	mov	w15, #0x147b            ; =5243
100005550:     	mov	w16, #-0x64             ; =-100
100005554:     	add	x17, sp, #0x9
100005558:     	mov	w0, #0xe0ff             ; =57599
10000555c:     	movk	w0, #0x5f5, lsl #16
100005560:     	mov	x1, x11
100005564:     	umulh	x11, x11, x13
100005568:     	lsr	x11, x11, #11
10000556c:     	madd	w2, w11, w14, w1
100005570:     	ubfx	w3, w2, #2, #14
100005574:     	mul	w3, w3, w15
100005578:     	lsr	w3, w3, #17
10000557c:     	madd	w2, w3, w16, w2
100005580:     	and	x2, x2, #0xffff
100005584:     	add	x4, x17, x12
100005588:     	ldrh	w3, [x10, w3, uxtw #1]
10000558c:     	sturh	w3, [x4, #0x23]
100005590:     	ldrh	w2, [x10, x2, lsl #1]
100005594:     	sturh	w2, [x4, #0x25]
100005598:     	sub	x12, x12, #0x4
10000559c:     	cmp	x1, x0
1000055a0:     	b.hi	0x100005560 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0x5c>
1000055a4:     	add	x12, x12, #0x27
1000055a8:     	cmp	x11, #0x63
1000055ac:     	b.hi	0x1000055c0 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0xbc>
1000055b0:     	b	0x1000055f0 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0xec>
1000055b4:     	mov	w12, #0x27              ; =39
1000055b8:     	cmp	x11, #0x63
1000055bc:     	b.ls	0x1000055f0 <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0xec>
1000055c0:     	ubfx	w13, w11, #2, #14
1000055c4:     	mov	w14, #0x147b            ; =5243
1000055c8:     	mul	w13, w13, w14
1000055cc:     	lsr	w13, w13, #17
1000055d0:     	mov	w14, #-0x64             ; =-100
1000055d4:     	madd	w11, w13, w14, w11
1000055d8:     	and	x11, x11, #0xffff
1000055dc:     	sub	x12, x12, #0x2
1000055e0:     	ldrh	w11, [x10, x11, lsl #1]
1000055e4:     	add	x14, sp, #0x9
1000055e8:     	strh	w11, [x14, x12]
1000055ec:     	mov	x11, x13
1000055f0:     	cmp	x11, #0xa
1000055f4:     	b.hs	0x10000560c <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0x108>
1000055f8:     	sub	x12, x12, #0x1
1000055fc:     	orr	w10, w11, #0x30
100005600:     	add	x11, sp, #0x9
100005604:     	strb	w10, [x11, x12]
100005608:     	b	0x10000561c <__ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$i64$GT$3fmt17haf723e3a9c7f13eeE+0x118>
10000560c:     	sub	x12, x12, #0x2
100005610:     	ldrh	w10, [x10, x11, lsl #1]
100005614:     	add	x11, sp, #0x9
100005618:     	strh	w10, [x11, x12]
10000561c:     	add	x10, sp, #0x9
100005620:     	mov	w11, #0x27              ; =39
100005624:     	sub	x5, x11, x12
100005628:     	lsr	x9, x9, #63
10000562c:     	eor	w1, w9, #0x1
100005630:     	add	x4, x10, x12
100005634:     	mov	x0, x8
100005638:     	mov	w2, #0x1                ; =1
10000563c:     	mov	x3, #0x0                ; =0
100005640:     	bl	0x100001030 <__ZN4core3fmt9Formatter12pad_integral17hc8c783efba75376aE>
100005644:     	ldp	x29, x30, [sp, #0x30]
100005648:     	add	sp, sp, #0x40
10000564c:     	ret

0000000100005650 <__main>:
100005650:     	mov	w9, #0x4240             ; =16960
100005654:     	movk	w9, #0xf, lsl #16
100005658:     	cmp	x2, x9
10000565c:     	b.hi	0x1000056dc <__main+0x8c>
100005660:     	cbz	x2, 0x1000056e4 <__main+0x94>
100005664:     	mov	x8, x0
100005668:     	mov	x0, #0x0                ; =0
10000566c:     	mov	w9, #0x5                ; =5
100005670:     	mov	w10, #0x3               ; =3
100005674:     	mov	x11, #0x1ffffffff       ; =8589934591
100005678:     	mov	w12, #0x7               ; =7
10000567c:     	mov	w13, #0x63              ; =99
100005680:     	mov	x14, #0x1               ; =1
100005684:     	movk	x14, #0x2, lsl #32
100005688:     	mov	x15, #0x100000001       ; =4294967297
10000568c:     	eor	w16, w1, w8
100005690:     	ands	x17, x8, #0xffffffff00000000
100005694:     	add	x3, x17, x11
100005698:     	csel	x17, x3, x17, lt
10000569c:     	asr	x17, x17, #33
1000056a0:     	ands	x3, x1, #0xffffffff00000000
1000056a4:     	add	x4, x3, x11
1000056a8:     	csel	x3, x4, x3, lt
1000056ac:     	cmp	x17, x3, asr #33
1000056b0:     	csel	x17, x13, x12, eq
1000056b4:     	cmp	w16, #0x0
1000056b8:     	csel	x16, x10, x17, ne
1000056bc:     	cmp	x1, x8
1000056c0:     	csel	x16, x16, x9, ne
1000056c4:     	add	x0, x16, x0
1000056c8:     	add	x1, x1, x14
1000056cc:     	add	x8, x8, x15
1000056d0:     	subs	x2, x2, #0x1
1000056d4:     	b.ne	0x10000568c <__main+0x3c>
1000056d8:     	b	0x1000056e8 <__main+0x98>
1000056dc:     	mov	x0, #-0x2               ; =-2
1000056e0:     	b	0x1000056e8 <__main+0x98>
1000056e4:     	mov	x0, #0x0                ; =0
1000056e8:     	stp	x29, x30, [sp, #-0x10]!
1000056ec:     	bl	0x1000006f8 <__bril_print_int>
1000056f0:     	ldp	x29, x30, [sp], #0x10
1000056f4:     	b	0x100000990 <__bril_print_end>

00000001000056f8 <_main>:
1000056f8:     	stp	x22, x21, [sp, #-0x30]!
1000056fc:     	stp	x20, x19, [sp, #0x10]
100005700:     	stp	x29, x30, [sp, #0x20]
100005704:     	mov	x21, x1
100005708:     	ldr	x0, [x1, #0x8]
10000570c:     	bl	0x1000009a4 <__bril_parse_int>
100005710:     	mov	x19, x0
100005714:     	ldr	x0, [x21, #0x10]
100005718:     	bl	0x1000009a4 <__bril_parse_int>
10000571c:     	mov	x20, x0
100005720:     	ldr	x0, [x21, #0x18]
100005724:     	bl	0x1000009a4 <__bril_parse_int>
100005728:     	mov	w8, #0x4240             ; =16960
10000572c:     	movk	w8, #0xf, lsl #16
100005730:     	cmp	x0, x8
100005734:     	b.hi	0x1000057b0 <_main+0xb8>
100005738:     	mov	x8, #0x0                ; =0
10000573c:     	cbz	x0, 0x1000057b4 <_main+0xbc>
100005740:     	mov	w9, #0x5                ; =5
100005744:     	mov	w10, #0x3               ; =3
100005748:     	mov	x11, #0x1ffffffff       ; =8589934591
10000574c:     	mov	w12, #0x7               ; =7
100005750:     	mov	w13, #0x63              ; =99
100005754:     	mov	x14, #0x1               ; =1
100005758:     	movk	x14, #0x2, lsl #32
10000575c:     	mov	x15, #0x100000001       ; =4294967297
100005760:     	eor	w16, w20, w19
100005764:     	ands	x17, x19, #0xffffffff00000000
100005768:     	add	x1, x17, x11
10000576c:     	csel	x17, x1, x17, lt
100005770:     	asr	x17, x17, #33
100005774:     	ands	x1, x20, #0xffffffff00000000
100005778:     	add	x2, x1, x11
10000577c:     	csel	x1, x2, x1, lt
100005780:     	cmp	x17, x1, asr #33
100005784:     	csel	x17, x13, x12, eq
100005788:     	cmp	w16, #0x0
10000578c:     	csel	x16, x10, x17, ne
100005790:     	cmp	x20, x19
100005794:     	csel	x16, x16, x9, ne
100005798:     	add	x8, x16, x8
10000579c:     	add	x20, x20, x14
1000057a0:     	add	x19, x19, x15
1000057a4:     	subs	x0, x0, #0x1
1000057a8:     	b.ne	0x100005760 <_main+0x68>
1000057ac:     	b	0x1000057b4 <_main+0xbc>
1000057b0:     	mov	x8, #-0x2               ; =-2
1000057b4:     	mov	x0, x8
1000057b8:     	bl	0x1000006f8 <__bril_print_int>
1000057bc:     	bl	0x100000990 <__bril_print_end>
1000057c0:     	mov	w0, #0x0                ; =0
1000057c4:     	ldp	x29, x30, [sp, #0x20]
1000057c8:     	ldp	x20, x19, [sp, #0x10]
1000057cc:     	ldp	x22, x21, [sp], #0x30
1000057d0:     	ret

00000001000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>:
1000057d4:     	stp	x29, x30, [sp, #-0x10]!
1000057d8:     	mov	x29, sp
1000057dc:     	bl	0x100000c64 <_rust_begin_unwind>

00000001000057e0 <__ZN4core9panicking18panic_bounds_check17h491d401ca67c6c26E>:
1000057e0:     	stp	x29, x30, [sp, #-0x10]!
1000057e4:     	mov	x29, sp
1000057e8:     	bl	0x1000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>

00000001000057ec <__ZN4core5slice5index24slice_end_index_len_fail17hc8b3d86fa48bf46aE>:
1000057ec:     	stp	x29, x30, [sp, #-0x10]!
1000057f0:     	mov	x29, sp
1000057f4:     	bl	0x1000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>

00000001000057f8 <__ZN4core9panicking5panic17hff67cc28c73a35f9E>:
1000057f8:     	stp	x29, x30, [sp, #-0x10]!
1000057fc:     	mov	x29, sp
100005800:     	bl	0x1000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>

0000000100005804 <__ZN4core9panicking13assert_failed17hc382478364c09037E>:
100005804:     	stp	x29, x30, [sp, #-0x10]!
100005808:     	mov	x29, sp
10000580c:     	bl	0x100005810 <__ZN4core9panicking19assert_failed_inner17h3dc21f8685cb0550E>

0000000100005810 <__ZN4core9panicking19assert_failed_inner17h3dc21f8685cb0550E>:
100005810:     	stp	x29, x30, [sp, #-0x10]!
100005814:     	mov	x29, sp
100005818:     	bl	0x1000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>

000000010000581c <__ZN4core9panicking11panic_const23panic_const_div_by_zero17h71be41e2a26e0e82E>:
10000581c:     	stp	x29, x30, [sp, #-0x10]!
100005820:     	mov	x29, sp
100005824:     	bl	0x1000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>

0000000100005828 <__ZN4core6result13unwrap_failed17h172b8a6210fff28dE>:
100005828:     	stp	x29, x30, [sp, #-0x10]!
10000582c:     	mov	x29, sp
100005830:     	bl	0x1000057d4 <__ZN4core9panicking9panic_fmt17h02edc520ea153b34E>

Disassembly of section __TEXT,__stubs:

0000000100005834 <__stubs>:
100005834:     	adrp	x16, 0x10000c000 <_write+0x10000c000>
100005838:     	ldr	x16, [x16]
10000583c:     	br	x16
100005840:     	adrp	x16, 0x10000c000 <_write+0x10000c000>
100005844:     	ldr	x16, [x16, #0x8]
100005848:     	br	x16
10000584c:     	adrp	x16, 0x10000c000 <_write+0x10000c000>
100005850:     	ldr	x16, [x16, #0x10]
100005854:     	br	x16
100005858:     	adrp	x16, 0x10000c000 <_write+0x10000c000>
10000585c:     	ldr	x16, [x16, #0x18]
100005860:     	br	x16
100005864:     	adrp	x16, 0x10000c000 <_write+0x10000c000>
100005868:     	ldr	x16, [x16, #0x20]
10000586c:     	br	x16
