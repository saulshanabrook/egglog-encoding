define void @_main(i64 %v0, i64 %v1, i64 %v2) local_unnamed_addr #28 {
label0:
  %var7 = icmp ult i64 %v2, 1000001
  br i1 %var7, label %b13_, label %common.ret

b13_:                                             ; preds = %label0
  %var11.not = icmp eq i64 %v2, 0
  br i1 %var11.not, label %common.ret, label %b39_.preheader

b39_.preheader:                                   ; preds = %b13_
  %min.iters.check = icmp ult i64 %v2, 8
  br i1 %min.iters.check, label %b39_.preheader21, label %vector.ph

vector.ph:                                        ; preds = %b39_.preheader
  %n.vec = and i64 %v2, 1048568
  %0 = mul nuw nsw i64 %n.vec, 4294967297
  %ind.end = add i64 %0, %v0
  %1 = mul nuw nsw i64 %n.vec, 8589934593
  %ind.end1 = add i64 %1, %v1
  %.splatinsert = insertelement <2 x i64> poison, i64 %v0, i64 0
  %.splat = shufflevector <2 x i64> %.splatinsert, <2 x i64> poison, <2 x i32> zeroinitializer
  %induction = add <2 x i64> %.splat, <i64 0, i64 4294967297>
  %.splatinsert7 = insertelement <2 x i64> poison, i64 %v1, i64 0
  %.splat8 = shufflevector <2 x i64> %.splatinsert7, <2 x i64> poison, <2 x i32> zeroinitializer
  %induction9 = add <2 x i64> %.splat8, <i64 0, i64 8589934593>
  br label %vector.body

vector.body:                                      ; preds = %vector.body, %vector.ph
  %index = phi i64 [ 0, %vector.ph ], [ %index.next, %vector.body ]
  %vec.ind = phi <2 x i64> [ %induction, %vector.ph ], [ %vec.ind.next, %vector.body ]
  %vec.ind10 = phi <2 x i64> [ %induction9, %vector.ph ], [ %vec.ind.next15, %vector.body ]
  %vec.phi = phi <2 x i64> [ zeroinitializer, %vector.ph ], [ %26, %vector.body ]
  %vec.phi16 = phi <2 x i64> [ zeroinitializer, %vector.ph ], [ %27, %vector.body ]
  %vec.phi17 = phi <2 x i64> [ zeroinitializer, %vector.ph ], [ %28, %vector.body ]
  %vec.phi18 = phi <2 x i64> [ zeroinitializer, %vector.ph ], [ %29, %vector.body ]
  %step.add = add <2 x i64> %vec.ind, <i64 8589934594, i64 8589934594>
  %step.add4 = add <2 x i64> %vec.ind, <i64 17179869188, i64 17179869188>
  %step.add5 = add <2 x i64> %vec.ind, <i64 25769803782, i64 25769803782>
  %step.add11 = add <2 x i64> %vec.ind10, <i64 17179869186, i64 17179869186>
  %step.add12 = add <2 x i64> %vec.ind10, <i64 34359738372, i64 34359738372>
  %step.add13 = add <2 x i64> %vec.ind10, <i64 51539607558, i64 51539607558>
  %2 = icmp eq <2 x i64> %vec.ind10, %vec.ind
  %3 = icmp eq <2 x i64> %step.add11, %step.add
  %4 = icmp eq <2 x i64> %step.add12, %step.add4
  %5 = icmp eq <2 x i64> %step.add13, %step.add5
  %6 = xor <2 x i64> %vec.ind10, %vec.ind
  %7 = xor <2 x i64> %step.add11, %step.add
  %8 = xor <2 x i64> %step.add12, %step.add4
  %9 = xor <2 x i64> %step.add13, %step.add5
  %10 = and <2 x i64> %6, <i64 4294967295, i64 4294967295>
  %11 = and <2 x i64> %7, <i64 4294967295, i64 4294967295>
  %12 = and <2 x i64> %8, <i64 4294967295, i64 4294967295>
  %13 = and <2 x i64> %9, <i64 4294967295, i64 4294967295>
  %14 = icmp eq <2 x i64> %10, zeroinitializer
  %15 = icmp eq <2 x i64> %11, zeroinitializer
  %16 = icmp eq <2 x i64> %12, zeroinitializer
  %17 = icmp eq <2 x i64> %13, zeroinitializer
  %18 = select <2 x i1> %14, <2 x i64> <i64 7, i64 7>, <2 x i64> <i64 3, i64 3>
  %19 = select <2 x i1> %15, <2 x i64> <i64 7, i64 7>, <2 x i64> <i64 3, i64 3>
  %20 = select <2 x i1> %16, <2 x i64> <i64 7, i64 7>, <2 x i64> <i64 3, i64 3>
  %21 = select <2 x i1> %17, <2 x i64> <i64 7, i64 7>, <2 x i64> <i64 3, i64 3>
  %22 = select <2 x i1> %2, <2 x i64> <i64 5, i64 5>, <2 x i64> %18
  %23 = select <2 x i1> %3, <2 x i64> <i64 5, i64 5>, <2 x i64> %19
  %24 = select <2 x i1> %4, <2 x i64> <i64 5, i64 5>, <2 x i64> %20
  %25 = select <2 x i1> %5, <2 x i64> <i64 5, i64 5>, <2 x i64> %21
  %26 = add <2 x i64> %22, %vec.phi
  %27 = add <2 x i64> %23, %vec.phi16
  %28 = add <2 x i64> %24, %vec.phi17
  %29 = add <2 x i64> %25, %vec.phi18
  %index.next = add nuw i64 %index, 8
  %vec.ind.next = add <2 x i64> %vec.ind, <i64 34359738376, i64 34359738376>
  %vec.ind.next15 = add <2 x i64> %vec.ind10, <i64 68719476744, i64 68719476744>
  %30 = icmp eq i64 %index.next, %n.vec
  br i1 %30, label %middle.block, label %vector.body, !llvm.loop !6912

middle.block:                                     ; preds = %vector.body
  %bin.rdx = add <2 x i64> %27, %26
  %bin.rdx19 = add <2 x i64> %28, %bin.rdx
  %bin.rdx20 = add <2 x i64> %29, %bin.rdx19
  %31 = tail call i64 @llvm.vector.reduce.add.v2i64(<2 x i64> %bin.rdx20)
  %cmp.n = icmp eq i64 %n.vec, %v2
  br i1 %cmp.n, label %common.ret, label %b39_.preheader21

b39_.preheader21:                                 ; preds = %b39_.preheader, %middle.block
  %v34_.0.ph = phi i64 [ %v0, %b39_.preheader ], [ %ind.end, %middle.block ]
  %v32_.0.ph = phi i64 [ %v1, %b39_.preheader ], [ %ind.end1, %middle.block ]
  %v30_.0.ph = phi i64 [ 0, %b39_.preheader ], [ %n.vec, %middle.block ]
  %v29_.0.ph = phi i64 [ 0, %b39_.preheader ], [ %31, %middle.block ]
  br label %b39_

common.ret:                                       ; preds = %b39_, %middle.block, %b13_, %label0
  %var93.lcssa.sink = phi i64 [ -2, %label0 ], [ 0, %b13_ ], [ %31, %middle.block ], [ %var93, %b39_ ]
  tail call void @_bril_print_int(i64 %var93.lcssa.sink)
  tail call void @_bril_print_end()
  ret void

b39_:                                             ; preds = %b39_.preheader21, %b39_
  %v34_.0 = phi i64 [ %var102, %b39_ ], [ %v34_.0.ph, %b39_.preheader21 ]
  %v32_.0 = phi i64 [ %var99, %b39_ ], [ %v32_.0.ph, %b39_.preheader21 ]
  %v30_.0 = phi i64 [ %var96, %b39_ ], [ %v30_.0.ph, %b39_.preheader21 ]
  %v29_.0 = phi i64 [ %var93, %b39_ ], [ %v29_.0.ph, %b39_.preheader21 ]
  %var35 = icmp eq i64 %v32_.0, %v34_.0
  %32 = xor i64 %v32_.0, %v34_.0
  %33 = and i64 %32, 4294967295
  %var56 = icmp eq i64 %33, 0
  %. = select i1 %var56, i64 7, i64 3
  %v49_.0 = select i1 %var35, i64 5, i64 %.
  %var93 = add i64 %v49_.0, %v29_.0
  %var96 = add nuw nsw i64 %v30_.0, 1
  %var99 = add i64 %v32_.0, 8589934593
  %var102 = add i64 %v34_.0, 4294967297
  %exitcond.not = icmp eq i64 %var96, %v2
  br i1 %exitcond.not, label %common.ret, label %b39_, !llvm.loop !6913
}
