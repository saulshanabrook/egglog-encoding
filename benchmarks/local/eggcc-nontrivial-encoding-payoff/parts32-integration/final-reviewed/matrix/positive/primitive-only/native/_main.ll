define void @_main(i64 %v0, i64 %v1, i64 %v2) local_unnamed_addr #28 {
label0:
  %var7 = icmp ult i64 %v2, 1000001
  br i1 %var7, label %b13_, label %common.ret

b13_:                                             ; preds = %label0
  %var11.not = icmp eq i64 %v2, 0
  br i1 %var11.not, label %common.ret, label %b39_

common.ret:                                       ; preds = %b53_, %b13_, %label0
  %var131.lcssa.sink = phi i64 [ -2, %label0 ], [ 0, %b13_ ], [ %var131, %b53_ ]
  tail call void @_bril_print_int(i64 %var131.lcssa.sink)
  tail call void @_bril_print_end()
  ret void

b39_:                                             ; preds = %b13_, %b53_
  %v34_.0 = phi i64 [ %var140, %b53_ ], [ %v0, %b13_ ]
  %v32_.0 = phi i64 [ %var137, %b53_ ], [ %v1, %b13_ ]
  %v30_.0 = phi i64 [ %var134, %b53_ ], [ 0, %b13_ ]
  %v29_.0 = phi i64 [ %var131, %b53_ ], [ 0, %b13_ ]
  %var35 = icmp eq i64 %v32_.0, %v34_.0
  br i1 %var35, label %b53_, label %b54_

b53_:                                             ; preds = %b54_, %b70_, %b39_
  %v49_.0 = phi i64 [ 5, %b39_ ], [ %., %b70_ ], [ 3, %b54_ ]
  %var131 = add i64 %v49_.0, %v29_.0
  %var134 = add nuw nsw i64 %v30_.0, 1
  %var137 = add i64 %v32_.0, 8589934593
  %var140 = add i64 %v34_.0, 4294967297
  %exitcond.not = icmp eq i64 %var134, %v2
  br i1 %exitcond.not, label %common.ret, label %b39_

b54_:                                             ; preds = %b39_
  %0 = xor i64 %v32_.0, %v34_.0
  %1 = and i64 %0, 4294967295
  %var56 = icmp eq i64 %1, 0
  br i1 %var56, label %b70_, label %b53_

b70_:                                             ; preds = %b54_
  %var83 = icmp ult i64 %0, 4294967296
  %. = select i1 %var83, i64 99, i64 7
  br label %b53_
}
