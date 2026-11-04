define void @_main(i64 %v0, i64 %v1, i64 %v2, i64 %v3, i64 %v4, i64 %v5, i64 %v6, i64 %v7) local_unnamed_addr #28 {
label0:
  %var1 = icmp slt i64 %v6, %v7
  %var4 = select i1 %var1, i64 %v0, i64 %v1
  %var8 = select i1 %var1, i64 %v2, i64 %v3
  %var12 = icmp eq i64 %var8, %var4
  %var15 = select i1 %var1, i64 %v1, i64 %v0
  %var19 = select i1 %var1, i64 %v3, i64 %v2
  %var23 = icmp eq i64 %var15, %var19
  %var26 = select i1 %var12, i1 %var23, i1 false
  br i1 %var26, label %b23_, label %common.ret

b23_:                                             ; preds = %label0
  %var37 = add i64 %v4, %v2
  %var40 = add i64 %v5, %v0
  %var43 = icmp eq i64 %var37, %var40
  br i1 %var43, label %common.ret, label %b29_

b29_:                                             ; preds = %b23_
  %var59 = icmp eq i64 %v4, %v5
  %spec.select = select i1 %var59, i64 99, i64 7
  br label %common.ret

common.ret:                                       ; preds = %b29_, %b23_, %label0
  %.sink = phi i64 [ 3, %label0 ], [ 5, %b23_ ], [ %spec.select, %b29_ ]
  tail call void @_bril_print_int(i64 %.sink)
  tail call void @_bril_print_end()
  ret void
}
