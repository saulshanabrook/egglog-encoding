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
  %var37 = add i64 %v4, %v2
  %var40 = add i64 %v5, %v0
  %var43 = icmp eq i64 %var37, %var40
  %. = select i1 %var43, i64 5, i64 7
  %.sink = select i1 %var26, i64 %., i64 3
  tail call void @_bril_print_int(i64 %.sink)
  tail call void @_bril_print_end()
  ret void
}
