define noundef i32 @main(i32 %argc, ptr nocapture readonly %argv) local_unnamed_addr #28 {
label209:
  %"calculate offset" = getelementptr inbounds ptr, ptr %argv, i64 1
  %"load arg" = load ptr, ptr %"calculate offset", align 8
  %parse_int = tail call i64 @_bril_parse_int(ptr %"load arg")
  %"calculate offset1" = getelementptr inbounds ptr, ptr %argv, i64 2
  %"load arg2" = load ptr, ptr %"calculate offset1", align 8
  %parse_int3 = tail call i64 @_bril_parse_int(ptr %"load arg2")
  %"calculate offset4" = getelementptr inbounds ptr, ptr %argv, i64 3
  %"load arg5" = load ptr, ptr %"calculate offset4", align 8
  %parse_int6 = tail call i64 @_bril_parse_int(ptr %"load arg5")
  %var7.i = icmp ult i64 %parse_int6, 1000001
  br i1 %var7.i, label %b13_.i, label %_main.exit

b13_.i:                                           ; preds = %label209
  %var11.not.i = icmp eq i64 %parse_int6, 0
  br i1 %var11.not.i, label %_main.exit, label %b39_.i

b39_.i:                                           ; preds = %b13_.i, %b53_.i
  %v34_.0.i = phi i64 [ %var140.i, %b53_.i ], [ %parse_int, %b13_.i ]
  %v32_.0.i = phi i64 [ %var137.i, %b53_.i ], [ %parse_int3, %b13_.i ]
  %v30_.0.i = phi i64 [ %var134.i, %b53_.i ], [ 0, %b13_.i ]
  %v29_.0.i = phi i64 [ %var131.i, %b53_.i ], [ 0, %b13_.i ]
  %var35.i = icmp eq i64 %v32_.0.i, %v34_.0.i
  br i1 %var35.i, label %b53_.i, label %b54_.i

b53_.i:                                           ; preds = %b70_.i, %b54_.i, %b39_.i
  %v49_.0.i = phi i64 [ 5, %b39_.i ], [ %..i, %b70_.i ], [ 3, %b54_.i ]
  %var131.i = add i64 %v49_.0.i, %v29_.0.i
  %var134.i = add nuw nsw i64 %v30_.0.i, 1
  %var137.i = add i64 %v32_.0.i, 8589934593
  %var140.i = add i64 %v34_.0.i, 4294967297
  %exitcond.not.i = icmp eq i64 %var134.i, %parse_int6
  br i1 %exitcond.not.i, label %_main.exit, label %b39_.i

b54_.i:                                           ; preds = %b39_.i
  %0 = xor i64 %v32_.0.i, %v34_.0.i
  %1 = and i64 %0, 4294967295
  %var56.i = icmp eq i64 %1, 0
  br i1 %var56.i, label %b70_.i, label %b53_.i

b70_.i:                                           ; preds = %b54_.i
  %var83.i = icmp ult i64 %0, 4294967296
  %..i = select i1 %var83.i, i64 99, i64 7
  br label %b53_.i

_main.exit:                                       ; preds = %b53_.i, %label209, %b13_.i
  %var131.lcssa.sink.i = phi i64 [ -2, %label209 ], [ 0, %b13_.i ], [ %var131.i, %b53_.i ]
  tail call void @_bril_print_int(i64 %var131.lcssa.sink.i)
  tail call void @_bril_print_end()
  ret i32 0
}
