; Analysis input only: guarded row scaling with the actual C99 stride shape.
; The dimension and row can be negative/zero; those paths must leave C unchanged.
target datalayout = "e-p:64:64-i64:64-n8:16:32:64-S128"

define void @unsupported_i16(ptr %C, i16 %n, i16 %row, double %scale) {
entry:
  %n64 = zext i16 %n to i64
  %row64 = zext i16 %row to i64
  %positive = icmp sgt i16 %n, 0
  br i1 %positive, label %rowguard, label %exit
rowguard:
  %row.valid = icmp sge i16 %row, 0
  br i1 %row.valid, label %preheader, label %exit
preheader:
  br label %body
body:
  %j = phi i16 [ 0, %preheader ], [ %next, %body ]
  %row.offset = mul nuw nsw i64 %row64, %n64
  %row.ptr = getelementptr inbounds double, ptr %C, i64 %row.offset
  %j64 = zext i16 %j to i64
  %element = getelementptr inbounds double, ptr %row.ptr, i64 %j64
  %old = load double, ptr %element, align 8
  %scaled = fmul double %old, %scale
  store double %scaled, ptr %element, align 8
  %next = add nuw nsw i16 %j, 1
  %more = icmp slt i16 %next, %n
  br i1 %more, label %body, label %exit
exit:
  ret void
}
