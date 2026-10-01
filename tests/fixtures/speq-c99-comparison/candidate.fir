
%for.body8 = λ ptr 1 double %C, i32 %j.02 .
  %0 = zext i32 %nj to i64
  %idxprom = zext i32 %i.09 to i64
  %2 = mul nuw nsw i64 %idxprom, %0
  %arrayidx = getelementptr inbounds double, ptr %C, i64 %2
  %idxprom9 = zext i32 %j.02 to i64
  %reproduction.c99.offset.0 = add nsw i64 %2, %idxprom9
  %arrayidx10 = getelementptr inbounds double, ptr %C, i64 %reproduction.c99.offset.0
  %3 = load double, ptr %arrayidx10, align 8
  %mul = fmul double %3, %beta
  %C.1 =  store double %mul, ptr %arrayidx10, align 8
  %inc = add nuw nsw i32 %j.02, 1
  %cmp7 = icmp slt i32 %inc, %nj
(%C.1) = fold (ptr 1 double %C) %for.body8 Range(i32 0, i32 %nj)
pos: ()
crd: ()
val: ()
%for.body16 = λ ptr 1 double %C, i32 %j.14 .
  %1 = zext i32 %nk to i64
  %0 = zext i32 %nj to i64
  %idxprom17 = zext i32 %i.09 to i64
  %4 = mul nuw nsw i64 %idxprom17, %1
  %arrayidx18 = getelementptr inbounds double, ptr %A, i64 %4
  %idxprom19 = zext i32 %k.06 to i64
  %reproduction.c99.offset.1 = add nsw i64 %4, %idxprom19
  %arrayidx20 = getelementptr inbounds double, ptr %A, i64 %reproduction.c99.offset.1
  %5 = load double, ptr %arrayidx20, align 8
  %mul21 = fmul double %5, %alpha
  %6 = mul nuw nsw i64 %idxprom19, %0
  %arrayidx23 = getelementptr inbounds double, ptr %B, i64 %6
  %idxprom24 = zext i32 %j.14 to i64
  %reproduction.c99.offset.2 = add nsw i64 %6, %idxprom24
  %arrayidx25 = getelementptr inbounds double, ptr %B, i64 %reproduction.c99.offset.2
  %7 = load double, ptr %arrayidx25, align 8
  %8 = mul nuw nsw i64 %idxprom17, %0
  %arrayidx28 = getelementptr inbounds double, ptr %C, i64 %8
  %reproduction.c99.offset.3 = add nsw i64 %8, %idxprom24
  %arrayidx30 = getelementptr inbounds double, ptr %C, i64 %reproduction.c99.offset.3
  %9 = load double, ptr %arrayidx30, align 8
  %10 = call double @llvm.fmuladd.f64(double %mul21, double %7, double %9)
  %C.2 =  store double %10, ptr %arrayidx30, align 8
  %inc32 = add nuw nsw i32 %j.14, 1
  %cmp15 = icmp slt i32 %inc32, %nj
(%C.2) = fold (ptr 1 double %C) %for.body16 Range(i32 0, i32 %nj)
pos: ()
crd: ()
val: ()
%for.body13 = λ ptr 1 double %C, i32 %k.06 .
  %C.4 = if ptr 1 double %cmp71 then %C.2 else %C
  %inc35 = add nuw nsw i32 %k.06, 1
  %cmp12 = icmp slt i32 %inc35, %nk
(%C.4) = fold (ptr 1 double %C.8) %for.body13 Range(i32 0, i32 %nk)
pos: ()
crd: ()
val: ()
%for.body = λ ptr 1 double %C, i32 %i.09 .
  %cmp71 = icmp sgt i32 %nj, 0
  %C.8 = if ptr 1 double %cmp71 then %C.1 else %C
  %cmp125 = icmp sgt i32 %nk, 0
  %C.6 = if ptr 1 double %cmp125 then %C.4 else %C.8
  %inc38 = add nuw nsw i32 %i.09, 1
  %cmp = icmp slt i32 %inc38, %ni
(%C.6) = fold (ptr 1 double %C) %for.body Range(i32 0, i32 %ni)
pos: ()
crd: ()
val: ()
