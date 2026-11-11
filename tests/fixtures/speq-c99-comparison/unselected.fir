
%for.body47 = λ ptr %B, i32 %j.210 .
  %add48 = add nuw nsw i32 %j.210, 2
  %mul49 = mul nsw i32 %i.212, %add48
  %rem50 = srem i32 %mul49, %nj
  %conv51 = sitofp i32 %rem50 to double
  %conv52 = sitofp i32 %nj to double
  %div53 = fdiv double %conv51, %conv52
  %idxprom54 = zext i32 %i.212 to i64
  %4 = mul nuw nsw i64 %idxprom54, %0
  %arrayidx55 = getelementptr inbounds double, ptr %B, i64 %4
  %idxprom56 = zext i32 %j.210 to i64
  %arrayidx57 = getelementptr inbounds double, ptr %arrayidx55, i64 %idxprom56
  %B.5 =  store double %div53, ptr %arrayidx57, align 8
  %inc59 = add nuw nsw i32 %j.210, 1
  %cmp45 = icmp slt i32 %inc59, %nj
(%B.5) = fold (ptr %B) %for.body47 Range(i32 0, i32 %nj)
pos: ()
crd: ()
val: ()
%for.body43 = λ ptr %B, i32 %i.212 .
  %cmp459 = icmp sgt i32 %nj, 0
  %B.7 = if ptr %cmp459 then %B.5 else %B
  %inc62 = add nuw nsw i32 %i.212, 1
  %cmp41 = icmp slt i32 %inc62, %nk
(%B.7) = fold (ptr %B.15) %for.body43 Range(i32 0, i32 %nk)
pos: ()
crd: ()
val: ()
%for.body23 = λ ptr %B, i32 %j.16 .
  %add24 = add nuw nsw i32 %j.16, 1
  %mul25 = mul nsw i32 %i.18, %add24
  %rem26 = srem i32 %mul25, %nk
  %conv27 = sitofp i32 %rem26 to double
  %conv28 = sitofp i32 %nk to double
  %div29 = fdiv double %conv27, %conv28
  %idxprom30 = zext i32 %i.18 to i64
  %3 = mul nuw nsw i64 %idxprom30, %1
  %arrayidx31 = getelementptr inbounds double, ptr %A, i64 %3
  %idxprom32 = zext i32 %j.16 to i64
  %arrayidx33 = getelementptr inbounds double, ptr %arrayidx31, i64 %idxprom32
  %B.4 =  store double %div29, ptr %arrayidx33, align 8
  %cmp21 = icmp slt i32 %add24, %nk
(%B.4) = fold (ptr %B) %for.body23 Range(i32 0, i32 %nk)
pos: ()
crd: ()
val: ()
%for.body19 = λ ptr %B, i32 %i.18 .
  %cmp215 = icmp sgt i32 %nk, 0
  %B.9 = if ptr %cmp215 then %B.4 else %B
  %inc38 = add nuw nsw i32 %i.18, 1
  %cmp17 = icmp slt i32 %inc38, %ni
(%B.9) = fold (ptr %B.17) %for.body19 Range(i32 0, i32 %ni)
pos: ()
crd: ()
val: ()
%for.body8 = λ ptr %B, i32 %j.02 .
  %mul = mul nsw i32 %i.04, %j.02
  %add9 = add nuw nsw i32 %mul, 1
  %rem = srem i32 %add9, %ni
  %conv = sitofp i32 %rem to double
  %conv10 = sitofp i32 %ni to double
  %div = fdiv double %conv, %conv10
  %idxprom = zext i32 %i.04 to i64
  %2 = mul nuw nsw i64 %idxprom, %0
  %arrayidx = getelementptr inbounds double, ptr %C, i64 %2
  %idxprom11 = zext i32 %j.02 to i64
  %arrayidx12 = getelementptr inbounds double, ptr %arrayidx, i64 %idxprom11
  %B.3 =  store double %div, ptr %arrayidx12, align 8
  %inc = add nuw nsw i32 %j.02, 1
  %cmp7 = icmp slt i32 %inc, %nj
(%B.3) = fold (ptr %B) %for.body8 Range(i32 0, i32 %nj)
pos: ()
crd: ()
val: ()
%for.body = λ ptr %B, i32 %i.04 .
  %cmp71 = icmp sgt i32 %nj, 0
  %B.13 = if ptr %cmp71 then %B.3 else %B
  %inc14 = add nuw nsw i32 %i.04, 1
  %cmp = icmp slt i32 %inc14, %ni
(%B.13) = fold (ptr %B.2) %for.body Range(i32 0, i32 %ni)
pos: ()
crd: ()
val: ()
