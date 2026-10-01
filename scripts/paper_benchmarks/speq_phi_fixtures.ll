; These small LLVM control-flow fixtures are analysis inputs, never executed.
; The scalar value and memory stores identify the actual branch arm independently
; of predecessor ordering. 0 is bypass, 11 is true-arm store, 22 is false-arm store.
define i32 @direct_true(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  br i1 %cond, label %merge, label %else
else:
  store i32 22, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 0, %entry ], [ 22, %else ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
define i32 @direct_true_reversed(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  br i1 %cond, label %merge, label %else
else:
  store i32 22, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 22, %else ], [ 0, %entry ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
define i32 @direct_false(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  br i1 %cond, label %then, label %merge
then:
  store i32 11, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 0, %entry ], [ 11, %then ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
define i32 @direct_false_reversed(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  br i1 %cond, label %then, label %merge
then:
  store i32 11, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 11, %then ], [ 0, %entry ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
define i32 @diamond(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  br i1 %cond, label %then, label %else
then:
  store i32 11, ptr %p
  br label %merge
else:
  store i32 22, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 11, %then ], [ 22, %else ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
define i32 @diamond_reversed(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  br i1 %cond, label %then, label %else
then:
  store i32 11, ptr %p
  br label %merge
else:
  store i32 22, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 22, %else ], [ 11, %then ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
define i32 @unsupported_switch(i1 %cond, ptr %p) {
entry:
  store i32 0, ptr %p
  switch i1 %cond, label %then [ i1 0, label %else ]
then:
  store i32 11, ptr %p
  br label %merge
else:
  store i32 22, ptr %p
  br label %merge
merge:
  %selected = phi i32 [ 11, %then ], [ 22, %else ]
  %loaded = load i32, ptr %p
  %out = add i32 %selected, %loaded
  ret i32 %out
}
