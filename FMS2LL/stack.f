20 constant stack-size

create stack stack-size cells allot

variable stack-depth

\ resets stack to zero items
: l-clr 0 stack-depth ! ; 
l-clr

: lsize ( -- sz) stack-depth @ ;

\ push item to stack LIFO
: >l ( n -- ) \ increase size of stack by 1
  stack-depth @ stack-size = if ." l-stack full" abort then
  stack stack-depth @ cells + !
  1 stack-depth +! ;

: check-empty stack-depth @ 0= if ." l-stack empty" abort then ;

\ retrieve top stack item
: l@ ( -- n ) \ size of stack remains unchanged
  check-empty
  stack stack-depth @ 1- cells + @ ;

\ pop top item from stack, LIFO
: l> ( -- n ) \ decrease size of stack by 1
  check-empty
  l@
  -1 stack-depth +! ;


\ print each object in the stack, useful for debugging
: .l stack-depth @ 0 ?do cr i . stack i cells + @ :. loop ;
