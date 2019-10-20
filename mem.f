\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Oct 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com

50000 constant mem-size \ choose a large enough size

create mem-list mem-size cells allot
mem-list mem-size cells erase 

: list-bounds ( -- end beg ) mem-list mem-size cells +  mem-list ;

: store-ptr ( ptr -- )
  list-bounds do i @ 0= if i ! unloop exit then cell +loop
  true abort" no room left in mem-list" ;

: allocate ( n -- ptr ior )
  allocate 
  2dup 0=
  if store-ptr
  else drop
  then ;

: free-ptr ( ptr -- )
  list-bounds do dup i @ = if 0 i ! drop unloop exit then
             cell +loop ;

: free ( ptr -- ior )
  dup free dup 0= 
  if
    swap
    ( ior ptr ) free-ptr
  then ;

: resize-mem ( ptr2 ptr1 -- )
  list-bounds do dup i @ = if drop i ! unloop exit then
             cell +loop ;

: resize ( ptr1 n -- ptr2 ior | ptr1 ior )
  over >r  
  resize 
  dup 0=
  if ( ptr2 ior  )
    swap dup ( ior ptr2 ptr2 ) r@ = if r> drop ( ior ptr1 ) swap exit
                  else 
                  ( ior ptr2 ) r@ ( ior ptr2 ptr1 ) over >r resize-mem r> ( ior ptr2)
                  then
  then r> drop swap ;

: .mem 0 locals| cnt |
  list-bounds do i @ if cr cnt . i @ . cnt 1+ to cnt then
             cell +loop cr cnt . ." unFREEd pointers " ;

: clr-mem
  list-bounds do i @ if  i @ free throw 0 i ! then
             cell +loop ;
 

