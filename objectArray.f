\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Oct 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com


[undefined] floats [if]
cr .( Floating Point is required) abort
[then]


20 constant max-lstack-size
create lstack max-lstack-size cells allot

variable lstack-depth
0 lstack-depth !
 
: >l ( n -- ) \ push item on stack
  lstack-depth @ 1+ max-lstack-size  > ABORT" l-stack full"
  lstack lstack-depth @ cells + !
  1 lstack-depth +! ;

: ?lstackEmpty lstack-depth @ 0= ABORT" l-stack empty" ;
: l@ ( -- n ) \ retrieve top stack item
  ?lstackEmpty  lstack lstack-depth @ 1- cells + @ ;
: l> ( -- n ) \ pop item from stack, last in first out
  ?lstackEmpty  l@  -1 lstack-depth +! ;


: cleanup-list ( list -- )
  <free
  lstack-depth @  0 ?do l> <free loop
  0 lstack-depth ! ; \ redundant?

:class int  
  cell bytes data 
 :m :init ( n -- ) data ! ;m
 :m :! ( n -- )  data ! ;m
 :m :@ ( -- n )  data @ ;m
 :m :.  self :@ . ;m \ print self
 :m := ( obj -- flag ) :@ self :@ = ;m
 :m :> ( obj -- flag ) :@ self :@ > ;m
;class

: >int ( n -- obj ) heap> int ;

:class flt   
  1 floats bytes data
 :m :init ( R: r -- ) data f! ;m
 :m :! ( R: r -- )  data f! ;m
 :m :@ ( R: -- r )  data f@ ;m
 :m :. self :@ f. ;m \ print self
 :m := ( obj -- flag ) :@ self :@ f= ;m
 [undefined] f> [if] : f> ( -- f ) ( F: r1 r2 --) f- f0< invert ; [then]
 :m :> ( obj -- flag ) :@ self :@ f> ;m
;class

: >flt ( -- obj ) ( F: r -- ) heap> flt ;
 

:class obj-array <super array
 :m :. cr  ." { "
       begin
         self :each
       while
         :. 
       repeat ." } " ;m 
;class

: >oArray ( -- arr ) heap> obj-array ;

: o{ ( -- list ) \ list allocated in the heap
  heap> obj-array locals| list |
  begin
    refilling-parse-name
      begin
       2dup s" {" compare 0=
      while 
       2drop list >l recurse
      repeat
    2dup s" }" compare
      0= if lstack-depth @ 0>
            if list l> :add  2drop refilling-parse-name exit
            else false
            then
         else true
         then
  while
    ( addr len )
    2dup s" .." compare 0=
     if \ we have a range
       2drop refilling-parse-name
          2dup >integer
          if 
             1+ ( end-of-range )
             list :last 
             dup is-a int 0= abort" .. expected an integer range start"
             ( end-of-range int-obj )
             :@ 1+ ?do i >int list :add loop 2drop
          else
            2dup >float 
            if 
              1e f- f>s ( end-of-range )
             list :last 
             dup is-a flt 0= abort" .. expected a fp range start"
             ( end-of-range flt-obj )
             :@ 1+ f>s list :last :@ ?do 1e f+ fdup  >flt list :add loop fdrop
             2drop
            else
             2drop
            then 
          then
     else
	    2dup >integer
	      if  >int list :add 2drop
	      else 2dup >float 
	             if  >flt list :add 2drop
	             else >string >r 
	                  r@ :first [char] ' =
	                  if r@ :last [char] ' =
	                     if r> list :add
	                     else 32 r@ :ch+ [char] ' parse r@ :add [char] ' r@ :ch+ r> list :add
	                     then
	                   else cr r> :. list cleanup-list
	                        true abort" invalid token in {..} list"
	                   then
	                  
	             then
	      then
	 then
  repeat 2drop
         lstack-depth @ if list cleanup-list
                           true abort" unmatched {..} pair in list"
                        then 
  list ;
 

\ remove the leading and trailing "'"s from string-objects created
\ using the o{ ... } syntax
: :dequote ( str-obj -- ) >r
   s" '" s" " r> :replall ;


