

\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Dec 11 2020 Douglas B. Hoffman
\ dhoffman888@gmail.com


[undefined] floats [if]
cr .( Floating Point is required) abort
[then]

[undefined] .l [if]
20 array l
: >l ( n -- ) \ push item on stack
  l :add ;
: l> ( -- n ) \ pop item from stack, last in first out
  l :size 1- l :remove ;
: .l l :. ;
: l@ ( -- n ) l :last ; \ retrieve top stack item
: l-clr l :clear ; \ resets stack to zero items
[then]

0 [if]
l-clr ok
4 >l 3 >l 2 >l 1 >l ok
.l 
0 4 
1 3 
2 2 
3 1 ok
[then]



\ remove the leading and trailing "'"s from string-objects created
\ using the o{ ... } syntax
: :dequote ( str-obj -- ) >r
   s" '" s" " r> :replall ;


:class obj-array <super array

 :m :. cr  ." { "
       begin
         self :each
       while
         dup is-a string
         if [char] ' emit :. [char] ' emit space
         else :. space
         then
       repeat ." } " ;m 
;class
 

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
      0= if l :size 0>
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
	                     if r> dup :dequote list :add
	                     else 32 r@ :ch+ [char] ' parse r@ :add  r@ :dequote r> list :add
	                     then
	                   else cr r> :. l-clr
	                        true abort" invalid token in {..} list"
	                   then
	                  
	             then
	      then
	 then
  repeat 2drop
         l :size if l-clr
                           true abort" unmatched {..} pair in list"
                        then 
  list ;


: dict{ ( n -- list ) \ list allocated in the dictionary with room for n elements
  dict> obj-array locals| list |
  begin
    refilling-parse-name
      begin
       2dup s" {" compare 0=
      while 
       2drop list >l recurse
      repeat
    2dup s" }" compare
      0= if l :size 0>
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
             :@ 1+ ?do i dict> int list :add loop 2drop
          else
            2dup >float 
            if 
              1e f- f>s ( end-of-range )
             list :last 
             dup is-a flt 0= abort" .. expected a fp range start"
             ( end-of-range flt-obj )
             :@ 1+ f>s list :last :@ ?do 1e f+ fdup  dict> flt list :add loop fdrop
             2drop
            else
             2drop
            then 
          then
     else
	    2dup >integer
	      if  dict> int list :add 2drop
	      else 2dup >float 
	             if  dict> flt list :add 2drop
	             else >string >r 
	                  r@ :first [char] ' =
	                  if r@ :last [char] ' =
	                     if r> dup :dequote list :add
	                     else 32 r@ :ch+ [char] ' parse r@ :add  r@ :dequote r@ :@ dup dict> string list :add r> <free
	                     then
	                   else cr r> :. l-clr
	                        true abort" invalid token in {..} list"
	                   then
	                  
	             then
	      then
	 then
  repeat 2drop
         l :size if l-clr
                           true abort" unmatched {..} pair in list"
                        then 
  list ;

