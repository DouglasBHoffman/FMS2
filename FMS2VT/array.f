
\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Jan 25 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com

\ removed extra [then] in conditional compilation

\ Last Revision: 21 Dec 2019  04:56:21  dbh
\ defined HOF :apply prior to class array (required)


[undefined] ptr [if] .( file ptr.f required ) [then]

[undefined] -cell [if]
   -1 cells constant -cell [then]
[undefined] cell- [if]
: cell- ( addr -- addr-cell ) -cell + ; 
[then]

\ very common messages should be defined first
make-selector :!
make-selector :@
make-selector :.
make-selector :at
make-selector :uneach
make-selector :each

\ HOF

\ replaces ordered-col when used with >dict
:class array <super ptr \ ( max#elems -- ) dict>  or  ( -- ) heap>
 \ len will become maxsize for a static array
     \ len = max number of elems for the static array
  1 bytes alloc? \ an alloc object will be allocated in the heap
  cell bytes current-idx
  cell bytes #elems 
  cell bytes elemSize

  : ?idx ( idx -- idx )
    dup 0 #elems @ within 0= abort" array index out of range" ;

fmsCheck? [if] 
  : ^elem ( idx -- addr ) ?idx elemSize @ * data @  + ;
[else] 
  : ^elem ( idx -- addr ) elemSize @ * data @  + ;
[then]
 :f :^elem ( idx -- addr ) ^elem ;f
 : check ( n --) len @ > abort" array maxsize exceeded" ;
 : (resize) ( #elems -- )
    alloc? c@
    if dup  #elems !  elemSize @ * super :resize 
    else
       dup check #elems !
    then ;

 :m :delete ( idx -- ) \ delete elem at idx and shrink array by 1 cell
    dup 1+  #elems @ <>
    if dup >r 1+  ^elem ( src)
           r@  ^elem ( dest)  #elems @ r> -  elemSize @ * ( len) move
    else drop
    then #elems @ 1 - (resize) ;m

 :m :clear \ reset the array size to zero
\    ['] <free self :apply
    0 #elems !
    0 current-idx !
    alloc? c@ if 0 super :resize then ;m

 :m :remove ( idx -- elem )
    dup self :at 
    swap eself :delete ;m

 :m :uneach 0  current-idx ! ;m

 :m :init \ ( -- ) or if static: ( max#elems --)
    ?alloc dup  alloc? c!
    if  0 super :init 
    else ( max#elems ) dup len ! cells align here swap allot data !
    then
    0 #elems !
     cell  elemSize !
     eself :uneach
     ;m

 :m :@elem ( addr -- elem ) @ ;m

 :m :each ( -- elem true | false)
     current-idx @ dup  #elems @ <
    if 1  current-idx +!  ^elem self :@elem true else drop eself :uneach false then ;m

 :m :size ( -- n)  #elems @ ;m
 :m :to ( elem idx -- )  ^elem  ! ;m
 :m :at ( idx -- elem )  ^elem  @ ;m
 :m .elem ( elem -- ) . ;m
 :m :.  #elems @ 0 ?do cr i dup . self :at self .elem loop ;m
    
 :m :add ( n -- ) \ increase size of array by one and place n in last position
    #elems @ dup 1+ (resize)
    self :to ;m 
 
 :m :insert ( n idx -- ) \ increase size of array by one, place n at given index position
                         \ after having moved all ensuing elements up by one position.
    >r
    #elems @ 1+ (resize)
    r@ ^elem ( src) r@ 1+ ^elem ( dest) eself :size r@ - elemSize @ * ( len) move
    r> self :to 
    ;m

\ quicksort is based on Wil Baden's code, for sorting integers

: mid ( l r -- mid ) over - 2/ -cell and + ;

: exch ( addr1 addr2 -- ) dup @ >r over @ swap ! r> swap ! ;

: part ( l r xt -- l r r2 l2 )
  locals| xt |
  2dup mid @ >r ( r: pivot )
  2dup begin
    swap begin dup @  r@ xt execute while cell+ repeat
    swap begin r@ over @ xt execute while cell- repeat
    2dup <= if 2dup exch >r cell+ r> cell- then
  2dup > until  r> drop ;

: qsort ( l r xt -- )
  locals| xt |
  xt part  swap rot
  2dup < if xt recurse else 2drop then
  2dup < if xt recurse else 2drop then ;

\ use ' < to sort into ascending integers
 :m :sortWith ( xt -- ) \ performs a quicksort using the sort-xt for comparisons
    locals| xt |
    0 ^elem #elems @ ( array len -- )
    dup 2 < if 2drop exit then
    1- cells over + xt qsort ;m

\ :sort always sorts in ascending order
 :m :sort ['] < self :sortWith ;m

 :m :+ ( array -- ) \ concatenate given array to the end of this array
    >r begin
         r@ :each
       while 
         eself :add
       repeat r> :uneach ;m
 :m :last ( -- n ) #elems @ 1- self :at ;m
 
 :m :search ( n -- idx true | false ) 
    eself :size 0 ?do dup i self :at =
          if drop i true unloop exit then loop drop false ;m

 :m :first ( -- n ) 0 self :at ;m
 :m :second ( -- n ) 1 self :at ;m

;class

\ HOFs

: >array ( -- obj ) heap> array ;

: :apply ( xt obj -- <varies> ) \ apply xt to each item in the array
                             \ items in array do not change
     locals| obj xt |
     obj :uneach
     begin
      obj :each
     while
      xt execute
     repeat
     ;


\ apply xt to each item in array
\ count the number of times xt returns non-zero
: :count ( xt array -- n )
  0 locals| cnt obj xt |
  obj :size 0 ?do i obj :at xt execute if cnt 1+ to cnt then
              loop cnt ;

\ apply xt2 only if xt1 returns true

: :applyIf ( xt1 xt2 obj -- <varies> ) \ apply xt2 to each item in the array
                             \ that responds true to xt1
                             \ items in array do not change
     locals| obj xt2 xt1 |
     obj :uneach
     begin
      obj :each
     while
      dup xt1 execute
      if xt2 execute
      else drop
      then
     repeat
     ;




   : :mapArray ( xt array -- ) \ apply xt to each object in the array
                             \ items in array are changed
     locals| obj xt |
     obj :size 0 ?do i obj :at xt execute i obj :to loop ;


 \ :filter returns a new array only with items that respond to a
 \ true condition defined by the xt (the array' is allocated in the heap)
 
 \ BUT, note the problem of having two copies of the same object. Use care.
 \ Only <free or <freeAll the original array, just use free on 1array'

: :filter ( xt array -- 1array' )
   0 locals| obj' obj xt |
   obj >class (heap) to obj'
   obj :uneach
   begin
    obj :each
   while
    xt execute obj' :add
   repeat obj' ;


\ for an array or array subclass filled with heap objects
\ and the array is also allocated in the heap
\ and there could be nested arrays or array subclasses to any level deep
  : <freeAll \ { obj -- }
  locals| obj |
  begin
   obj :each
  while
   dup is-a-kindof array
   if recurse else <free then
  repeat obj <free ;


