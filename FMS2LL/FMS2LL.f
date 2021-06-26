\ Last Revision: 25 Jun 2021  05:44:31  dbh


decimal


[undefined] cell [if] 1 cells constant cell [then]
[undefined] place [if] : place 2dup 2>r 1+ swap move 2r> c! ; [then]
[undefined] +order [if] : +order ( wid -- ) >r get-order r> swap 1+ set-order ;
[then]

\ file mem.f is only used for debugging allocated memory FREEing
\ include FMS2LL/mem.f

here

0 value dflt-cur
get-current to dflt-cur

create order-list 6 cells allot
: save-order get-order dup 1+ 0 do order-list i cells + ! loop ;
save-order

0 value self \ will contain the current object

0 value ^class \ will contain the current class being compiled

: restore-order
  0 order-list @ do order-list i cells + @ -1 +loop set-order
  dflt-cur set-current 0 to ^class ;

0 [if]  Class Structure

note that ^class is the address of cell 0

cell  contents
----  ---------------------------------------------
 0    1st n-way method linked list address
 1    2nd n-way method linked list address
 2    ...
 3
 4
 5
 6
 7    8th n-way method linked list address
 8    dfa  ( addr of total size of instance variables for this class )
 9    sfa  ( addr of superclass )
10    ifa  ( addr of last embedded-object instance variable, LL )
11    nfa ( addr of class name )
12    wida ( addr of class wordlist )

Note that for class inheritance we need only copy the above to the newly created
subclass and then update the SFA and WIDA fields. The DFA field will be updated
as new instance variables are added to the subclass. Any new methods defined
for the subclass will be appended to the n-way linked lists. The linked lists
will naturally handle method inheritance and over riding.

The structure of all objects is to contain the ^class in its first cell, followed
by the object's instance variables. Offsets to the instance variables can be obtained
by inspecting the definition of the instance variable. See the does> action of (IVAR) below.

[then]

: dfa ( cls -- a)  8 cells + ; 
: sfa ( cls -- a)  9 cells + ;
: ifa ( cls -- a) 10 cells + ;
: nfa ( cls -- a) 11 cells + ; 
: wida ( cls -- a) 12 cells + ; 
13 cells constant classSize

\ sel is a unique address that identifies the selector, or message.
\ _mfa computes which of the 8 linked lists is used for method lookup.
\ ideally _mfa should provide a uniformly distributed offset to the linked lists
: _mfa ( addr -- offset )  dup >r 2/ 2/ r@ xor \ offset will be 0 thru 7 for 8 lists
  2/ 2/ r> xor 7 and cells ;

\ method field address, mfa, returns the liked list to be used for the method search
: mfa ( sel cls -- sel mfa ) over _mfa + ;

\ fm, or find method, given the sel address as the key and the mfa as the linked list
\ to search, returns the method xt if the key is found or aborts if not found.
: fm ( sel mfa -- xt )
  begin \ standard linked list search, key = sel
    @ dup
  while
    2dup cell+ @ = \ stored keys are 1 cell offset from node
    if [ 2 cells ] literal + nip @ exit then \ payload is xt, 2 cells offset from node
  repeat -1 abort" method not found" ;

\ meta is a dummy class that class object inherits from
\ create meta classSize dup allot meta swap erase  cell meta dfa !
create meta classSize dup allot meta swap erase  cell 1+ meta dfa !

: fms-set-order ( cls --) \ make all instance variables, class variables, helper defs visible
  begin  
    dup meta <>
  while
    dup wida @ +order sfa @ 
  repeat drop ;

\ <super is used to declare the superclass, create the wordlist that is associated
\ with this class and set it as the current compilation wordlist,
\ and finally set the wordlist search order so instance variables
\ and class definitions can be found (including any level of
\ superclass definitions). 
: <super ( addr 'name' -- ) here dup >r to ^class
  classSize allot
  ' >body dup r@ classSize move r> sfa ! \ copy data from the superclass
  ( addr) ^class nfa !  \ store addr of name of class
  wordlist dup set-current ^class wida ! 
  ^class fms-set-order ;

\ is the next word in the input stream a selector?
\ if so return the selector under true
\ if not return false
: ?isSel ( 'name' -- sel t | f )
  bl word find
  if >body dup 1+ c@ 254 = if ( sel ) true exit then
  then drop false ;

: ex-meth self >r swap to self execute r> to self ;

: make-selector ( 'name' -- sel )
  get-current
  dflt-cur set-current  create
  here dup _mfa c, \ grab a new unique address, compute its associated offset into the n-way lists
              \ and store that offset. The does> action of this definition will
              \ return that unique adress (or sel). The sel address also points
              \ to the n-way linked list offset.
 ( set-current ) 254 c, swap set-current
  does> ( obj addr ) \ the action of the message is to fetch the ^class from the first
                     \ cell of the object, add the n-way offset to that,
                     \ and do a linked list search for the method xt.
                     \ Then store the old self and place the object address in self.
                     \ Lastly execute the xt and restore self.
  over @ over c@ + fm ex-meth ;

: gs ( "name" -- sel )
  >in @ \ save for possible restore
  ?isSel if ( in sel ) nip
         else \ not a selector so make it one
            >in ! make-selector  
         then ;

: sel ( "name" -- ) gs drop ;

: link ( addr -- ) here over @ , swap ! ;

\ make the n-way linked list method xt entry
: :m ( 'name' -- a xt )
   gs ^class mfa link , here 0 , :noname ;

: ;m ( a xt -- )
  postpone ; swap ! ; immediate

: super ( 'name' -- ) ' >body ^class sfa @ mfa fm compile, ; immediate
: eself ( 'name' --) ' >body ^class mfa fm compile, ; immediate

\ the action of an instance variable is to return its address
\ which is the address of the object, self, plus the offset
: (ivar) ( offset 'name' -- ) create immediate ,
  does> ( -- addr ) @ postpone literal postpone self postpone + ;

: bytes ( n 'name' -- ) ^class dfa dup @ (ivar) +! ;

: embed-make-ivar ( ^cls-eo offset "eo-name" -- ) create immediate ( offset ) , ( ^cls-eo) ,
  does>  >r postpone self r@ @ ( offs ) ?dup if postpone literal postpone + then  \ does> will leave the eo on the stack at runtime
  >in @ ?isSel if nip ( sel) r> cell+ @ ( sel ^cls-eo ) mfa fm ( xt ) postpone literal postpone ex-meth
          else >in ! r> drop
          then ;

: embed-bytes ( offset ^cls-eo size-of-eo "eo-name" --)
  >r
  swap embed-make-ivar
  r> ^class dfa +! ;

: embed-obj ( ^cls-eo "eo-name" -- ) >r align ^class ifa link
 r@ , ^class dfa @ ( offset ) dup , r@ r> dfa @ ( offset ^cls-eo size-of-eo ) embed-bytes ;

: (setup-eos) \ {: f obj class -- :} \ store ^cls in first cell of each eo
   locals| class obj f |
   obj class
    ifa
  begin \ walk the linked-list
    @ ?dup
  while
    ( we have an eo )
    dup >r
	       2 cells + @ ( obj eo-offset )
	       over + ( obj eo )
	       r@ cell+ @ ( obj eo ^class-eo )
	       2dup swap ( obj eo ^class-eo ^class-eo eo  ) ! \ store ^class
	       ( obj eo ^class-eo) over ( obj eo ^class-eo eo ) f swap cell+ c!
	       ( obj eo ^class-eo ) over >r
	       f -rot
	       recurse \ must set up eos of eos nested to any level
	       r> drop
    r>
  repeat drop ;
: setup-eos ( f obj -- )
  dup @ ( f obj class ) (setup-eos)  ;


0 value (dict)-xt \ will contain xt for (dict)

s" gforth" environment? 
0= [if] \ can't get early binding to dict obj to work on gforth 0.7.3

: ?execute ( obj --) 
     >in @ ?isSel
     if nip ( obj sel )
        over @ ( obj sel ^class ) mfa fm swap ( obj xt )
        postpone literal postpone literal postpone ex-meth
     else >in !
     then
  ;

: build ( class -- )
  ^class
  if embed-obj \ inside a class definition, so we are building an embedded object as ivar declaration
  else \ outside a class definition, so instantiate a new named dictionary object
    create immediate (dict)-xt execute drop
    does> state @ if ?execute then
  then ; 

[else]

: build ( class -- )
  ^class
  if embed-obj \ inside a class definition, so we are building an embedded object as ivar declaration
  else \ outside a class definition, so instantiate a new named dictionary object
    create (dict)-xt execute drop
  then ; 

[then]


: :class ( "name" -- addr) \ addr is passed to <super where the class name is stored at nfa
  >in @ bl word count ( n c-adr len ) here over 1+ allot dup >r place >in !  
   create immediate r> does> build ;

defer restore  ' restore-order is restore

: ;class restore ;

: .class ( obj --) @ nfa @ count type space ;
 

:class object <super meta
  :m :init ;m
  :m :free ;m
;class

: (pre) ( cls f -- f cls n) swap dup dfa @ ;  
: (post) ( ... f cls a -- obj) dup >r ( f cls a) ! r@ ( f a ) 2dup ( f a f a) cell+ c! ( f a) setup-eos 
   r@ ( a) :init r> ( a) ;

: make-obj ( cls f -- obj) 
  if -1 (pre) allocate throw  
  else 0 (pre) align here swap allot  
  then (post) ;

: (dict) ( cls -- obj ) 0 make-obj ;  ' (dict) to (dict)-xt
: (heap) ( cls -- obj ) -1 make-obj ;

\ dict> and heap> are compile-time only
: heap>   ( "spaces<classname>" -- obj )
  ' >body postpone literal postpone (heap) ; immediate
: dict>   ( "spaces<classname>" -- obj )
 ' >body postpone literal postpone (dict) ; immediate
: <free  ( heap-obj --) dup :free free throw ;

: alloc? ( obj -- f) cell+ c@ ; 

\ is-a is compile-ony
: is-a ( obj "classname" -- flag ) 
  postpone @ ' >body postpone literal postpone = ; immediate

: (is-a-kindOf) ( object-class target-class -- flag )
  swap
  begin
    2dup = if 2drop true exit then
    sfa @ dup ['] object >body = if 2drop false exit then
  again ;

\ is-a-kindOf is compile-ony
: is-a-kindOf ( obj "classname" -- flag ) 
  postpone @ ' >body postpone literal postpone (is-a-kindOf)
  ; immediate

cr here swap - . .( bytes)  \ 4645  SF 32-bit

[defined] >M4TH [if]
: restore-MF ONLY FORTH DEFINITIONS >M4TH 0 to ^class ;
' restore-MF is restore
[then]


0 [if] \ test code

28 value x

:class point <super object
  cell bytes x
  cell bytes y
  :m :init ( x y --) y ! x ! ;m
  :m :get ( -- x y) x @ y @ ;m
;class

10 20 point p \ messages to p will be early-bound

:class rect <super object
  point ul \ messages to ul and lr will be early-bound
  point lr
  :m :init ( x1 y1 x2 y2 --) lr :init ul :init ;m
  :m :get ( -- x1 y1 x2 y2 ) ul :get lr :get ;m
;class

10 20 30 40 rect r \ messages to r will be early-bound

:class rect <super object
  cell bytes ul \ messages to ul @ and lr @ will be late-bound
  cell bytes lr
  :m :init ( x1 y1 x2 y2 --) dict> point lr !  dict> point ul ! ;m
  :m :get ( -- x1 y1 x2 y2 ) ul @ :get lr @ :get ;m
;class

: make-point dict> point ;
: make-rect dict> rect ;
30 50 make-point constant p \ messages to p and r will be late-bound
10 20 30 40 make-rect constant r 

: go 90000000 0 do p :get 2drop r :get 2drop 2drop loop ;
 
\ SF
counter go counter - .  \ 1472 early binding to dict and embedded objects
counter go counter - .  \ 3736 late binding to dict objects, early binding to embedded objects
counter go counter - .  \ 5221 late binding to dict and embedded objects

[then]

-1 [if]

[defined] VFXForth [if]

  include /Users/doughoffman/VfxOsxPro/Examples/quotations.fth
  include /Users/doughoffman/VfxOsxPro/Lib/xchar.fth
		[undefined] F+ [if]
  include /Users/doughoffman/VfxOsxPro/Lib/x86/Ndp387.fth [then]

				   [then]
[defined] 'SF [if]
  include /Users/doughoffman/Desktop/fpmathSF.f
    [then]

include FMS2LL/ptr.f
include FMS2LL/utility-words.f
include FMS2LL/array.f
include FMS2LL/string.f
include FMS2LL/int.f
include FMS2LL/flt.f
include FMS2LL/file.f
include FMS2LL/farray.f
include FMS2LL/arrays.f 
include FMS2LL/objectArray.f 
include FMS2LL/json.f
include FMS2LL/hash-table.f
include FMS2LL/hash-table-m.f
include FMS2LL/btree.f

\ optional testing routines
\ include FMS2LL/FMS2Tester.f

[then]
