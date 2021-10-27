

\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Douglas B. Hoffman  dhoffman888@gmail.com

\ Last Revision: 27 Oct 2021  06:33:14  dbh
\ removed early binding via message-to-class, too complex, no need
\ reinstated wordlist based ?isSel (otherwise code was bugged)

[defined] >M4TH [if]
ONLY FORTH DEFINITIONS
>M4TH
traceoff debug off 
anew --fms--
[then]

\ optional unFREEd memory checker, for development
\ include mem.f

[undefined] cell [if] 1 cells constant cell [then]
[undefined] place [if] : place 2dup 2>r 1+ swap move 2r> c! ; [then]

[undefined] +order [if]
 : +order ( wid -- ) >r get-order r> swap 1+ set-order ;
[then]



\ here
decimal

\ *** BEGIN FMS2 CODE ***

true constant fmsCheck? \ use false *only* after all classes and their use are fully debugged

0 value dflt-cur
get-current to dflt-cur

create order-list 6 cells allot
: save-order get-order dup 1+ 0 do order-list i cells + ! loop ;
save-order

\ We use message-wid wordlist to record and identify all messages during class creation. 
\ But the message definition used for actual message sends will be in the dflt-cur
\ wordlist. This way we can always identify message names that may conflict with
\ other definitions.
wordlist constant message-wid  
message-wid +order \ make it the first wordlist to be searched, always

0 value ^class

: restore-order
  0 order-list @ do order-list i cells + @ -1 +loop set-order
  message-wid +order dflt-cur set-current 0 to ^class ;

0 value self
: dfa  ( cls -- addr) 1 cells + ; \ data field address
: sfa  ( cls -- addr) 2 cells + ; \ superclass field address
: wida ( cls -- addr) 3 cells + ; \ wordlisi id address
: ifa  ( cls -- addr) 4 cells + ; \ embedded object instance variables
: cna  ( cls -- addr) 5 cells + ; \ class name address
\ : dna  ( cls -- addr) 6 cells + ; \ ### is class done compiling? address
\ 7 cells constant classSize \ ###
6 cells constant classSize

0 value hptr
0 value hptrSz
: hset ( n ptr ior --) throw to hptr to hptrSz ;
: initHtbl ( n --) cells dup allocate hset  hptr hptrSz erase ;
: HtblSz ( -- #cells) hptrSz cell / ;
: rszHtbl ( n --) cells dup hptr swap resize hset ;
: ^helem ( #cells -- a) cells hptr + ;
: Stbl ( -- ^dispatch) ^class sfa @ @ ; 
: StblSz ( -- #cells) Stbl @ cell / 1+ ;
: toDtbl ( n #cells --) cells ^class @ + ! ;
: buildDtbl
  HtblSz 1 do i ^helem @ dup 0=
             if i StblSz <
                if drop i cells Stbl + @ then
             then i toDtbl 
           loop hptrSz cell - 0 toDtbl ;
           
create meta classSize allot  meta classSize erase  here 0 , meta !
  cell meta dfa !  here 0 , meta sfa !
  
: fms-set-order ( cls --) \ make all instance variables, class variables, helper defs visible
  begin  
    dup meta <>
  while
    dup wida @ +order sfa @ 
  repeat drop ;

: <super ( addr 'name' -- ) locals| addr | here dup >r to ^class 
  classSize allot ' >body dup r@ classSize move r@ sfa !
  wordlist dup set-current r@ wida ! r> fms-set-order
  StblSz initHtbl
  addr ^class cna !
\  false ^class dna ! \ ### mark class as not done compiling (for use by early-bind)
  ;

\ return the class of any object
: >class ( obj -- cls) @ cell - @ ; 

: (ivar) ( offset 'name' -- ) create immediate ,
  does> ( -- addr) @ postpone literal postpone self postpone + ;
  
: bytes ( n 'name' --) ^class dfa dup @ (ivar) +! ;

: ex-meth ( obj xt -- ) self >r swap to self execute r> to self ;

: ?isSel ( "<name>" -- table-offset t | f) 
                 \ selector-ID = table-offset
  >in @ bl word count message-wid search-wordlist
  if ( in xt ) nip >body ( addr ) @ true exit 
  then >in ! false ;


: not-understood? ( flag -- ) abort" message not understood" ;

fmsCheck? [if] 
: >xt ( table-offset ^dispatch -- xt )
  2dup @ > not-understood? + @ dup 0= not-understood? ;
[else]
: >xt ( table-offset ^dispatch -- xt ) + @ ;
[then]

: eself ( "<messageName>" -- ) \ force early bind to self 
  ?isSel if  \ followed by message name, so early bind to it
            dup hptr + @ ?dup if nip else Stbl >xt then
            compile,
         else 
           true abort" ESELF not followed by a message" 
         then ; immediate

\ =====================================================================
\ An embedded instance variable record consists of 3 cell-sized fields.
\
\   cell    field
\  Offset   Name      Description
\  ------   ----      ---------------------------------------
\    0      link      addr points to link of prior embedded-obj ivar in chain, if any
\    1      class     pointer to class of embedded-obj 
\    2      offset    offset in owning object to this embedded-obj 
\ =====================================================================

\ **** begin embedded instance variable primitives ****

: link ( addr -- ) here over @ , swap ! ;

: store-eo-data ( n cls "name" -- offset )
  align ^class ifa link  \ store link
   ( cls) , \ store class
  ^class dfa @ ( n) , ;  \ store offset to instance variable

 
: ?execute-method-eo ( addr -- ) 
    \ input stream:    ( "<message:>" -- )  early bind message send to ivar
    \     or        ( "<non-message>" -- ^obj ) just leave addr of embedded-object 
          >r
          postpone self r@ @ ( offs ) ?dup if postpone literal postpone + then
          ?isSel
          if \ early bind to following message
          ( addr )
            ( table-offset ) r@ cell+ @ @ ( ^dspatch ) >xt ( xt ) 
            postpone literal postpone ex-meth
          then r> drop ; 

: embed-make-ivar ( ^cls-eo offset "eo-name" -- )
  create immediate ( offset ) , ( ^cls-eo ) ,
  does>  ?execute-method-eo  ;

: embed-bytes ( ^cls-eo n "eo-name" --)
  >r ^class dfa dup >r @ embed-make-ivar r> r> swap ( n dfa ) +! ;

: embed-obj ( ^cls-eo "eo-name" -- )
  dup store-eo-data
  dup dfa @ ( size-of-eo ) embed-bytes ;  

\ The total memory for all embedded objects
\ will already have been allotted/allocated at this time.
\ What remains to be done is to store ^dispatch pointers.

: (setup-eos) ( obj class -- ) 
    ifa
  begin \ walk the linked-list
    @ ?dup
  while
    ( we have an eo )
    >r
	       r@ [ 2 cells ] literal + @ ( obj eo-offset )
	       over + ( obj eo )
	       r@ cell+ @ ( obj eo ^class-eo )
	       2dup @ swap ( obj eo ^class-eo ^dispatch eo ) ! \ store ^dispatch
	       ( obj eo ^class-eo ) over >r
	       recurse \ must set up eos of eos nested to any level
	       r> drop
    r>
  repeat  drop ;

: setup-eos ( obj -- )
  dup >class ( obj class ) (setup-eos)  ;

\ **** end embedded instance variable primitives ****



\ For a dispatch table selector, the selector-ID is a table offset.
\ The offset is stored in the body of the selector definition.
\ The address of the offset is subsequently retrieved by obtaining the body address 
\ of the selector's xt and performing @.

0 value table-offset

: make-selector ( 'name' --) get-current message-wid set-current
  create table-offset cell+ dup to table-offset , set-current  
  does> @ over @ >xt ex-meth ;

: get-selector ( "<messageName>" -- table-offset ) \ table-offset = selector
  ?isSel if ( table-offset ) 
         else \ <messageName> is not a selector, so make it one
           make-selector table-offset 
         then ;

: sel ( "<messageName>" -- ) get-selector drop ;

: :m ( 'name' -- #table-cells xt ) get-selector cell / :noname ;
: ;m ( #table-cells xt --) postpone ; swap
   begin
     HtblSz 1- over < 
   while
     HtblSz 1+ rszHtbl 
     0 HtblSz 1- ^helem !
   repeat ^helem ! ; immediate

: super ( 'name' --) ?isSel if Stbl >xt compile, else -1 abort" invalid selector after super" then ; immediate


0 value (dict)-xt \ will contain xt for (dict)

: ex-meth2 ( xt obj  -- ) self >r to self execute r> to self ;

: ?execute ( obj --) 
     ?isSel \ is the next word a selector?
     if ( obj table-offset ) \ if yes early bind to it
        over @ ( obj table-offset ^dispatch ) >xt ( obj xt )
        postpone literal postpone literal postpone ex-meth2
     else postpone literal   
     then
  ;

: build ( class -- )  \ Last Revision: 12 Oct 2021  10:44:54  dbh fixed
  ^class
  if embed-obj exit then \ inside a class definition, so we are building an embedded object as ivar declaration
   \ outside a class definition, so instantiate a new named dictionary object
    create immediate (dict)-xt execute drop
    does> state @ if ?execute then ;

: >lower ( C -- c )
    dup [char] A [ char Z 1+ ] literal within if
        32 or
    then ;

: to-lower ( adr len -- ) \ convert entire string to lowercase in-place
  over \ addr cnt addr
  + swap  \ cnt+addr addr
  ?do i c@ >lower i c!
  loop ;

: pre-scan ( -- in adr len) >in @ bl word count ;
: post-scan ( in adr1 cnt adr2 -- ) place >in ! ;
: do-scan pre-scan pad post-scan pad count to-lower ;

: scanForSuper ( addr --- )
  do-scan pad count s" <super" compare  \ addr $ptr flag
  if s" <super object" evaluate then ;  

 
: :class ( "name" -- addr) \ name of the new class being defined
    \ addr is passed to <super where the class name is stored at cfa
  >in @ bl word count ( n c-adr len ) here over 1+ allot dup >r place >in !  
   create immediate r>
   scanForSuper 
   does> build ;  


0 [if] \ ### how to enable message-to-class
: early-bind ( sel ^cls -- )
     dup dna @
     if
        \ class is done compiling so use completed dispatch table
        @ >xt postpone literal postpone ex-meth
     else 
        \ class is still compiling, so use heap table or super table
        drop dup ( sel sel ) hptr + @ ?dup if nip nip else Stbl >xt then
        postpone literal postpone ex-meth
     then ; 


: :class ( "name" -- addr) \ name of the new class being defined
    \ addr is passed to <super where the class name is stored at cfa
  >in @ bl word count ( n c-adr len ) here over 1+ allot dup >r place >in !  
   create immediate r>
   scanForSuper 
   does> ( ^cls) >r
   ?isSel
   if
     \ classname is followed by a message, so early bind to whatever object is on the stack
     (  sel ) r> ( sel ^cls ) early-bind 
   else
     r> build
   then ;  
 [then]

defer restore  ' restore-order is restore

\ in case of class compilation error execute:  restore 
\ or whatever your system requires

[defined] >M4TH [if]
: restoreMF >M4TH message-wid +order 0 to ^class ;
' restoreMF is restore
' restoreMF is BeforeAlert 
[then]

 : ;class ( -- ) 
  ^class , here ^class !
  hptrSz allot buildDtbl  
  hptr free throw
\  true ^class dna ! \ ### mark class as done compiling ( for early-bind )
  restore ;


:class object <super meta   
 :m :init ;m  
 :m :free ;m  
;class 

0 value ?alloc 
: make-obj ( cls f -- obj) dup to ?alloc
  if dup dfa @ allocate throw 
  else dup dfa @ align here swap allot 
  then tuck swap @ swap ! dup setup-eos dup >r :init r> ; 

: (dict) ( cls -- obj ) 0 make-obj ;
' (dict) to (dict)-xt

: (heap) ( cls -- obj ) -1 make-obj ;

\ dict> and heap> are compile-time only
: heap>   ( "spaces<classname>" -- obj )
  ' >body postpone literal postpone (heap) ; immediate
: dict>   ( "spaces<classname>" -- obj )
 ' >body postpone literal postpone (dict) ; immediate

: <free  ( heap-obj --)
  dup :free free throw ; 

: (is-a-kindOf) ( object-class target-class -- flag )
  swap
  begin
    2dup = if 2drop true exit then
    sfa @ dup ['] object >body = if 2drop false exit then
  again ;


: is-a ( obj "classname" -- flag ) 
  postpone >class ' >body postpone literal postpone =
  ; immediate

: is-a-kindOf ( obj "classname" -- flag ) 
  postpone >class ' >body postpone literal postpone (is-a-kindOf)
  ; immediate

: to-self ( obj --) to self ;

: :f ( 'name' --) get-current dflt-cur set-current 
  : postpone self postpone >r postpone to-self ; immediate

: ;f ( wid --) postpone r> postpone to-self postpone ; set-current ; immediate 

: exitf postpone r> postpone to-self postpone exit ; immediate


: .class ( obj -- ) \ prints the class name of any object
  >class cna @ count type space ;

\ *** END FMS2 CODE ***

\ here swap - cr .  .( bytes used ) \ 7454 bytes on VFX Forth for OS X IA32 Version: 4.72 (32-bit)
                                  \ 5674 bytes on SwiftForth i386-macOS 3.10.5 15-Dec-2020 (32-bit)


0 [if]

:class point 
  cell bytes x
  cell bytes y
  :m :init ( x y --) y ! x ! ;m
  :f :get ( -- x y) x @ y @ ;f
;class

30 50 point p 


p constant p2

:class rect 
  point ul
  point lr
  :m :init ( x1 y1 x2 y2 --) lr :init ul :init ;m
  :m :get2 ( -- x1 y1 x2 y2 ) ul :get lr :get ;m
;class

10 20 30 40 rect r r constant r2 


: go 90000000 0 do p :get 2drop r :get2 2drop 2drop loop ;

counter go counter - .

\ SF
late bind =  3050 w\ fmsCheck? false
early bind = 1484 w\ fmsCheck? false
:f bind   = 1306
:class rect2 <super object
  cell bytes ul
  cell bytes lr
  :m :init ( x1 y1 x2 y2 --) dict> point lr ! dict> point ul ! ;m
  :m :get ( -- x1 y1 x2 y2 ) ul @ :get lr @ :get ;m
;class

: >rect2 dict> rect2 ;
: >point dict> point ;

30 50 >point constant p2
10 20 30 40 >rect2 constant r2 


: go2 90000000 0 do p2 :get 2drop r2 :get 2drop 2drop loop ;
 
counter go2 counter - .


:class rect2 <super object
  point ul
  point lr
  :m :init ( x1 y1 x2 y2 --) lr :init ul :init ;m
  \ proof that eo not followed by a message does the right thing
  :m :get ( -- x1 y1 x2 y2 ) ul :get lr :get ul ;m
;class

1 2 3 4 rect2 r2
r2 :get .s => 1 2 3 4 254328 <-Top  ok
.class => point

[then]


0 [if]

[defined] VFXForth [if]

previous \ get rid of message-wid in search order
         \ this seems to necessary for loading the following
         \ VFX extensions 


\ quotations.fth are not required, but are nice to have
  include /Users/doughoffman/VfxOsxPro/Examples/quotations.fth
  
  \ xchar.fth is only required if you want unicode capability in json.f
  include /Users/doughoffman/VfxOsxPro/Lib/xchar.fth
		[undefined] F+ [if]
  include /Users/doughoffman/VfxOsxPro/Lib/x86/Ndp387.fth [then]

				   [then]

restore \ restore message-wid

[defined] 'SF [if]
  include /Users/doughoffman/Desktop/fpmathSF.f
  include /Users/doughoffman/SwiftForth/lib/options/quotations.f
    [then]

restore \ restore message-wid

include /Users/doughoffman/FMS2VT/ptr.f
include /Users/doughoffman/FMS2VT/utility-words.f
include /Users/doughoffman/FMS2VT/array.f
include /Users/doughoffman/FMS2VT/string.f
include /Users/doughoffman/FMS2VT/int.f
include /Users/doughoffman/FMS2VT/flt.f
include /Users/doughoffman/FMS2VT/file.f
include /Users/doughoffman/FMS2VT/farray.f
include /Users/doughoffman/FMS2VT/arrays.f 
include /Users/doughoffman/FMS2VT/objectArray.f 
include /Users/doughoffman/FMS2VT/json.f
include /Users/doughoffman/FMS2VT/hash-table.f
include /Users/doughoffman/FMS2VT/hash-table-m.f
include /Users/doughoffman/FMS2VT/btree.f

\ optional testing routines
 include /Users/doughoffman/FMS2VT/FMS2Tester.f

[then]


0 [if] \ Optional Diagnostics/Inspection code 

\ Example Use:  dc string  \ "dump-class string"

: (dd) ( ^cls -- )
  cr ." DISPATCH TABLE"
  to ^class 
  cr ." address " ." cell#  " ." XT  " 
  cr ^class @ cell - . -1 . ^class >class . ."  => ^class at cell -1"
  ^class @ @  cell /  1+ 0
  ?DO cr ^class @ i cells + . i . ^class @ i cells + @ .
   i 0= if ."  cell 0 contains the max valid table-offset" then
  LOOP cr ;

0 value addr 
: (dc) ( ^class -- )
  cr ." DUMP CLASS"
 0 to addr to ^class 
 cr ^class . 2 spaces 0 . ." ^class=" ^class . ." ^class @ => " ^class @ .  ." = ^dispatchTable"
 cr  ^class DFA dup . 2 spaces 1  . @  . ."  ^class DFA @  => obj length without indexed area"
 cr  ^class SFA dup . space 2  . @ . ."   ^class SFA @ => superclass "
 cr  ^class WIDA dup . space 3  . @ . ."   ^class WIDA @ => wordlist id "
 cr  ^class IFA dup . space 4  . @ . ."   ^class IFA @ => ^ifa "
 ;

\ "dump class"
: dc  \ usage: dc <classname>  
 ' >body
 to ^class 
 ^class (dc)
 ^class (dd)
 0 to ^class ;

 
[then]

