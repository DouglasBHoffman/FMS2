\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Feb 23 2021 Douglas B. Hoffman
\ simplified ?isSel
\   made is-a state smart, added is-a-kindOf, added .class
\ added JSON support to the library
\ dhoffman888@gmail.com

[defined] >M4TH [if]
ONLY FORTH DEFINITIONS
>M4TH
\ traceon debug off
anew --fms--
[then]

\ optional unFREEd memory checker, for development
\ include /Users/doughoffman/Desktop/FMS2a/mem.f

[undefined] cell [if] 1 cells constant cell [then]
[undefined] +order [if] : +order ( wid -- ) >r get-order r> swap 1+ set-order ; [then]

here
decimal

\ *** BEGIN FMS2 CODE ***

0 constant fmsCheck? \ use false *only* after all classes and their use are fully debugged

0 value dflt-cur
0 value self
0 value ^class
: dfa  ( cls -- addr) 1 cells + ; \ data field address
: sfa  ( cls -- addr) 2 cells + ; \ superclass field address
: wida ( cls -- addr) 3 cells + ; \ wordlisi id address
: ifa  ( cls -- addr) 4 cells + ; \ embedded object instance variables
fmsCheck? [if]
: cna  ( cls -- addr) 5 cells + ; \ class name address
55 cells constant classSize \ maximum classname of 49 chars
[else] 5 cells constant classSize
[then]
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

: <super ( 'name' -- wid1 wid2 ...) here dup >r to ^class 
  classSize allot ' >body dup r@ classSize move r@ sfa !
  wordlist dup set-current r@ wida ! get-order r> fms-set-order
  StblSz initHtbl ;

\ return the class of any object
: >class ( obj -- cls) @ cell - @ ; 

: (ivar) ( offset 'name' -- ) create immediate ,
  does> ( -- addr) @ postpone literal postpone self postpone + ;
  
: bytes ( n 'name' --) ^class dfa dup @ (ivar) +! ;

\ We use message-wid wordlist to record and identify all messages during class creation. 
\ But the message definition used for actual message sends will be in the dflt-cur
\ wordlist. This way we can always identify message names that may conflict with
\ other definitions.
wordlist constant message-wid  
message-wid +order \ make it the first wordlist to be searched, always

: ex-meth ( obj xt -- ) self >r swap to self execute r> to self ;

\ : ?isSel ( "<name>" -- table-offset t | f) 
                 \ selector-ID = table-offset
\  >in @ bl word count message-wid search-wordlist
\  if ( in xt ) drop >in ! bl word find drop >body ( addr ) @ true exit 
\  then >in ! false ;

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
          ?issel
          if \ early bind to following message
          ( addr )
            ( table-offset ) r@ cell+ @ @ ( ^dspatch ) >xt ( xt )
            postpone literal postpone ex-meth
          then r> drop ; 

: embed-make-ivar ( ^cls-eo offset "eo-name" -- )
  create immediate ( n ) , ( ^cls-eo ) ,
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

: :m ( 'name' -- #table-cells xt ) get-selector cell / :noname ;
: ;m ( #table-cells xt --) postpone ; swap
   begin
     HtblSz 1- over < 
   while
     HtblSz 1+ rszHtbl 
     0 HtblSz 1- ^helem !
   repeat ^helem ! ; immediate

: super ( 'name' --) ?isSel if Stbl >xt compile, else -1 abort" invalid selector" then ; immediate


0 value (dict)-xt \ will contain xt for (dict)

\ : ex-meth ( obj xt -- ) self >r swap to self execute r> to self ;
\ : >xt ( table-offset ^dispatch -- xt ) + @ ;

: ?execute-method 
  state @
  if
    ?isSel
    if
    \ early bind to following message
    ( addr sel-type )
      ( obj table-offset ) over @ rot postpone literal ( obj table-offset ^dspatch ) >xt 
      postpone literal postpone ex-meth
    else \ no message so just compile addr of object
      postpone literal
    then
  then ; 


: (obj) \ Compile time ( "spaces<name>" -- ) \ name of the new dictionary object
   create  immediate
   \ Run time: ( -- ^obj )
   \   or execute: ^obj <message:>
   does> ?execute-method
   ; 

: build ( class -- )
  ^class
  if embed-obj \ inside a class definition, so we are building an embedded object as ivar declaration
  else \ outside a class definition, so instantiate a new named dictionary object
    create (dict)-xt execute drop
  then ;

: >lower ( char -- char') 32 or ; \ return lower-case character of c

: to-lower ( addr cnt -- ) over + swap ?do i c@ >lower i c! loop ;

: move$ ( src$ptr\dest$ptr --) \ copy src to dest, dest must be long enough
  over c@ 1+ move ;

: do-scan ( $ptr -- $ptr ) \ always converts to upper case
  dup >in @ bl word rot move$ >in ! 
  dup count to-lower ;

: scanForSuper
  pad do-scan count s" <super" compare  \ $ptr flag
  if s" <super object" evaluate then ;  

fmsCheck? [if]
create temp-className 50 allot
: scanForClassname ( "name" -- )
  pad dup >in @ bl word rot move$ >in ! 
  pad c@ 50 min pad c! \ assure we don't overflow the destination
  temp-className move$ ;

: :class ( "name" -- ) \ name of the new class being defined
   scanForClassname
   get-current to dflt-cur
   create immediate
   scanForSuper
   does> build ;  

: ;class ( wid1 wid2 ... -- ) set-order dflt-cur set-current
  ^class , here ^class !
  hptrSz allot buildDtbl  
  hptr free throw
  temp-className ^class cna move$
  0 to ^class ;
  
[else]

: :class ( "name" -- ) \ name of the new class being defined
   get-current to dflt-cur
   create immediate
   scanForSuper
   does> build ;  

: ;class ( wid1 wid2 ... -- ) set-order dflt-cur set-current
  ^class , here ^class !
  hptrSz allot buildDtbl  
  hptr free throw
  0 to ^class ;

[then]


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

fmsCheck? [if] \ is-a and is-a-kindOf are state-smart only during development
: is-a ( obj "classname" -- flag ) 
  state @
  if   postpone >class ' >body postpone literal postpone =
  else >class ' >body =
  then ; immediate

: is-a-kindOf ( obj "classname" -- flag ) 
  state @
  if   postpone >class ' >body postpone literal postpone (is-a-kindOf)
  else >class ' >body (is-a-kindOf)
  then ; immediate

[else]

: is-a ( obj "classname" -- flag ) 
  postpone >class ' >body postpone literal postpone =
  ; immediate

: is-a-kindOf ( obj "classname" -- flag ) 
  postpone >class ' >body postpone literal postpone (is-a-kindOf)
  ; immediate

[then]

: to-self ( obj --) to self ;

: :f ( 'name' --) get-current dflt-cur set-current 
  : postpone self postpone >r postpone to-self ; immediate

: ;f ( wid --) postpone r> postpone to-self postpone ; set-current ; immediate 

: exitf postpone r> postpone to-self postpone exit ; immediate

: restore only forth message-wid +order dflt-cur set-current 0 to ^class ;

fmsCheck? [if] \ debugging tool
: .class ( obj -- ) \ prints the class name of any object
  >class cna count type space ;
[then]

\ *** END FMS2 CODE ***

here swap - cr .  .( bytes used ) \ 7426 bytes on VFX Forth for OS X IA32 Version: 4.72 (32-bit)
                                  \ 5693 bytes on SwiftForth i386-macOS 3.10.5 15-Dec-2020 (32-bit)


\ in case of class compilation error execute:  restore 
\ or whatever your system requires


[defined] >M4TH [if]
: restore >M4TH message-wid +order 0 to ^class ;
' restore is BeforeAlert 
[then]

0 [if]

:class foo 
  cell bytes data
  :m :init ( o --) 66 data ! ;m
  :m :get ( o -- n) data @ ;m
;class 

foo  x    
 
x :get . 66 ok

: go :get ;  ok
see go 
GO 
( 00088940    8B13 )                  MOV       EDX, 0 [EBX]
( 00088942    0315C0880800 )          ADD       EDX, [000888C0]
( 00088948    FF3554940600 )          PUSH      [00069454]
( 0008894E    8B12 )                  MOV       EDX, 0 [EDX]
( 00088950    891D54940600 )          MOV       [00069454], EBX
( 00088956    8BCA )                  MOV       ECX, EDX
( 00088958    8B5D00 )                MOV       EBX, [EBP]
( 0008895B    8D6D04 )                LEA       EBP, [EBP+04]
( 0008895E    FFD1 )                  CALL      ECX
( 00088960    5A )                    POP       EDX
( 00088961    891554940600 )          MOV       [00069454], EDX
( 00088967    C3 )                    NEXT,
( 40 bytes, 12 instructions )

[then]






\ stopincluding
-1 [if] \ Recommended class library file includes.
        \ Actually, none of these files are required to use FMS.
[defined] VFXForth [if]
include /Users/doughoffman/VfxOsxPro/Examples/quotations.fth
include /Users/doughoffman/VfxOsxPro/Lib/xchar.fth
[then]
		[undefined] F+ [defined] VFXForth and [if]
  include /Users/doughoffman/VfxOsxPro/Lib/x86/Ndp387.fth [then]
				   [then]
[defined] 'SF [if]
   include /Users/doughoffman/Desktop/fpmathSF.f
   
    [then]
    
here
include /Users/doughoffman/Desktop/FMS2a/ptr.f 

here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/utility-words.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/array.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/string.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/int.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/flt.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/file.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/farray.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/arrays.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/objectArray.f
here swap - cr .  .( bytes used )

[defined] 'SF [if]
include /Users/doughoffman/Desktop/FMS2a/jsonSF.f
[then]

[defined] VFXForth [if]
here
include /Users/doughoffman/Desktop/FMS2a/json.f
here swap - cr .  .( bytes used )
[then]


here
include /Users/doughoffman/Desktop/FMS2a/hash-table.f
here swap - cr .  .( bytes used )

here
include /Users/doughoffman/Desktop/FMS2a/hash-table-m.f
here swap - cr .  .( bytes used )

\ include /Users/doughoffman/Desktop/FMS2a/FMS2Tester.f  \ not fully comprehensive yet

[then]  


0 [if] \ Optional Diagnostics/Inspection code 

\ Example Use:  dc string  \ "dump class string"

: (dd) ( ^cls -- )
  ." DISPATCH TABLE"
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

