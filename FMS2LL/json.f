[undefined] >string [if] cr .( file string.f required ) abort [then]
\ Feb 8, 2021 dbh  https://github.com/DouglasBHoffman/FMS2
\ changed names of instance variables DATA and KEY

\ eliminated need for 2nd extra stack
\   tweaked a few details
\   added support for unicode
\ jul 3, 2021  custom :insert for json ( subclass of array )
\ jul 15, 2021 removed some locals

[undefined] >int [if] cr .( file int.f required ) abort [then]
[undefined] >flt [if] cr .( file flt.f required ) abort [then]
[undefined] >l [if] cr .( file stack.f required ) abort [then]
\ [undefined] xc@+ [if] cr .( xchar wordset is required )  abort [then]

\ This parser is based on the ECMA standard as described here:
\     https://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf

\ It is a lookup table based json parser. 
\ Each ASCII character of the JSON text is an index into the 128 cell
\ table. Each cell contains an XT appropriate for that ASCII character.
\ Unicode characters are still handled.
\ So the algorithm simply steps through each character and executes
\ the XT for that character. One-pass. No backing up or looking ahead.
\ A stack is used to push and pop json objects as they are
\ created and consumed. This is the l stack.
\ This is a state-based one-pass parser. The state is maintained
\ using one extra stack and three global variables:
\ str? (are we parsing a string?), num?(are we parsing a number?)
\ and esc?(are we parsing an escaped character?).

\ Note that no effort is made to detect invalid JSON formatting.
\ Invalid formatting will likely result in a crash.
\ moved l-stack to file stack.f \ jul 2021

decimal

:class json-string <super string

 :m :. '"' emit super :. '"' emit ;m

[defined] xc@+
[if]
 : processUNI \ {: str | addr len -- :}
   0 0 locals| addr len str |
   super :@ drop ( addr)
   current-idx @ 1- + dup to addr 4 x-size to len
   addr xc@+ nip ( xchar ) len 1- current-idx +!
   '\' str :ch+  'u' str :ch+
   hex s>d <# # # # # #> decimal str :add ;
[else]
  : processUNI drop ;
[then]

 :m :write \ {: str -- :}
    locals| str |
    '"' str :ch+
      begin
       super :each
      while
            dup 127 >
            if drop str processUNI
		    else   dup case
		             '"' of '\' str :ch+ endof 
		             '\' of '\' str :ch+ endof
		               8 of '\' str :ch+ drop 'b' endof \ backspace
		              12 of '\' str :ch+ drop 'f' endof \ form feed
		            ( all others dropped) endcase str :ch+
	        then
      repeat '"' str :ch+ ;m

;class
: >json-string heap> json-string ;

0 [if]

j{ { "qz\u20ACBz": 10 } }j  value j
j :.
{
"qz€Bz": 10
}  

j{ { "qz\u20ACBz": 10 } }j  value j  ok
j json>$  ok-1 
dup :. {\"qz\\u20ACBz\":10} ok-1 
s\" {\"qz\\u20ACBz\":10}" $>json
dup :. 
{
"qz€Bz": 10
} ok-1 



[then]





:class json <super array

 :m :insert ( n idx -- ) \ increase size of array by one, place n at given index position
                         \ after having moved all ensuing elements up by one position.
    >r
    #elems @ 1+ (resize)
    r@ eself :size 1- ?do i 1- eself :at i eself :to -1 +loop
    ( n) r> eself :to 
   ;m


  :m :. cr '{' emit
      self :size 0 >
      if
        self :size 1- 0 ?do cr i self :at :. ',' emit space loop 
        cr self :last :. cr 
      then '}' emit ;m
  :m :free
      super :size 0 >
      if super :size 0 ?do i super :at <free loop then  
      super :free ;m \ will free class ptr
  :m :write \ {: str -- :}
     locals| str |
     '{' str :ch+
     super :size 0 >
     if
       super :size 1- 0 ?do   str i super :at ( pair )  :write 
                            ',' str :ch+  loop
                              str super :last ( pair ) :write
     then '}' str :ch+ ;m
   :m :search \ {: adr len -- val t | f :}
      locals| len adr |
      super :uneach
      begin
        super :each
      while
        ( pair-obj) :@ ( val-obj key-obj ) adr len rot :=ci
        if ( val-obj ) dup :. true exit
        else drop
        then
      repeat false ;m
;class
: >json heap> json ;

:class json-array <super array
  :m :. '[' emit 
        super :size 0 >
        if space super :size 1- 0 ?do i super :at :. ',' emit space loop 
           super :last :. 
        then ']' emit ;m
  :m :free
      super :size 0 >
      if super :size 0 ?do i super :at <free loop then  
      super :free ;m \ will free class ptr
  :m :write \ {: str -- :}
      locals| str |
     '[' str :ch+
     super :size 0 >
     if
       super :size 1- 0 ?do  str i super :at ( obj )  :write 
                            ',' str :ch+ loop
                             str super :last ( pair ) :write
     then ']' str :ch+ ;m
;class
: >json-array heap> json-array ;


:class bool 
 1 bytes bdata
 :m :init ( b -- ) bdata c! ;m
 :m :! ( b --) bdata c! ;m
 :m :@ ( -- b ) bdata c@ ;m
 : get ( -- adr len ) bdata c@ if s" true" else s" false" then ;
 :m :. get type ;m
 :m :write \ {: str -- :}
     \ locals| str |
     >r
     get r> :add ;m
;class
: >bool ( b -- bool-obj) heap> bool ;

:class null 
  :m :. ." null" ;m
  :m :write \ {: str -- :}
      \ locals| str |
      >r
      s" null" r> :add ;m
;class
: >null ( -- null-obj) heap> null ;

:class pair 
  cell bytes pkey
  cell bytes val
  :m :init ( str-obj --) pkey ! s" <empty-val>" >json-string val ! ;m
  :m :! ( val-obj -- pair-obj )
      val @ <free \ first free the place-holder object
      val ! self ;m
  :m :@ ( -- val-obj str-obj) \ val pkey
     val @ pkey @ ;m
  :m :free val @ <free pkey @ <free ;m
  :m :. pkey @ :.  ':' emit space val @ :. ;m 
  :m :write \ {: str -- :}
     \ locals| str |
     dup >r
     ( str) pkey @ :write
     ':' r@ :ch+ 
     r> val @ :write ;m
;class
: >pair ( str-obj -- pair-obj) heap> pair ;

\ *** begin json parsing state definitions

0 value str? \ true if we are parsing a string
0 value num? \ true if we are parsing a number ( integer or float )
0 value esc? \ true if we are parsing an escape sequence in a string

\ *** end json parsing state definitions

: setup
   false to str?
   false to num?
   false to esc?
   l-clr ;

128 array jump-table \ a table of xts

: fill-jump-table \ {: xt -- :}
  locals| xt |
  128 0 do xt jump-table :add loop ;

: c+ ( c --) l@ :ch+ ; \ add the char to the string on the l-stack
' c+ fill-jump-table  \ the default XT, exceptions are defined below

: jt ( c xt -- ) swap jump-table :to ;
: >jt ( xt c -- xt ) over jt ;

'\' :noname ( c --) \ solidus
    esc? if ( '\' ) c+ false 
         else drop true 
         then to esc? ; jt

'/' :noname ( c --) \ reverse solidus
    esc? if false to esc? then c+ ; jt

'b' :noname ( c --) \ possible escaped backspace
    esc? if drop 8 false to esc? then c+ ; jt

'r' :noname ( c --) \ possible escaped cr
    esc? if drop 13 false to esc? then c+ ; jt

'{' :noname ( c --) 
    str? if c+ exit else drop then
    >json >l ; jt
    
' drop 
10 >jt  \ line feed
13 >jt drop  \ carriage return

:noname ( c --) str? if c+ else drop then ;
9  >jt \ tab
32 >jt drop \ space
'"' :noname ( c --) 
     esc? if c+ false to esc? exit then 
     str? if false to str? 
          else true to str? 0 0 >json-string >l
          then ( c ) drop ; jt
          
':' :noname ( c --)
    str? if c+ exit then drop
    l> >pair >l ; jt

'[' :noname ( c --) 
    str? if c+ exit then drop
     >json-array >l ; jt

:class json-flt <super flt
  cell bytes precision
  :m :init ( n -- ) ( R: r -- ) super :init  precision ! ;m
  :m :. precision @ set-precision super :. ;m
;class
: >json-flt ( n -- ) ( R: r -- ) heap> json-flt ;


: (,) \ 0 {: j-str :}
      0 locals| j-str |
     num? if l> dup to j-str :@ 2dup >integer
	             				   if nip nip >int j-str <free
	                               else ( adr len ) tuck >float if >json-flt j-str <free
	                                           else abort" invalid number string"
	                                           then
	                               then l@ is-a pair if l> :! then l@ :add false to num?
           else l> l@ is-a pair if l> ( val-obj pair-obj) :! ( pair-obj) l@ :add
             					else l@ :add
             					then
           then 
;

\ , marks the end of a key:value pair if doing a { ... } array
\   or the end of an element if doing a [ ... ] array
\ note that the last element must NOT be followed by a comma (!!)

: do-, ( c --)
    str? if c+ exit then drop
	lsize 2 < if exit then \ do nothing if } or ] has already handled it 
	l@ is-a json-array 0= if false to str? then (,) ; 

',' ' do-, jt

'}' :noname ( c --) str? if c+ exit then drop false to str? (,) ; jt
']' :noname ( c --) str? if c+ exit then do-,                   ; jt

:noname ( c --) \ process possible number character
  str? 0= if 
            num? 0= if 
                     true to num? 0 0 >json-string >l 
                    then
          then c+ ;

'+' >jt
'-' >jt
'.' >jt
'0' >jt
'1' >jt
'2' >jt
'3' >jt
'4' >jt
'5' >jt
'6' >jt
'7' >jt
'8' >jt
'9' >jt
'e' >jt
'E' >jt drop

variable adr

create xc 4 allot

[defined] xc!+ [if]
: processUnicode   \ 0 0 >string {: uni -- :}
  0 0 >string locals| uni |
  4 0 do 1 adr +!  adr @ c@  uni :ch+  loop
  hex uni :@ evaluate decimal dup >r xc xc!+ drop xc r> xc-size ( adr len )
  l@ :add   uni <free ;
[else]
: processUnicode -1 abort" cannot process unicode" ;
[then]
:noname ( c --) str? if esc? if case
   								  'u' of processUnicode false to esc? exit endof
 								  'n' of 10  endof \ line feed
 								  't' of  9  endof \ tab
 								  'f' of 12  endof \ form feed
 								0 endcase false to esc?
							 then c+
       			   else case
       			          'n' of >null >l 3 endof
       			          't' of true >bool >l 3 endof
       			          'f' of false >bool >l 4 endof
       			         0 endcase ( n ) adr +! \ skip over n next chars
       			   then ;

'u' >jt
'n' >jt
't' >jt
'f' >jt drop

0 [if] \ using VFX with xchar.f loaded

j{ { "qz\u20ACBz": 10 } }j value j
:. 
{
"qz€Bz": 10
} 

[then]

0 value max-adr

[defined] x-size
[if]
: processUni 
  adr @ dup 4 x-size >r
  dup r@ l@ :add
      r> + adr ! ;
[else]
: processUni -1 abort" cannot process unicode" ;
[then]

: $>json ( adr len -- json-obj )
  setup
  ( adr cnt ) >r adr ! adr @ r> + to max-adr
  begin
   adr @ c@ dup 127 >
   if drop processUni
   else dup jump-table :at execute
        1 adr +!
   then
   adr @ max-adr <
  while
  repeat l> 
  lsize if l> :! then ;


: refilling-parse ( -- c-addr u )
	begin
	   10 parse dup 0= 
	while
	  2drop refill 0= -39 and throw
	repeat ;

: j{ ( "<input stream>" -- json-obj )
\  0 0 >string 0 0 >string {: s s1 :}
  0 0 >string 0 0 >string locals| s s1 |
  begin
    refilling-parse 2dup s1 :! s" }j" s1 :searchCI 0=
  while
    s :add
  repeat 2drop
  s1 :delete
  0 s1 :start ! s1 :@sub s :add 
  s :@ $>json   
  s1 :delete 
  s1 :@ evaluate   s1 <free s <free
  ; 


: json>$ \ {: json -- str-obj :} 
  \ locals| json |
  >r
  0 0 >string dup
  ( str str ) r> :write 
\  json <free  \ must free the json manually when desired
  ( str ) ;


0 [if]

j{ {
  "firstName": "John",
  "lastName": "Smith",
  "isAlive": true,
  "age": 27,
  "address": {
    "streetAddress": "21 2nd Street",
    "city": "New York",
    "state": "NY",
    "postalCode": "10021-3100"
  },
  "phoneNumbers": [
    {
      "type": "home",
      "number": "212 555-1234"
    },
    {
      "type": "office",
      "number": "646 555-4567"
    }
  ],
  "children": [],
  "spouse": null
} }j value j

 
j :.  
{
"firstName": "John", 
"lastName": "Smith", 
"isAlive": true, 
"age": 27, 
"address": 
{
"streetAddress": "21 2nd Street", 
"city": "New York", 
"state": "NY", 
"postalCode": "10021-3100"
}, 
"phoneNumbers": [ 
{
"type": "home", 
"number": "212 555-1234"
}, 
{
"type": "office", 
"number": "646 555-4567"
}], 
"children": [], 
"spouse": null
} ok

s" lastname" j :search .s \ => "Smith"( 2 ) \ 11714160 \ -1 ok  

s" Venkman" 11714160 :! ok ok \ 2 

j :.  
{
"firstName": "John", 
"lastName": "Venkman", 
"isAlive": true, 
"age": 27, 
"address": 
{
"streetAddress": "21 2nd Street", 
"city": "New York", 
"state": "NY", 
"postalCode": "10021-3100"
}, 
"phoneNumbers": [ 
{
"type": "home", 
"number": "212 555-1234"
}, 
{
"type": "office", 
"number": "646 555-4567"
}], 
"children": [], 
"spouse": null
} ok  


[then]

