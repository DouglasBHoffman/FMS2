[undefined] >string [if] cr .( file string.f required ) abort [then]
\ January20, 2021 dbh  https://github.com/DouglasBHoffman/FMS2
\   added support for unicode

[undefined] >int [if] cr .( file int.f required ) abort [then]
[undefined] >flt [if] cr .( file flt.f required ) abort [then]
[undefined] xc@+ [if] cr .( xchar wordset is required )  abort [then]

\ This parser is based on the ECMA standard as described here:
\     https://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf

\ It is a table based json parser. 
\ Each ASCII character of the JSON text is an index into the 128 cell
\ table. Each cell contains an XT appropriate for that ASCII character.
\ Unicode chacaters are handled seperately.
\ So the algorithm simply steps through each character and executes
\ the XT for that character. One-pass. No backing up or looking ahead.
\ A stack is used to push and pop json objects as they are
\ created and consumed. This is the l stack.
\ This is a state-based one-pass parser. The state is maintained
\ using 2 extra stacks and three global variables:
\ str? (are we parsing a string?), num?(are we parsing a number?)
\ and esc?(are we parsing an escaped character?).

\ Note that no effort is made to detect invalid JSON formatting.

decimal

:class json-string <super string

 :m :. '"' emit super :. '"' emit ;m



 : processUNI {: str | addr len -- :}
   super :@ drop ( addr)
   current-idx @ 1- + dup to addr 4 x-size to len
   addr xc@+ nip ( xchar ) len 1- current-idx +!
   '\' str :ch+ '\' str :ch+ 'u' str :ch+
   hex s>d <# # # # # #> decimal str :add ;

   
   
 :m :write {: str -- :}
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
"qz�Bz": 10
}  

j{ { "qz\u20ACBz": 10 } }j  value j  ok
j json>$  ok-1 
dup :. {\"qz\\u20ACBz\":10} ok-1 
s\" {\"qz\\u20ACBz\":10}" $>json
dup :. 
{
"qz�Bz": 10
} ok-1 



[then]





:class json <super array
  :m :. cr '{' emit
      super :size 0 >
      if
        super :size 1- 0 ?do cr i super :at :. ',' emit space loop 
        cr super :last :. cr 
      then '}' emit ;m
  :m :free
      super :size 0 >
      if super :size 0 ?do i super :at <free loop then  
      super :free ;m \ will free class ptr
  :m :write {: str -- :}
     '{' str :ch+
     super :size 0 >
     if
       super :size 1- 0 ?do   str i super :at ( pair )  :write 
                            ',' str :ch+  loop
                              str super :last ( pair ) :write
     then '}' str :ch+ ;m
   :m :search {: adr len -- val t | f :}
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
  :m :write {: str -- :}
     '[' str :ch+
     super :size 0 >
     if
       super :size 1- 0 ?do  str i super :at ( obj )  :write 
                            ',' str :ch+ loop
                             str super :last ( pair ) :write
     then ']' str :ch+ ;m
;class
: >json-array heap> json-array ;

\ The astack holds the current state of array parsing.
\ We are either parsing inside { ... } or [ ... ]
20 array a
: >a ( n -- ) \ push item on stack
  a :add ;
: a> ( -- n ) \ pop item from stack, last in first out
  a :size 1- a :remove ;
: .a a :. ;
: a@ ( -- n ) a :last ; \ copy top stack item to data stack
: a-clr a :clear ; \ resets stack to zero items

\ 2 array types for a stack in json parser
0 constant t{
1 constant t[


:class bool
 1 bytes data
 :m :init ( b -- ) data c! ;m
 :m :! ( b --) data c! ;m
 :m :@ ( -- b ) data c@ ;m
 : get ( -- adr len ) data c@ if s" true" else s" false" then ;
 :m :. get type ;m
 :m :write {: str -- :}
     get str :add ;m
;class
: >bool ( b -- bool-obj) heap> bool ;

:class null
  :m :. ." null" ;m
  :m :write {: str -- :}
      s" null" str :add ;m
;class
: >null ( -- null-obj) heap> null ;

:class pair
  cell bytes key
  cell bytes val
  :m :init ( str-obj --) key ! s" <empty-val>" >json-string val ! ;m
  :m :! ( val-obj -- pair-obj )
      val @ <free \ first free the place-holder object
      val ! self ;m
  :m :@ ( -- val-obj str-obj) \ val key
     val @ key @ ;m
  :m :free val @ <free key @ <free ;m
  :m :. key @ :.  ':' emit space val @ :. ;m 
  :m :write {: str -- :}
     str key @ :write
     ':' str :ch+ 
     str val @ :write ;m
;class
: >pair ( str-obj -- pair-obj) heap> pair ;


[undefined] >l [if]
\ the l stack retains objects as they are created and
\ consumed by new objects needing them
20 array l
: >l ( n -- ) \ push item on stack
  l :add ;
: l> ( -- n ) \ pop item from stack, last in first out
  l :size 1- l :remove ;
: .l l :. ;
: l@ ( -- n ) l :last ; \ copy top stack item to data stack
: l-clr l :clear ; \ resets stack to zero items
[then]


0 value str? \ true if we are parsing a string
0 value num? \ true if we are parsing a number
0 value esc? \ true if we are parsing an escape sequence in a string

: setup
   false to str?
   false to num?
   false to esc?
   a-clr
   l-clr ;

128 array jump-table \ a jump table of xts

: fill-jump-table {: xt -- :}
  128 0 do xt jump-table :add loop ;

: c+ ( c --) l@ :ch+ ; \ add the char to the string on the l-stack
' c+ fill-jump-table

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
    >json >l t{ >a ; jt
' drop 
10 >jt
13 >jt drop
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
     >json-array >l  t[ >a ; jt

: (,) 0 {: j-str :}
     num? if l> dup to j-str :@ 2dup >integer
	             				   if nip nip >int j-str <free
	                               else >float if >flt j-str <free
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

: do-, ( c --)
    str? if c+ exit then drop
	l :size 2 < if exit then \ do nothing if } or ] has already handled it 
	a@ t[ <> if false to str? then (,) ; 

',' ' do-, jt

'}' :noname ( c --) str? if c+ exit then drop false to str? (,) a> drop ; jt
']' :noname ( c --) str? if c+ exit then do-,              a> drop ; jt

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

: processUnicode   0 0 >string {: uni -- :}
  4 0 do 1 adr +!  adr @ c@  uni :ch+  loop
  hex uni :@ evaluate decimal dup >r xc xc!+ drop xc r> xc-size ( adr len )
  l@ :add   uni <free ;

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
"qz�Bz": 10
} 

[then]

0 value max-adr

: processUni 
  adr @ dup 4 x-size >r
  dup r@ l@ :add
      r> + adr ! ;

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
  l :size if l> :! then ;


: refilling-parse ( -- c-addr u )
	begin
	   10 parse dup 0= 
	while
	  2drop refill 0= -39 and throw
	repeat ;

: j{ ( "<input stream>" -- json-obj )
  0 0 >string 0 0 >string {: s s1 :}
  begin
    refilling-parse 2dup s1 :! s" }j" s1 :searchCI 0=
  while
    s :add
  repeat 2drop
  s1 :delete
  0 s1 :start ! s1 :@sub s :add 
  s :@ $>json  s <free 
  s1 :delete 
  s1 :@ evaluate   s1 <free
  ; 

: json>$ {: json -- str-obj :} 
  0 0 >string dup
  ( str str ) json :write 
  json <free
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

