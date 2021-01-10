[undefined] >string [if] cr .( file string.f required ) abort [then]
\ January1, 2021 dbh  https://github.com/DouglasBHoffman/FMS2

[undefined] >int [if] cr .( file int.f required ) abort [then]
[undefined] >flt [if] cr .( file flt.f required ) abort [then]

\ This parser is based on the ECMA standard as described here:
\     https://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf
\ with the exception that only ASCII is supported, not UTF-8 or unicode

\ It is a table based json parser. 
\ Each character of the JSON text is an index into the 128 cell
\ table. Each cell contains an XT appropriate for that character.
\ So the algorithm simply steps through each character and executes
\ the XT for that character. One-pass. No backing up or looking ahead.
\ A stack is used to push and pop json objects as they are
\ created and consumed. This is the l stack.
\ This is a state-based one-pass parser. The state is maintained
\ using 2 extra stacks and three global variables:
\ str? (are we parsing a string?), num?(are we parsing a number?)
\ and esc?(are we parsing an escape character?).

\ Note that no effort is made to detect invalid JSON formatting.


:class json-string <super string
 :m :. '"' emit super :. '"' emit ;m

 :m :write {: str -- :}
    '\' str :ch+  '"' str :ch+
      begin
       super :each
      while
        dup case
             '"' of '\' str :ch+ endof 
             '\' of '\' str :ch+ endof
               8 of '\' str :ch+ drop 'b' endof \ backspace
              12 of '\' str :ch+ drop 'f' endof \ form feed
            ( all others dropped) endcase str :ch+
      repeat '\' str :ch+ '"' str :ch+ ;m


;class
: >json-string heap> json-string ;

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

:noname ( c --) str? if esc? if case
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

'n' >jt
't' >jt
'f' >jt drop

0 value max-adr


: $>json ( adr len -- json-obj )
  setup
  ( adr cnt ) >r adr ! adr @ r> + to max-adr
  begin
   adr @ c@ dup jump-table :at execute
   1 adr +!
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

0 [if] \ not used
\ IMPORTANT: }j must be alone on a single line and must be lower case
: j{ ( "<input stream>" -- json-obj )
  0 0 >string {: s :}
  begin
    refilling-parse 2dup s" }j" compare 
  while
    s :add
  repeat 2drop s :@ $>json  s <free
  ( l :size if l> :! then) ;
[then]


: key-val>Pair ( adr len val -- pair-obj )
  -rot >json-string >pair ( val pair-obj ) :! ;



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

stopincluding

0 [if]

j{ "hello": null 
}j
dup :. . 
  "hello": null 16259664 ok
16259664 .class pair ok

.l ok




.l ok \ 1 
. 15819088 ok
15819088 .class pair ok

15982608 .class null ok

.l ok

.l 
0 15982624 ok
.a ok
l :size . 1 ok
15982624 :. "hello": "<empty-val>"ok






j{ {
  "f": "J o" }
}j value j1
 
j1 :. 
{
"f": "J o"
}ok



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


j json>$ value s  ok

 
s :.  {
"firstName": "John", 
"lastName": "Venkman", 
"isAlive": true, 
"age": 27, 
"address": {
"streetAddress": "21 2nd Street", 
"city": "New York", 
"state": "NY", 
"postalCode": "10021-3100"
}, 
"phoneNumbers": [{
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



: key-val>Pair ( adr len val -- pair-obj )
  -rot >json-string >pair ( val pair-obj ) :! ;
 
s" hello" >null key-val>Pair dup :. .   "hello": null 16124752 ok
16124752 :. "hello": nullok
j{ [4, 67, 68.9, "dog" ] }j dup :. . [ 4, 67, 68.9 , "dog"] 16393776 ok
>json ok \ 1 
16124752 over :add ok \ 1 
16393776 over :add . 15786176 ok
15786176 :. 
{
"hello": null, 
[ 4, 67, 68.9 , "dog"]
}ok
15786176 .class json ok
15786176 :size . 2 ok
0 15786176 :at .class pair ok
1 15786176 :at .class json-array ok
1 15786176 :at . 16393776 ok
16393776 :size . 4 ok
0 16393776 :at .class int ok
2 16393776 :at .class flt ok
3 16393776 :at .class json-string ok


s\" {\"hello\": null}" $>json .  16070096 ok
16070096 :. 
{
"hello": null
}ok

16431344 :. nullok

16171264 :. nullok

dup :.  nullok \ 1 


\ build a json structure manually:
>json  value j  ok
s" value" >json-string >pair   ok \ 1 
10 >int  ok \ 2 
swap :!   ok \ 1 
j :add  ok
j :. 
{
"value": 10
}ok

s" flag" >json-string >pair 
false >bool swap :! j :add ok
j :. 
{
"value": 10, 
"flag": false
}ok


s" array" >json-string >pair ok \ 1 
>json-array ok \ 2 
1 >int ok \ 3 
over :add ok \ 2 
2 >int over :add ok \ 2 
3 >int over :add ok \ 2 
swap :! ok \ 1 
j :add ok
j :. 
{
"value": 10, 
"flag": false, 
"array": [ 1, 2, 3]
}ok

j :size . 3 ok
2 j :at :. "array": [ 1, 2, 3]ok
2 j :at :@ . . 13192848 15801136 ok
13192848 .class json-string ok
15801136 .class json-array ok


s" test" >json-string >pair dup :. . "test": "<empty-val>" 16311632 ok
4.5e >flt 16311632 :! ok \ 1 
:. "test": 4.5 ok


Forth has no built-in higher level data structures such as arrays,
dynamically resizeable arrays, strings, dynamically resizeable
strings, and objects. There is no standardized Forth library to build
and use such structures. But there are many different Forth libraries,
written by individuals,available, though finding them is not always easy.
The syntax and behavior is different for each.
The library code used below can be found here:
 https://github.com/DouglasBHoffman/FMS2

Load a JSON string into a data structure.

s\" {\"value\":10,\"flag\":false,\"array\":[1,2,3]}" $>json value j 
j :.    
{
"value": 10, 
"flag": false, 
"array": [ 1, 2, 3]
}ok

Create a new data structure and serialize it into JSON.

j{ "another":"esc\"aped" }j 1 j :insert ok
j :. 
{
"value": 10, 
"another": "esc"aped", 
"flag": false, 
"array": [ 1, 2, 3]
}ok



Convert the JSON object into a string.

j json>$ cr :. 
{\"value\":10,\"another\":\"esc\"aped\",\"flag\":false,\"array\":[1,2,3]}ok



[then]

