[undefined] >string [if] cr .( file string.f required ) abort [then]
[undefined] >int [if] cr .( file int.f required ) abort [then]
[undefined] >flt [if] cr .( file flt.f required ) abort [then]


\ A jump table based json parser. 
\ A stack is used to push and pop json objects as they are
\ created and consumed. This is the l stack.
\ This is a state-based one-pass parser. The state is maintained
\ using a second stack, the a stack, and two global variables:
\ str? (are we parsing a string?), num?(are we parsing a number?).

\ Each character of the JSON text is an index into the 128 cell
\ jump table that contains an XT appropriate for that character.


:class json-string <super string
 :m :. '"' emit super :. '"' emit ;m
 :m :write ( str -- )
     locals| str |
    '"' str :ch+  self :@ str :add  '"' str :ch+ ;m
;class
: >json-string heap> json-string ;

:noname cr :. ',' emit space ; value xt

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
  :m :write ( str -- )
     locals| str |
     '{' str :ch+
     super :size 0 >
     if
       super :size 1- 0 ?do 10 str :ch+    str i super :at ( pair )  :write 
                            ',' str :ch+ bl str :ch+ loop
                            10 str :ch+   str super :last ( pair ) :write
     then 10 str :ch+ '}' str :ch+ ;m
   :m :search ( adr len -- val t | f )
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
  :m :write ( str -- )
      locals| str |
     '[' str :ch+
     super :size 0 >
     if
       super :size 1- 0 ?do  str i super :at ( pair )  :write 
                            ',' str :ch+ bl str :ch+ loop
                            10 str :ch+   str super :last ( pair ) :write
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
: a@ ( -- n ) a :last ; \ retrieve top stack item
: a-clr a :clear ; \ resets stack to zero items

\ 2 array types for a stack in json parser
0 constant t{
2 constant t[

:class bool
 1 bytes data
 :m :init ( b -- ) data c! ;m
 :m :! ( b --) data c! ;m
 :m :@ ( -- b ) data c@ ;m
 :m :. data c@ if ." true" else ." false" then ;m
 :m :write ( str --)
     locals| str |
     data c@ if s" true" else s" false" then str :add ;m
;class
: >bool ( b -- bool-obj) heap> bool ;

:class null
  :m :. ." null" ;m
  :m :write \ { str --}
      locals| str |
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
  :m :write ( str -- )
     locals| str |
     str key @ :write
     ':' str :ch+  bl str :ch+
     str val @ :write
     ;m
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
: l@ ( -- n ) l :last ; \ retrieve top stack item
: l-clr l :clear ; \ resets stack to zero items
[then]

0 value str? \ true if we are parsing a string
0 value num? \ true if we are parsing a number

: setup
   false to str?
   false to num?
   a-clr
   l-clr ;

128 array jump-table \ a jump table of xts

: fill-jump-table ( xt -- )
  locals| xt |
  128 0 do xt jump-table :add loop ;

: c+ ( c --) l@ :ch+ ; \ add the char to the string on the l-stack
' c+ fill-jump-table

: jt ( c xt -- ) swap jump-table :to ;
: >jt ( xt c -- xt ) over jt ;

'{' :noname ( c --) 
    str? if c+ exit else drop then
    >json >l t{ >a ; jt
:noname ( c --) drop ; \ a noop
10 >jt
13 >jt drop
:noname ( c --) str? if c+ else drop then ;
8  >jt
32 >jt drop
'"' :noname ( c --) drop
     str? if false to str? 
          else true to str? 0 0 >json-string >l
          then ; jt
':' :noname ( c --)
    str? if c+ exit then drop
    l> >pair >l ; jt

'[' :noname ( c --) 
    str? if c+ exit then drop
     >json-array >l  t[ >a ; jt

: (,) 0 locals| j-str |
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

'}' :noname ( c --) 
    str? if c+ exit then drop
    a> drop false to str?  (,) ; jt

']' :noname ( c --)
    str? if c+ exit then 
    do-, a> drop ; jt


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
 
:noname ( c --) str? if c+
       			   else drop >null >l
       			        3 adr +!
       			   then ;

'n' >jt
'N' >jt drop
 
:noname ( c --) str? if c+
                   else drop true >bool >l
                        3 adr +!
                   then ;

't' >jt
'T' >jt drop                   
 
:noname ( c --) str? if c+
                   else drop false >bool >l
                        4 adr +!
                   then ;

'f' >jt
'F' >jt drop

0 value max-adr

: $>json ( adr len -- json-obj )
  setup
  ( adr cnt ) >r adr ! adr @ r> + to max-adr
  begin
   adr @ c@ dup jump-table :at execute
   1 adr +!
   adr @ max-adr <
  while
  repeat l> ;

: j{ ( "<input stream>" -- json-obj )
  0 0 >string locals| s |
  begin
    refilling-parse-name 2dup s" }j" compare 0<> >r
                         2dup s" }J" compare 0<> r> and
  while
    s :add
  repeat 2drop s :@ $>json  s <free ;

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
 ok


j :.  
{
"firstName": "John", 
"lastName": "Smith", 
"isAlive": true, 
"age": 27, 
"address": 
{
"streetAddress": "212ndStreet", 
"city": "NewYork", 
"state": "NY", 
"postalCode": "10021-3100"
}, 
"phoneNumbers": [ 
{
"type": "home", 
"number": "212555-1234"
}, 
{
"type": "office", 
"number": "646555-4567"
}], 
"children": [], 
"spouse": null
}ok

s" lastname" j :search .s \ => "Smith"( 2 ) \ 16087920 \ -1 ok

s" Venkman" 16087920 :! ok
j :. 
{
"firstName": "John", 
"lastName": "Venkman", 
"isAlive": true, 
"age": 27, 
"address": 
{
"streetAddress": "212ndStreet", 
"city": "NewYork", 
"state": "NY", 
"postalCode": "10021-3100"
}, 
"phoneNumbers": [ 
{
"type": "home", 
"number": "212555-1234"
}, 
{
"type": "office", 
"number": "646555-4567"
}], 
"children": [], 
"spouse": null
}ok

0 0 >string value s 
s j :write ok
 
s :. {
"firstName": "John", 
"lastName": "Venkman", 
"isAlive": true, 
"age": 27, 
"address": {
"streetAddress": "212ndStreet", 
"city": "NewYork", 
"state": "NY", 
"postalCode": "10021-3100"
}, 
"phoneNumbers": [{
"type": "home", 
"number": "212555-1234"
}, 
{
"type": "office", 
"number": "646555-4567"
}], 
"children": [], 
"spouse": null
} ok

s\" [[\"foo\",1],[\"bar\",[10,\"apples\"]]]" $>json value j2 ok
j2 :. [ [ "foo", 1], [ "bar", [ 10, "apples"]]]ok
j2 :size . 2 ok
0 j2 :at :. [ "foo", 1] ok



[then]