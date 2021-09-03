0 [if]

What is different about miniFMS from other minimalist ANS Forth object extentions?

1. Duck typing. The same message name can be used for objects from unrelated 
   (by inheritance) classes.

2. The initialization message is automatically sent to each newly instantiated object.
   This avoids the two-steo process of a) instantiate the object, b) initialize it.

3. Defining a message name, associating the method code with that name, and if necessary
   (automatically) over riding the superclass method: all done in one step instead of three.

4. No need to juggle the current object using, for example the return stack. It is
   cumbersome (and ugly IMO) to have to preface each(most) use of an instance variable with
   something like R@ or R>.

5. A "METHOD?" error message is presented if an object does recognize a message sent
   to it, as opposed to just crashing.

Note: No wordlists are used and there is direct access to instance variables 
      (no accessor methods needed). But this is common for a minimalist extension).

[then]

\ Last Revision:  2 Sep 2021  17:45:20  dbh


0 value self
: dfa ( cls -- a) 8 cells + ; 
: _mfa ( adr -- ofs) dup >r 2/ 2/ r@ xor 2/ 2/ r> xor 7 and cells ;
: mfa ( sel cls -- sel mfa) over _mfa + ;
: fm ( sel mfa -- xt) begin @ dup while 2dup cell+ @ = 
  if 2 cells + nip @ exit then repeat -1 abort" method?" ;
: class ( supClass 'name' -- cls) create here >r
  9 cells dup allot r@ swap move r> ;
: ?isSel ( 'name' -- sel t | f) bl word find
  if >body dup 1+ c@ 254 = if true exit then then drop false ;
: ms ( 'name' -- sel ) create here dup _mfa c, 254 c,
  does> over @ over c@ + fm self >r swap to self execute r> to self ;
: sel ( "name" -- sel ) >in @ ?isSel if nip else >in ! ms then ;
: :m ( cls 'name' -- a xt) sel over mfa
   here over @ , swap !  , here 0 , :noname ;
: ;m ( a xt -- ) postpone ; swap ! ; immediate
: :: ( cls 'name' -- ) ' >body swap mfa fm compile, ; immediate
: (ivar) ( offset 'name' -- ) create , does> ( -- addr ) @ self + ;
: var ( cls n 'name' -- ) over dfa dup @ (ivar) +! ;
create object 9 cells dup allot object swap erase  cell object dfa !
object :m :init ;m drop
: new ( cls -- obj) dup dfa @ here swap allot tuck ! dup >r :init r> ;
: .. ( obj 'name' -- adr) ' >body @ + ;


0 [if] \ usage example

object class button  
  cell var text
  cell var len
  cell var x
  cell var y
 :m :init ( addr u -- ) len ! text ! 0 x ! 0 y ! ;m
 :m draw  x @ y @ at-xy text @ len @ type ;m
drop

\ inheritance

: bold   27 emit ." [1m" ;
: normal 27 emit ." [0m" ;

button class bold-button  
 :m draw bold [ button :: draw ] normal ;m
drop

\ Create and draw the buttons:

s" normal button" button new constant foo  \ implicit :init
s" bold button" bold-button new constant bar
1 bar .. y !
page
foo draw
bar draw


[then]



0 [if] \ another example
object class barray
 cell var tflags
 cell var sz
  :m :init ( sz -- ) here over allot tflags ! sz ! ;m
  :m :fill {: c -- :} tflags @ sz @ c fill ;m 
  :m :at ( idx -- c ) tflags @ + c@ ;m
  :m :to ( c idx -- ) tflags @ + c! ;m
drop

barray class sieve
 :m prime {: | lo hi -- :}
  1 [ barray :: :fill ]
  0 sz @ 0
  DO i [ barray :: :at ]
  IF i 2* 3 + dup to lo i + to hi
   BEGIN hi sz @ <
   WHILE 0 hi [ barray :: :to ] lo +to hi
   REPEAT 1+
  THEN
  LOOP ( . ) drop ;m
drop

8190 sieve new constant s
s prime \ => 1899
: go 10000 0 do s prime loop ;
ticks go ticks swap - . \ => 780 msec  vfx

[then]

0 [if] \ alternative definition (using late binding)
barray class sieve
 :m prime {: | lo hi -- :}
  1 self :fill 
  0 sz @ 0
  DO i self :at 
  IF i 2* 3 + dup to lo i + to hi
   BEGIN hi sz @ <
   WHILE 0 hi self :to lo +to hi
   REPEAT 1+
  THEN
  LOOP  ( . ) drop  ;m
drop

8190 sieve new constant s
s prime \ => 1899
: go 10000 0 do s prime loop ;
ticks go ticks swap - . \ => 1610 msec  vfx

[then]



