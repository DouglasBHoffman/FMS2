0 [if]

What is different about miniFMS from other minimalist ANS Forth object extentions?

1. Duck typing. The same message name can be used for objects from unrelated 
   (by inheritance) classes.

2. The initialization message is automatically sent to each newly instantiated object.
   This avoids the two-steo process of a) instantiate the object, b) initialize it.

3. Defining a message name, associating the method code with that name, and if necessary
   (automatically) over riding the superclass method: all done in one step instead of three.

4. No need to juggle the current object using, for example the return stack. It is
   cumbersome (and ugly IMO) to have to preface the use of an instance variable with
   something like R@ or R>.

5. A "METHOD?" error message is presented if an object does recognize a message sent
   to it, as opposed to just crashing.

[then]

\ Last Revision: 31 Aug 2021  12:11:38  dbh


0 value self
0 value ^class
: dfa ( cls -- a) 8 cells + ; 
9 cells constant classSize
: _mfa ( addr -- offset )  dup >r 2/ 2/ r@ xor
  2/ 2/ r> xor 7 and cells ;
: mfa ( sel cls -- sel mfa ) over _mfa + ;
: fm ( sel mfa -- xt )
  begin @ dup while
    2dup cell+ @ = if [ 2 cells ] literal + nip @ exit then
  repeat -1 abort" method?" ;
: class ( supClass 'name' -- ) create here to ^class
  classSize allot ^class classSize move ;
: ?isSel ( 'name' -- sel t | f ) bl word find
  if >body dup 1+ c@ 254 = if ( sel ) true exit then
  then drop false ;
: make-selector ( 'name' -- sel ) create here dup _mfa c, 254 c,
  does> over @ over c@ + fm self >r swap to self execute r> to self ;
: sel ( "name" -- sel ) >in @ ?isSel if ( in sel ) nip
  else >in ! make-selector then ;
: :m ( 'name' -- a xt ) sel ^class mfa
   here over @ , swap !  , here 0 , :noname ;
: ;m ( a xt -- ) postpone ; swap ! ; immediate
: :: ( class 'name' -- ) ' >body swap mfa fm compile, ; immediate
: (ivar) ( offset 'name' -- ) create , does> ( -- addr ) @ self + ;
: var ( n 'name' -- ) ^class dfa dup @ (ivar) +! ;
create object classSize dup allot object swap erase  cell object dfa !
object to ^class :m :init ;m
: (pre) ( cls flag -- cls n ) dup dfa @ ;
: (post) ( ...cls a -- obj ) tuck ! dup >r :init r> ;
: >dict ( cls -- obj ) (pre) ( align ) here swap allot (post) ;
: .. ( obj 'name' -- adr) ' >body @ + ;


0 [if] \ usage example

object class button  
  cell var text
  cell var len
  cell var x
  cell var y
 :m :init ( addr u -- ) len ! text ! 0 x ! 0 y ! ;m
 :m draw  x @ y @ at-xy text @ len @ type ;m

\ inheritance

: bold   27 emit ." [1m" ;
: normal 27 emit ." [0m" ;

button class bold-button  
 :m draw bold [ button :: draw ] normal ;m

\ Create and draw the buttons:

s" normal button" button >dict constant foo  \ implicit :init
s" bold button" bold-button >dict constant bar
1 bar .. y !
page
foo draw
bar draw


[then]

