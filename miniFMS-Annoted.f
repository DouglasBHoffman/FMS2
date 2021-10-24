\ Last Revision: 24 Oct 2021  11:06:08  dbh

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

5. New methods can be defined for any alread-defined class. Alread-instantiated objects
   will respond to these new methods.

6. A "METHOD?" error message is presented if an object does not recognize a message sent
   to it, as opposed to just crashing.

7. Adding a way to allocate objects is trivial.

Note: No wordlists are used and there is direct access to instance variables 
      (no accessor methods needed) provided they are not shadowed. 
      But this is common for a minimalist extension.

For a full-featured OOP with some library code see: https://github.com/DouglasBHoffman/FMS2

[then]




0 value self \ will contain the current object

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
    if 2 cells + nip @ exit then \ payload is xt, 2 cells offset from node
  repeat -1 abort" method?" ; \ meth? => method not found

\ create the new class name and copy the 9 cells from
\ the superclass to the new class for inheritance of the
\ linked-lists (methods) and instance variables (dfa)
: class ( supClass 'name' -- cls) create here >r
  9 cells dup allot r@ swap move r> ;

\ create a new selector with the given name
: makeSel ( 'name' -- sel ) create 
  here dup _mfa c, \ grab a new unique address, compute its associated offset into the n-way lists
              \ and store that offset. The does> action of this definition will
              \ return that unique adress (or sel). The sel address also points
              \ to the n-way linked list offset.



   254 c, \ tag this definition as a selector with the (hopefully) unique
          \ number at the given offset
  does> ( obj addr ) \ the action of the message is to fetch the ^class from the first
                     \ cell of the object, add the n-way offset to that,
                     \ and do a linked list search for the method xt.
                     \ Then store the old self and place the object address in self.
                     \ Lastly execute the xt and restore self.
   
  over @ over c@ + fm self >r swap to self execute r> to self ;

\ make a new selector ONLY if it is not already a selector
\ if it is not a selector then shadow the existing definition
\ if there is one
: sel ( 'name' -- sel ) >in @ bl word find if >body dup 1+ c@ 254 =
   if nip exit then then drop >in ! makeSel ;

\ possibly make a new message with sel, regardless make a new method
\ definition with :noname
: :m ( cls 'name' -- a xt) sel over mfa
   here over @ , swap !  , here 0 , :noname ;

\ store the method xt in the right place for this method
: ;m ( a xt -- ) postpone ; swap ! ; immediate


\ given the class and a message name, early bind the object on
\ the stack to the method found by fm.
\ This syntax can replace SUPER and ESELF
: :: ( cls 'name' -- ) ' >body swap mfa fm compile, ; immediate


\ The action of an instance variable is to return its address
\ which is the address of the object, self, plus the offset.
\ Important: instance variable names are not encapsulated
\ meaning they can be shadowed by any subsequent definition.
\ So if this you will be shadowing your instance variable names
\ but you still want to access them then you should define "getter"
\ and "setter" methods for them.
: (ivar) ( offset 'name' -- ) create , does> ( -- addr ) @ self + ;

\ dfa +! keeps the running offset updated for this class
: var ( cls n 'name' -- ) over dfa dup @ (ivar) +! ;

\ manually construct the class OBJECT
create object 9 cells dup allot object swap erase  cell object dfa !

\ give class object an :INIT method (that does nothing)
object :m :init ;m drop


\ A simple way to instantiate a new nameless object in the
\ dictionary. Note that all objects have their class pointer
\ stored in the first cell. Instance variables follow the class
\ pointer.
: new ( cls -- obj) dup dfa @ here swap allot tuck ! dup >r :init r> ;

-1 [if] \ usage example

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

s" normal button" button new constant foo
s" bold button" bold-button new constant bar
1 bar to self y !
page
foo draw
bar draw


\ another example
\ note re-use of draw (and there is no inheritance relationship)
object class point
  cell var x
  cell var y
 :m p! ( x y -- ) y ! x ! ;m
 :m p@ ( -- x y ) x @ y @ ;m
 :m draw x ? y ? ;m
 :m :init ( x y -- ) self p! ;m  \ late bind
\ :m :init ( x y -- ) [ point :: p! ] ;m \ alternatively early bind
drop

1 2 point new constant p1
p1 draw cr
foo draw  \ draw still works on foo and bar
cr bar draw
: test 3 4 p1 p! p1 draw  p1 to self x @ y @ + . ;
test
\ => 3 4 7

[then] 