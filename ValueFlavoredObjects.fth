\ Value Flavored Objects 

\ include /Users/doughoffman/ValueFlavoredObjects.fth
\ Last Revision:  1 Aug 2022  09:27:49  dbh

0 [IF]
 
The following is a significant modification of Andrew McKewan's class.fth
which is an ANS Forth version of the Neon/Yerk objects extension.

The following changes have been made:

1) (FINDM), which is used at run time for all dynamic binds,
    has been made more efficient.

WAS:
: mfa  ( selid ^class -- selid mfa )
	over 2/ 2/ 7 and cells + ; \ poor distribution on 64-bit system

: (findm)   ( selid ^class -- xt )	\ find method in a class
	mfa ((findm)) if  @ exit  then
	true abort" message not understood by class" ;

IS NOW:

: (findm)   ( selid ^class -- xt )	\ find method in a class
	over c@ + findLL if  @ exit  then
	true abort" message not understood by class" ;

2) The method lookup is distributed among 8 linked lists
   for efficiency. The code that computes which linked list
   to use has been modified for better distribution over
   those 8 linked lists, which also provides better efficiency
   for dynamic binding.

3) There is no requirement to have message names
    end with colon ":".
    
4) With class.fth it was possible to have a hard to find bug
   when a new message name was the same as a previous (non-message name) 
   dictionary entry. This code fixes that with the use of a message tag.

5) The dynamic binding syntax no longer uses " <message> [ <obj> ] ".
   Instead a message send to "**" will dynamically bind
   <message> to the object on the stack. " <obj> <message> ** "

6) The <Indexed and <General declarations for array classes are gone.
   They just add complexity and are not needed.
   
7) There are 2 advantages to a message-object ordering oop extension:
   1. No wordlists are needed for instance variable encapsulation
      (so also no need for a restore upon class compilation error).
   2. The instance variable declarations can be used as a struct
      because there is no header info. stored before each instance
      variable storage location.

8) If a new class is being defined, the "<super object" declaration
   is not needed when the superclass is class object.

9) All objects respond to the " .class " word which simply prints the
   name of the object's class.  Useful when debugging.

10) The " is-a " and " is-a-kind-of " utility words are provided.

[THEN] 


[undefined] cell [if] 1 cells constant cell [then]
[undefined] bounds [if] : bounds over + swap ; [then]
[undefined] noop [if] : noop ; [then]
[undefined] place [if]
   : place  ( src u dest -- )
     over >r rot over 1+ r> move c! ; 
[then]



: link ( addr -- )   here  over @ ,  swap ! ; 

0 value ^class		\ pointer to class being defined
0 value (classinit:)	\ selector for classinit: message
0 value self 

 : ifa ( ^cls -- addr)  8 cells + ; 
 : dfa ( ^cls -- addr)  9 cells + ; 
 : sfa ( ^cls -- addr) 10 cells + ;
 : cna ( ^cls -- addr) 11 cells + ;
 : tag ( ^cls -- addr) 12 cells + ;
 13 cells constant classsize 
 create classtag 

: >class  ( ^obj -- ^class )  \ get the class of an object
	cell - @ ;

: tag= ( ^cls -- flag) tag @ classtag = ;

: ?isobj  ( pfa -- ) @ dup if tag= then ; 

: ex-meth  ( ^obj xt -- ) self >r swap to self execute r> to self ; 

: _mfa ( addr -- offset )  dup >r 2/ 2/ r@ xor
  2/ 2/ r> xor 7 and cells ;

: mfa ( sel cls -- sel mfa ) over _mfa + ;

\ method-xt lookup: ( selid mfa -- mcfa true | false )
\ ivar lookup:      ( iv-hash ifa-addr -- ivar-cls true | false )
: findLL  ( key addr -- xxx true | false ) 
  begin @ dup 
  while 2dup cell+ @ = 
             if [ 2 cells ] literal + nip true exit then 
  repeat nip ; 

: (findm)   ( selid ^class -- xt )	\ find method in a class
	over c@ + findLL if  @ exit  then
	true abort" message not understood" ;

: find-method ( selid ^obj -- ^obj xt ) tuck >class (findm) ; 

: ex-iv  ( xt offset -- ) self >r self + to self execute r> to self ; 

: (defer)  ( ^obj selid -- )  over >class (findm) ex-meth ; 

: hash  ( addr len -- n )
  tuck bounds ?do  5 lshift  i c@ 32 or xor loop 
  dup 0< if exit then invert ; 

: hash>  ( -- n )  bl word count hash ; 

create ^self 0 , hash> self , 0 , 0 , 
create ^super ^self , hash> super , 0 , 0 , 
create meta classsize here over allot swap erase 
  ^super   meta ifa !  
  classtag meta tag ! 

: vfind  ( str -- str false | ^iclass true ) 
  ^class 
  if dup count hash ^class ifa findLL 
   dup if  rot drop  then 
  else false 
  then ; 

: classinit  ( addr -- )  \ send init: to newobject
	dup (classinit:)
	swap >class (findm) ex-meth ;

: <var ( ^class -- )
  bl word  
  count hash align ^class ifa link , dup , 
  ^class dfa @ ,  dfa @ ^class dfa +! ; 

: pre-scan ( -- in adr len) >in @ bl word count ;
: post-scan ( in adr1 cnt adr2 -- ) place >in ! ;

create lastParsedName 32 allot

: (obj)  ( "name" -- )  pre-scan lastParsedName post-scan   create  does> cell+ ; 

: build   ( ^class "name"-- ) 
  ^class
  if <var \ build an instance variable because we are inside a class
  else
     (obj) \ create a named object in the dictionary
     dup >r ,
     here \ to newobject
     r> dfa @ allot 
     ( here ) classinit \ send init: message
  then ; 

: >lower ( C -- c )
    dup [char] A [ char Z 1+ ] literal within if
        32 or
    then ;

: to-lower ( adr len -- ) \ convert entire string to lowercase in-place
  over \ addr cnt addr
  + swap  \ cnt+addr addr
  ?do i c@ >lower i c!
  loop ;

: do-scan pre-scan pad post-scan pad count to-lower ;

: scanForSuper ( addr --- )
  do-scan pad count s" <super" compare  \ addr $ptr flag
  if s" <super object" evaluate then ;  

: :class ( "name" -- addr) \ name of the new class being defined
    \ addr is passed to <super where the class name is stored at cfa
   >in @ bl word count ( n c-adr len ) here over 1+ allot dup >r place >in !  
   create 0 to ^class r> scanForSuper does> build ;

: icls! ( n ivar -- ) 2 cells + ! ; 

: <super ( addr "name" -- )  
  here to ^class classsize allot ' >body 
  dup ^class classsize move 
  dup ^class sfa !
  ^super icls! ^class ^self icls!
  ( addr) ^class cna ! ; \ store addr of className

: .class ( obj -- ) \ prints the class name of any object
  >class cna @ count type space ;

: ;class 0 to ^class ; 

: ?is** ( $ptr -- t/f ) count s" **" compare 0= ; 
: ?isclass  ( pfa -- f ) tag= ;  \ is this a valid class?

: reftoken ( str -- xt tokenid | tokenid ) 
  dup ?is**   if  exit   then 
  find if dup >body ?isobj if  0  exit   then 
          dup >body ?isclass if >body (findm)
                                state @ if postpone literal  postpone ex-meth
                                        else ex-meth
                                        then 3 exit
                             then 
       then
       true abort" invalid object" 
  ; 


: ivarref   ( selid ^iclass -- ) 
   ." "  \ band aid
  cell+ find-method  swap @  ( xt offset )
   ." "  \ band aid
  ?dup 
  if swap  postpone literal  postpone literal postpone ex-iv 
  else compile, \ optimise when offset=0
  then ; 

: compileref ( selid $str -- ) 
  reftoken dup 3 = if drop exit then 
           if postpone literal postpone (defer) 
           else >body 
           cell+ find-method swap ( xt ^obj ) 
   postpone literal  postpone literal  postpone ex-meth then ; 

: runref ( selid $str -- ) 
  reftoken dup 3 = if drop exit then 
  ( reftoken ) if ( ^obj selid )  swap  find-method 
           else  >body  cell+  find-method 
           then ex-meth ; 

: message   ( selid -- )
  bl word  state @
  if ( we are compiling)
     vfind \ instance variable or SELF or SUPER ?
     if   ivarref 
     else  compileref \ message to object or class or ** 
     then 
  else ( we are interpreting or running) runref 
  then ; 

\ force the creation of a message. this can be done outside of a class definition
: selector  ( "name" -- sel) create here dup _mfa c, 254 c, immediate  does> message ; 

: getselect ( 'name' -- sel ) >in @ bl word find if >body dup 1+ c@ 254 =
  if nip exit then then drop >in ! selector ;


getselect init: to (classinit:)

: :m  ( "name" -- adr xt )
    getselect align ^class  mfa  link ( selid ) , here 0 , :noname ; 

: ;m ( adr xt -- )
      postpone ; swap ! ( save xt )
      ; immediate 

:class object  <super meta
	:m addr: ( -- addr)  self ;m	\ get object address
	:m init: ;m	\ null method for object init
	:m free: ;m	\ null method for object release
;class


\ Bytes is used as the instance variable allocation primitive for basic classes
\ It creates an object of class Object that is n bytes long.
\ You can get the address by sending it an addr: message.

: (ivar) ( offset 'name' -- ) create immediate ,
  does> ( -- addr) @ postpone literal postpone self postpone + ;

: bytes  ( n -- ) 
   ['] object >body <var  ^class dfa +! ;

: allocobj  ( size class -- obj )  \ allocate object and store in newobject
	over cell+		\ allow for class ptr
	allocate throw	\ ( size class addr -- )
	dup cell+ >r  \ object address
	! r> ;		\ create the class ptr

: (heapobj)  ( class -- ^obj )
	>r  ( save class on return stack )
	r@ dfa @  ( ivar data size )
	r> allocObj	
	dup classinit		\ send classinit: message to new object
	 ;		\ return object address

\ heap> is compile time only
: heap>   ( -- addr )
	' >body postpone literal  postpone (heapobj) ; immediate

: <free  ( ^obj -- )	\ free heap object
	dup free: **	\ send free: message to object
	cell - free throw ;	\ deallocate it

: is-a ( obj "classname" -- flag ) 
  state @
  if
   postpone >class ' >body postpone literal postpone =
  else
   >class ' >body =
  then
  ; immediate


: (is-a-kindOf) ( object-class target-class -- flag )
  swap
  begin
    2dup = if 2drop true exit then
    sfa @ dup ['] object >body = if 2drop false exit then
  again ;

: is-a-kindOf ( obj "classname" -- flag )
  state @
  if
   postpone >class ' >body postpone literal postpone (is-a-kindOf)
  else
   >class ' >body (is-a-kindOf)
  then
  ; immediate



\ generic container class for convenience
:class var
 cell bytes data
 :m get: ( -- n ) addr: data @ ;m
 :m put: ( n -- ) addr: data ! ;m
;class

0 [if]

:class point
 var x
 var y
:m init: ( x y -- ) put: y  put: x ;m
:m get: ( -- x y ) get: x  get: y ;m
:m put: ( x y -- ) init: self ;m
;class

10 20 point p
get: p . . \ => 20 10


\ note that the init: message is automatically sent ONLY to the
\ owning object (rect object in this case). For the instance variable
\ objects UL and LR init: must be explicitly sent.
:class rect
 point ul
 point lr
:m init: ( x1 y1 x2 y2 -- ) init: lr  init: ul ;m
:m get: ( -- x1 y1 x2 y2 ) get: ul  get: lr ;m
;class

3 4 15 16 rect r
get: r . . . . \ => 16 15 4 3

r ? \ => 3  ok
r cell+ ? \ => 4  ok
r 2 cells + ? \ => 15  ok
r 3 cells + ? \ => 16  ok



[then]

