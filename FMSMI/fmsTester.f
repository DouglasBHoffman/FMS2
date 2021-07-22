\ 02/18/12 dbh
\ added testing of dict> 2-array btree
\ Last Revision: 12/03/11 dbh
\ test for SELF and SUPER edge conditions
\ added dot parser tests

DECIMAL

cr .( Test Basic Objects and Messaging )
cr .( testing interpret early bind ) 

var x
33 x !:
T{ x @: -> 33 }T


3 x +:     
T{ x @: -> 36 }T

cr .( testing compile early bind ) 

: test 33 x !: x @: ;
T{ test -> 33 }T

cr .( testing interpret late bind ) 

var x  x value y
33 y !:
T{ y @: -> 33 }T

3 y +:     
T{ y @: -> 36 }T

cr .( testing compile late bind ) 

: test 33 y !: y @: ;
T{ test -> 33 }T

cr .( Verify mixing message sends to public objects and ivars in a method )
var x1 66 x1 !:
var x2 77 x2 !:

:class var2 <super var
  :m get: self @: x1 @: self @: x2 @: ;m
;class

var2 v2 88 v2 !: 

T{ v2 get: -> 88 66 88 77 }T

bool b
T{ b @: -> 0 }T
b set:
T{ b @: -> -1 }T
b clear:
T{ b @: -> 0 }T


cr .( testing indexed objects ) 

5 dicArray a

T{ a size: -> 5 }T
77 3 a to:
T{ 3 a at: -> 77 }T

: test 3 a at: ;
T{ test -> 77 }T

0 a fill:
T{ test -> 0 }T

cr .( testing each: and heap> ) 

45 2 a to:

: test begin a each: while  repeat ;

T{ test -> 0 0 45 0 0 }T 

: v heap> var ;


v 0 a to:
v 1 a to:
v 2 a to:
v 3 a to:
v 4 a to:


: test2 begin a each: while @: repeat ;

T{ test2 -> 0 0 0 0 0 }T

: add2 ( var-obj -- )
  2 swap +: ;

: test3 begin a each: while add2 repeat ; 

T{ test3 test2 -> 2 2 2 2 2 }T
T{ test3 test2 -> 4 4 4 4 4 }T

: test4 begin a each: while <free repeat ; test4

cr .( testing array )

array  b
3 b new:



10 0 b to:
20 1 b to:
30 2 b to:



: test5 begin b each: while repeat ;

T{ test5 -> 10 20 30 }T


5 b resize:

99 b fill:


T{ 0 b at: 4 b at: -> 99 99 }T


b free:
\ ok to here
4 b new:

100 200 300 400 4 b set:

T{ 3 b at: -> 400 }T

2 b delete:
T{ 2 b at: -> 400 }T
T{ b size: -> 3 }T
b free:


cr .( testing string+ )

true TO case-sensitive?
string+  s



s" Now is" s new:  s"  the time" s add:

T{ s @:  s" Now is the time" COMPARE -> 0 }T

s free:


string+  s2
s" Now is the time for all" s2 new:
T{ s"  all" s2 search: -> -1 }T
s2 delete:  
T{ s"  all" s2 search: ->  0 }T

s2 reset:  
T{ s"  time" s2 search: ->  -1 }T
s2 delete:  
T{ s2 @:  s" Now is the for" COMPARE ->  0 }T
s2 free:

s" Now is the time" s new:

T{ s selectall: s @sub:  s" Now is the time" COMPARE -> 0 }T
T{ s @sub: s" Now is the time" COMPARE -> 0 }T
T{ s @sub: s" Now is THE time" COMPARE -> 1 }T

false TO case-sensitive?
T{ s" Now is THE time" s =: -> TRUE }T

true TO case-sensitive?
T{ s" Now is THE time" s =: -> FALSE }T

s reset:
T{ s" THE" s search: -> FALSE }T

s reset:
false TO case-sensitive?
T{ s" THE" s search: -> TRUE }T


s free:

cr .( testing string+ replall: )

true to case-sensitive?
string+ dot$
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ !:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ add:

create s1 ," ."
create s2 ,"  IV "

: test s1 count s2 count dot$ replall: ;

test

T{ dot$ size: -> 2373 }T
T{ dot$ rem: -> 2373 }T
T{ dot$ start: @ -> 0 }T
T{ dot$ end: @ -> 0 }T



cr .( testing xstring )

25 xstring  xs

s" Now" xs !:
s"  is the tim" xs add:
char e xs +:

T{ xs @:  s" Now is the time" COMPARE ->  0 }T

cr .( testing late binding to self )
cr .( testing methodless ivar access )
cr

:class point <super object 
  var x
  var y
  :m show:
         x p:  \ access ivar via message
         y @ . \ access ivar via methodless means
        ;m 
  :m dot: ." Point at "  [self] show: ;m
\  :m dot: ." Point at "  self show: ;m \ alternative that will affect objects of class label-point
;class 

point  origin

\ methodless ivar access
5 origin iv x !
8 origin iv y !

: test55 origin [iv] x @ ;

T{ test55 -> 5 }T


: test6 origin [iv] y @ ;

T{ test6 -> 8 }T 


origin dot:  .( =>  Point at 5 8 )


cr .( testing object array interpreted )

5 objArray() point points()
55  0 points() iv x !
88  0 points() iv y !
cr
0 points() dot:   .( => Point at 55 88 )
cr
4 points() dot:   .( => Point at 0 0 )

cr .( testing object array compiled )

5 objArray() var vars()
55  0 vars() !:
0 vars() VALUE v
: test v @: ;
T{ test -> 55 }T
: test2 0 vars() @: ;
T{ test2 -> 55 }T

:class rectangle <super object
  point ul
  point lr
  :m show:  ul dot:   lr dot: ;m
  :m dot: ." Rectangle, "  self show: ;m
  :m p: self dot: ;m
;class 

rectangle  r

cr
r dot: .( => Rectangle, Point at 0 0 Point at 0 0 )


:class label-point <super point
  :m show: ." X"  x @ .  ." Y"  y @ .  ;m
;class 

label-point  poo


cr
poo dot: .( =>  Point at X0 Y0 )  .( \ proof that show: is late-bound in class point )


cr .( testing ordered collection )

5 ordered-col+  c

10 20 30 40 4 c set:

T{ 0 c at: -> 10 }T

T{ c last: -> 40 }T

T{ 30 c search: -> 2 -1 }T

2 c delete:

: test7 begin c each: while repeat ;

T{ test7 -> 10 20 40 }T

T{ 50 c add: test7 -> 10 20 40 50 }T 

T{ c first: -> 10 }T

T{ c removeFirst: test7 -> 20 40 50 }T 

T{ 5 c addFirst: test7 -> 5 20 40 50 }T

T{ c sum: -> 115 }T

T{ c max: -> 50 }T

T{ c min: -> 5 }T

T{ 5 c add: test7 -> 5 20 40 50 5 }T

T{ 5 c occurrencesOf: -> 2 }T

T{ 60 c occurrencesOf: -> 0 }T

: test8 30 < ;

T{ ' test8 c conform: -> 0 }T  \ all elements do not conform

: test9 60 < ;

T{ ' test9 c conform: -> -1 }T  \ all elements do conform

' test8 c accept: value acc  \ a new collection whose elements pass accept: test

: test10 begin acc each: while  repeat ;

T{ test10 -> 5 20 5 }T 

acc <free


: test11 2 + ;

' test11 c collect: value coll  \ a new collection transformed by collect:

: test12 begin coll each: while  repeat ;

T{ test12 -> 7 22 42 52 7 }T

coll <free

cr .( testing dict> )

10 ordered-col coll3

: Add-coll3
  dict> var coll3 add:
  10 dict> xstring coll3 add:
  dict> var coll3 add:
  dict> rectangle coll3 add:
  dict> string coll3 add:
;

Add-coll3

T{ 0 coll3 at: classname:  s" VAR"       COMPARE -> 0 }T
T{ 1 coll3 at: classname:  s" XSTRING"   COMPARE -> 0 }T
T{ 2 coll3 at: classname:  s" VAR"       COMPARE -> 0 }T
T{ 3 coll3 at: classname:  s" RECTANGLE" COMPARE -> 0 }T
T{ 4 coll3 at: classname:  s" STRING"    COMPARE -> 0 }T

s" Hello" 4 coll3 at: !:
T{ 4 coll3 at: @: s" Hello" COMPARE -> 0 }T
4 coll3 at: free:


cr .( testing init: super super> class_as> )

:class var1 <super var
  cell bytes data1
 :m !: ( n -- ) data1 ! ;m
 :m +: ( n -- ) data1 +! ;m
 :m @: ( -- n ) data1 @ ;m
 :m p: ( data ) data1 @ . ;m \ print self
 :m init: 55 self !: ;m
;class



var1 v1
T{ v1 @: -> 55 }T \ verifies init: for self



:class var2 <super var1
   cell bytes data2
   var1 x
 :m !: ( n -- ) data2 ! ;m
 :m +: ( n -- ) data2 +! ;m
 :m @: ( -- n ) data2 @ ;m
 :m p: ( data ) data2 @ . ;m \ print self
 :m init:  100 self !: ;m
 :m dump: x @:  self @: super @: super> var @: ;m
;class



var2 v2
T{ v2 dump: -> 55 100 55 0 }T \ verifies init: for embedded ivar objects, self, super, and super>

v2 value vv2

: test vv2 class_as> var2 dump: ;
T{ test -> 55 100 55 0 }T \ exercises class_as>

: test v2 ;

: test2 test dump: ;

 \ The following exercises a compiled dictionary object name that is *not* directly
 \ followed by a message name.  In this case the object system will simply leave the ^obj
 \ which can be manipulated any way we wish including very indirectly sending a message.
T{ ' test2 execute -> 55 100 55 0 }T


:class test-init <super var2
   var2 var2-ivar
   rec{ var rec-y
        var rec-x
        }rec
   var2 var2-ivar2
   \ 1 bytes data \ will error => duplicate ivar name
:m dump: super dump: var2-ivar dump: rec-y @ rec-x @
         var2-ivar2 dump: ;m
;class

test-init t

T{ t dump: -> 55 100 55 0 55 100 55 0 0 0 55 100 55 0 }T

cr .( testing rec{  }rec class_as> )

:class testrec0 <super object 
  rec{ var x }rec \ test case when first ivar is a record (offset=0)
  :m init: 44 x ! ;m
  :m @: ( -- n ) x @: ;m
  \ :m @: ;m  \ will error => method redefined in same class
;class


testrec0 x0

T{ x0 @: -> 44 }T

:class testrec <super object 
  var x
  var yy
  rec{ var y
       var z
      }rec
  string s-ivar

 :m init: 33 y !  99 z !: ;m \ message to record ivar

 :m test1: ( -- y y z )
      y @ 
      y @: \ message to record ivar
      z class_as> var @:
     ;m
 :m test2: ( -- addr len )
      s" Hello" s-ivar !:
      s-ivar @:
     ;m

;class

testrec tr

: test tr test1: ;

T{ test -> 33 33 99 }T

T{ tr test2: s" Hello" COMPARE -> 0 }T

cr .( testing object-list )

object-list aa

   ' var       aa add:
10 ' xstring   aa add:
   ' var       aa add:
   ' rectangle aa add:

\      string s
\      s         aa addObj: \ no longer a valid way to add object
   ' string    aa add:

s" Hello" aa obj: !:  


T{ 0 aa at: classname:  s" VAR"       COMPARE -> 0 }T

T{ 1 aa at: classname:  s" XSTRING"   COMPARE -> 0 }T

T{ 2 aa at: classname:  s" VAR"       COMPARE -> 0 }T

T{ 3 aa at: classname:  s" RECTANGLE" COMPARE -> 0 }T

T{ 4 aa at: classname:  s" STRING"    COMPARE -> 0 }T


T{ aa obj: @:  s" Hello" COMPARE -> 0 }T \ get last object added to list

aa free:



object-list list
string+ s-input
string+ s-output


: initialize \ load text into input string
  s"   Now  is   the time" s-input !: ;

   
: extract-words \ extract each word into a list of string objects
  BEGIN
   bl s-input word:
  WHILE
   ['] string list add:
    s-input @sub: ( addr len ) list obj: ( addr len ^string-obj ) !:
  REPEAT
  ['] string list add: \ a string for the last word
  \ now grab last word
  s-input end: @  s-input rem: +  s-input end: !
  s-input @sub: list obj: !:
  ;

 
: csv-format \ format the output into a single string object
  pad 0 s-output new:
  BEGIN
    list each:
  WHILE
    @: ( addr len ) s-output add: \ build output
    [char] , s-output +:
  REPEAT
   \ optionally replace last "," with a "cr"
    \ 13 ( CR ) s-output size: 1- s-output to:
    ;


: cleanup \ free the heap memory
  list free:
  s-input free:
  s-output free: ;



TRUE TO case-sensitive?
initialize
extract-words
csv-format
T{ s-output @:  s" Now,is,the,time," COMPARE -> 0 }T

cleanup


FALSE TO case-sensitive?
initialize
extract-words
csv-format

T{ s-output @:  s" Now,is,the,time," COMPARE -> 0 }T

cleanup

cr .( Single Inheritance Tests are Complete )

:class charc super{ object }
  1 bytes data
 :m !: ( n -- ) data c! ;m
 :m @: ( -- n ) data c@ ;m
 :m late: ( -- n ) [self] @: ;m
;class

cr .( testing MI ITRAV edge condition )

:class varzz super{ object }
  3 bytes filler
  charc cc
  cell bytes data
 :m !: ( n -- ) data ! ;m
 :m @: ( -- n ) data @ ;m
 :m init: 888 self !: 11 cc !: ;m
 :m late: ( -- n ) cc late: ;m
;class

varzz zz2
T{ zz2 @: -> 888 }T
 \ Last Revision: 11/22/11
 \ tests for proper header creation in ITRAV for ivar cc
T{ zz2 late: -> 11 }T

:class var888 super{ object }
  cell bytes data
 :m !: ( n -- ) data ! ;m
 :m @: ( -- n ) data @ ;m
 :m init: 888 self !: ;m
 :m p: data @ . ;m
;class


cr .( testing 3 MI superclasses )

:class test2 super{ var888 string dicArray }
   5 ordered-col oc
:m getstring: ( -- addr len ) super> string @: ;m
:m add: ( n -- ) oc add: ;m
:m dumpoc: ( -- ... ) begin oc each: while repeat ;m
;class

3 test2 t2

10 1 t2 to: \ dicArray
20 2 t2 to: \ dicArray

s" hello" t2 new: \ string

89 t2 !: \ var888

100 t2 add: \ ordered-col ivar
200 t2 add:
300 t2 add:

T{ t2 @: -> 89 }T  \ var888
T{ t2 getstring: s" hello" COMPARE -> 0 }T \ string
T{ 1 t2 at: -> 10 }T \ dicArray
T{ 2 t2 at: -> 20 }T \ dicArray
T{ t2 dumpoc: -> 100 200 300 }T \ ordered-col ivar

: u1 t2 @: ;
: u2 t2 getstring: ;
: u3 1 t2 at: ;
: u4 t2 dumpoc: ;
T{ u1 -> 89 }T
T{ u2 s" hello" COMPARE -> 0 }T
T{ u3 -> 10 }T
T{ u4 -> 100 200 300 }T

cr .( testing indexed MI object as embedded-object-as-ivar )

:class test3 <super var888
  10 test2 ivar2

:m new: ( addr len -- ) ivar2 new: ;m
:m getstring: ( -- addr len ) ivar2 getstring: ;m
:m add: ivar2 add: ;m
:m dumpoc: ivar2 dumpoc: ;m
:m to: ( n idx -- ) ivar2 to: ;m
:m at: ( idx -- n ) ivar2 at: ;m
;class

test3 t3


4004 t3 !: \ var888 superclass

101 t3 add: \ ivar2 ordered-col
202 t3 add:
303 t3 add:
404 t3 add:
505 t3 add:

s" HELLO WORLD" t3 new: \ ivar2 string

11 0 t3 to: \ ivar2 dicarray
12 1 t3 to:
13 2 t3 to:
14 3 t3 to:
15 4 t3 to:
16 5 t3 to:
17 6 t3 to:
18 7 t3 to:
19 8 t3 to:


T{ t3 @: -> 4004 }T \ var888 superclass
T{ t3 dumpoc: -> 101 202 303 404 505 }T \ ivar2 ordered-col
T{ t3 getstring: s" HELLO WORLD" COMPARE -> 0 }T \ ivar2 string
T{ 0 t3 at: -> 11 }T \ ivar2 dicarray
T{ 1 t3 at: -> 12 }T
T{ 2 t3 at: -> 13 }T
T{ 3 t3 at: -> 14 }T
T{ 4 t3 at: -> 15 }T
T{ 5 t3 at: -> 16 }T
T{ 6 t3 at: -> 17 }T
T{ 7 t3 at: -> 18 }T
T{ 8 t3 at: -> 19 }T

: k0 t3 @: ;
: k1 t3 dumpoc: ;
: k2 t3 getstring: ;
: k3 3 t3 at: ;

T{ k0 -> 4004 }T
T{ k1 -> 101 202 303 404 505 }T
T{ k2 s" HELLO WORLD" COMPARE -> 0 }T
T{ k3 -> 14 }T


:class sup1 super{ object }
 var888 v1a
 var888 v1char
 var888 v1b
:m init: 1 v1a !:  ( v1b init: ) 10 v1char !: ;m
:m @a1: ( -- n ) v1a @: ;m
:m @c1: ( -- n ) v1char @:  ;m
:m @b1: ( -- n ) v1b @:  ;m
;class


sup1 s1


T{ s1 @a1: -> 1 }T
T{ s1 @b1: -> 888 }T
T{ s1 @c1: -> 10 }T

:class sup2  super{ object }
 var888 v2a
 var888 v2b
:m init: 3 v2a !:  4 v2b !: ;m
:m @a2: v2a @:  ;m
:m @b2: v2b @:  ;m
;class

:class sup3 super{ object }
 var888 v3a
 var888 v3b
:m init: 5 v3a !:  6 v3b !: ;m
:m @a3: ( -- n ) v3a @:  ;m
:m @b3: ( -- n ) v3b @:  ;m
;class

makeselect d:

:class sup4 super{ sup1 sup2 } 
 var888 v4a 
 var888 v4b
 sup3 s3
:m late: [self] d: ;m
:m init:
     7 v4a !:
 ;m
:m ba: super init: ;m
:m @a4: ( -- n ) v4a @:  ;m
:m @b4: ( -- n ) v4b @:  ;m
:m d: ( -- n n )
 s3 @a3:
 s3 @b3:
 ;m 
;class

sup4 s4


makeselect frog:

:class sup5 super{ object }
 var888 x
 var888 y
:m !: ( n -- ) x !: ;m
:m @: ( -- n ) x @: ;m
:m !y: ( n -- ) y !: ;m
:m @y: ( -- n ) y @: ;m
:m init: 1 self !:  2 y !: ;m
:m croak: [self] frog: ;m  
:m sup5: ( -- n ) y @: ;m
;class


:class sup6 super{ object }
 var888 x
 var888 y
:m !: ( n -- ) x !: ;m
:m @: ( -- n ) x @: ;m
:m !y: ( n -- ) y !: ;m
:m @y: ( -- n ) y @: ;m
:m init: 3 self !:  4 y !: ;m
;class



:class sup7a super{ object }
 var888 x
 var888 y
 var888 z
 :m foo: ." foo: in class sup7a" ;m
 :m frog: ( -- addr len ) s" RIBBET" ;m
;class


:class sup7 super{ sup7a }
 var888 x7
 var888 y7
:m !: ( n -- ) x7 !: ;m
:m @: ( -- n ) x7 @: ;m
:m !y: ( n -- ) y7 !: ;m
:m @y: ( -- n ) y7 @: ;m
:m init: 5 self !:  6 y7 !:  999 z !: ;m
;class


cr .( testing 4 superclasses, with nested superclasses )
:class sup super{ sup5 sup4 sup6 sup7 }
 var888 x9
 var888 y9
:m !: ( n -- ) x9 !: ;m
:m @: ( -- n ) x9 @: ;m
:m !y: ( n -- ) y9 !: ;m
:m @y: ( -- n ) y9 @: ;m
:m init: 7 self !: 8 y9 !: ;m
:m !1: ( n -- ) super> sup5 !: ;m
:m @1: ( -- n ) super> sup5 @: ;m
:m @11: ( -- n ) super @: ;m 
 :m @0: ( -- n ) self @: ;m 
 :m aa: ( -- n ) z @:  ;m 
 :m bb: ( -- n ) super> sup6 @y: ;m
;class

sup s

T{ s @: -> 7 }T
T{ s @y: -> 8 }T
T{ s bb: -> 4 }T

: f1 s @: ;
: f2 s @y: ;
: f3 s bb: ;
T{ f1 -> 7 }T
T{ f2 -> 8 }T
T{ f3 -> 4 }T
s value sss
: f4 sss @: ;
: f5 sss @y: ;
: f6 sss bb: ;
T{ f4 -> 7 }T
T{ f5 -> 8 }T
T{ f6 -> 4 }T

\ Croak: method is in class sup5, which calls frog:.
\ Frog: is defined in class sup7a.
\ Class sup7a is the superclass for class sup7.
\ Classes sup5 and sup7 are multiply inherited by class sup.
\ Amazingly sending a croak: message to a sup object results in a "RIBBET".
T{ s croak: s" RIBBET" COMPARE -> 0 }T
T{ s @c1: -> 10 }T
T{ s @y: -> 8 }T
T{ s bb: -> 4 }T
T{ s late:  -> 5 6 }T

: t s late: ; 
                
T{ t -> 5 6 }T
T{ s @a4: -> 7 }T
T{ s d: -> 5 6 }T

: run-sup
  s @:
  s @y:
  s @1:
  s @11:
  s @0:
  s aa:
  s bb:
  ;

T{ run-sup -> 7 8 1 1 7 999 4 }T


:class sup8 super{ object }
 var888 v1a
:m @a2: ;m
:m init: 1 v1a !: ;m
:m @a1: ( -- n ) v1a @:  ;m
:m @a2late: ( -- n ) [self] @a2: ;m
;class


:class sup9 super{ object }
 var888 v2a
 var888 v2b
 :m d2: ;m
 :m late:  [self] @a1: ;m 
 :m late2:  [self] @a2: ;m \ @a2: is null in sup1
 :m late3:  [self] @a3: ;m
 :m lated2: [self] d2: ;m
:m init: 3 v2a !: 4 v2b !:  ;m
:m @a2: ( -- n ) v2a @:  ;m
:m @b2: ( -- n ) v2b @:  ;m
;class

cr .( testing MI late-bound messages across non-related superclasses )

:class supx super{ sup8 sup9 } 
 var888 v3a
 :m late1: [self] d: ;m  \ d: is already defined
 :m init: 5 v3a !: 
 ;m
 :m @a3: v3a @:  ;m
:m d: 
  v1a @ 
  v2a  @ 
  v2b @
  v3a  @ 
 ;m
:m @a1: v1a @ ;m \ must define this here because
                 \ it is otherwise undefined ( = null)
 :m d2: 
  self @a1:
  super> sup9 @a2:
  super> sup9 @b2:
  [self] @a3:
 ;m 

 :m d3:
  [self] @a2:   
 ;m 
 :m d4:
  [self] @a3: 
 ;m 
;class

supx sx

T{ sx late1: -> 1 3 4 5 }T
T{ sx d2: -> 1 3 4 5 }T
T{ sx lated2: -> 1 3 4 5 }T
T{ sx d3: ->  }T
T{ sx d4: -> 5 }T
T{ sx late: -> 1 }T
T{ sx late3: -> 5 }T

: f sx d2: ;

T{ f -> 1 3 4 5 }T

CR .( test SELF edge condition )

:class varxx super{ object }
  cell bytes data
:m @: ( -- n ) data @ ;m
:m !: ( n -- ) data ! ;m
:m p: self @: . ;m
;class

:class sup1xx super{ object }
  cell bytes data
:m @1: ( -- n ) data @ ;m
:m !1: ( n -- ) data ! ;m
;class


:class testxx super{ varxx sup1xx }
  cell bytes data
:m @s: ( -- n ) data @ ;m
:m !s: ( n -- ) data ! ;m
:m t: ( -- n ) self @1:  ;m \ edge condition
;class

testxx tx
46 tx !1:

T{ tx t: -> 46 }T


CR .( testing SUPER edge condition )

:class varz super{ object }
  cell bytes data11
:m @1: ( -- n ) data11 @ ;m
:m !1: ( n -- ) data11 ! ;m
:m p: self @1: . ;m
;class

:class sup1z super{ object }
  var x7
  cell bytes data22
:m @: ( -- n ) data22 @ ;m
:m !: ( n -- ) data22 ! ;m
;class

:class testz super{ varz sup1z }
  cell bytes data
:m @: ( -- n ) data @ ;m
:m !: ( n -- ) data ! ;m
:m _init: 1 data !  2 data11 !  3 data22 ! ;m
:m d: self @:  ;m
:m d1: super @:  ;m
;class

testz tz
tz _init:

T{ tz d: -> 1 }T
T{ tz d1: -> 3 }T

CR .( Multiple Inheritance Torture Test is Complete )

CR .( testing dot parser )

:class int: <super object
  cell bytes data
:m !: ( n -- ) data ! ;m
:m @: ( -- n ) data @ ;m
;class

:class point: <super object
   int: y0
   int: x0
:m !: ( x y -- ) y0 ! x0 ! ;m
:m @: ( -- x y ) x0 @ y0 @ ;m
;class

:class line: <super object
   point: p1
   point: p2
:m !: ( x1 y1 x2 y2 -- ) p2 !: p1 !: ;m
:m @: ( -- x1 y1 x2 y2 ) p1 @: p2 @: ;m
;class

line: MyLine
10 20 30 40 MyLine !:

T{ .. MyLine.p1.y0 @: -> 20 }T
T{ .. MyLine.p2.y0 @: -> 40 }T
: t .. MyLine.p1.y0 @: ;
T{ t -> 20 }T

cr .( DotParseAns tests complete )


cr .( Testing 2-dimension arrays )

: transpose ( -- array0 array1 )
  2 3 dimension heap> 2-array
  3 2 dimension heap> 2-array locals| a1 a0 |
  
  2 0 do
    3 0 do i 1+ j 2 + * j i a0 to: loop
  loop
  a0 p: \ print original matrix
  
  2 0 do
    3 0 do j i a0 at:   i j a1 to: loop
  loop
  cr a1 p: \ print transposed
  
  a0  a1  ;

cr .( transpose 2-dim array )

transpose
value a1{{
value a0{{

: }}@ ( ^obj row col -- elem{ r c } ) \ word that fetches 2-D array element contents
  rot at: ;

T{  a0{{ 0 0 }}@ a0{{ 0 1 }}@ a0{{ 0 2 }}@  -> 2 4 6 }T
T{  a0{{ 1 0 }}@ a0{{ 1 1 }}@ a0{{ 1 2 }}@  -> 3 6 9 }T
T{  a1{{ 0 0 }}@ a1{{ 1 0 }}@ a1{{ 2 0 }}@  -> 2 4 6 }T
T{  a1{{ 0 1 }}@ a1{{ 1 1 }}@ a1{{ 2 1 }}@  -> 3 6 9 }T
 
a0{{ <free
a1{{ <free

[undefined] about-win32forth [if]

cr .( Testing Binary Tree - With Recursion )

btree b
' emit b iv key-display-xt !
' display-char b iv info-displ-xt !

cr .( insert t d e r a )
char t dup b insert:
char d dup b insert:
char e dup b insert:
char r dup b insert:
char a dup b insert:

cr .( b .nodes: )  b .nodes: 
\ t(116) d(100) a(97) e(101) r(114) 

cr .( b balance: b .nodes: ) b balance: b .nodes: 
\ e(101) d(100) a(97) r(114) t(116) 

cr .( char e b delete: b .nodes: )
T{ char e b delete: -> -1 }T
 b .nodes: 
\ r(114) d(100) a(97) t(116) 

cr .( b .sorted: )  b .sorted: 
\ adrt

b free:


[undefined] noop [if] : noop ; [then]
' noop b iv key-display-xt !
' drop b iv info-displ-xt !

char t dup b insert:
char d dup b insert:
char e dup b insert:
char r dup b insert:
char a dup b insert:

T{ b .nodes: -> 116 100 97 101 114 }T
T{ b balance: b .nodes: -> 101 100 97 114 116 }T
T{ char e b delete: -> -1 }T
T{ b .nodes: -> 114 100 97 116 }T
T{ b .sorted: -> 97 100 114 116 }T

b free:

[then]
cr cr .( All Testing Completed )
