\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.

\ Feb 8, 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com
\ require <super object


DECIMAL

: ?? ( n n -- ) <> abort" ?? error!" ;

[defined] floats [if]
: f<> ( R: r r -- flag ) f- f0= 0= ;
: f?? ( R: r r -- ) f<> abort" f?? error!" ;
[then]


cr .( Test Basic Objects and Messaging )

33 int x
x :@ 33 ??



cr .( testing interpret late bind ) 

x value y
36 y :!
y :@ 36 ??


cr .( testing compile late bind ) 

: test 40 y :! y :@ ;
test 40 ??

cr .( Verify mixing message sends to public objects and ivars in a method )
66 int x1 
77 int x2 

:class int2 <super int
  :m get self :@ x1 :@ self :@ x2 :@ ;m
;class

88 int2 v2  


v2 get 77 ?? 88 ?? 66 ?? 88 ??
 

cr .( testing array ) 

5 array a

a :size 0 ??
77 a :add
 3 a :add
a :size 2 ??

: test 1 a :at ;
test 3 ??


cr .( testing :each and heap> ) 

45 a :add

: test begin a :each while  repeat ;

test 45 ?? 3 ?? 77 ?? 


: v heap> int ;

0 v 0 a :to
1 v 1 a :to
2 v 2 a :to


: test2 begin a :each while :@ repeat ;

: test4 begin a :each while <free repeat ; test4 



cr .( testing array sort )

>array value a
  5 a :add
  3 a :add
 33 a :add
 22 a :add
333 a :add
 
a :sort
0 a :at 3 ??
1 a :at 5 ??
2 a :at 22 ??
3 a :at 33 ??
4 a :at 333 ??

a <free

[defined] floats [if]
cr .( testing fp-array sort )


>farray to a
  5e a :add
  3e a :add
 33e a :add
 22e a :add
333e a :add

a :sort
0 a :at 3e f??
1 a :at 5e f??
2 a :at 22e f??
3 a :at 33e f??
4 a :at 333e f??
a <free
 
[else] cr .( Warning FP not loaded so not tested) cr
[then]


cr .( testing string )

s" Now is" 15 string s 
s"  the time" s :add 

\ : go s" bye" s :! ; 
\ go ok
\ s :. byeok


s :@  s" Now is the time" compare 0 ??


s" Now is the time for all" dup string s2

s"  all" s2 :search -1 ??

s2 :delete  
s"  all" s2 :search 0 ??

s2 :reset  
s"  time" s2 :search -1 ??
s2 :delete  
s2 :@  s" Now is the for" compare 0 ??
 

s" Now is the time" s :!



s :selectAll s :@sub  s" Now is the time" compare 0 ??
s" Now is the time" s := -1 ??
s" Now is THE time" s :=CI -1 ??

s" Now is THE time" s :selectAll s :=subCI TRUE ??

s" Now is THE time" s :selectAll s :=sub FALSE ??




s :reset
s" THE" s :search FALSE ??

s :reset
s" THE" s :searchCI TRUE ??
 


cr .( testing >string :replall )

s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" >string value dot$

s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add 
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add
s" now.is.the.time.for.all.good.men.to.come.to.the.aid.of.their.country" dot$ :add

s" ." dup string s1
s"  IV " dup string s2

: test s1 :@ s2 :@ dot$ :replall ; 

test 


dot$ :size 2373 ??
dot$ :start @ 0 ??
dot$ :end @ 0 ??

dot$ <free


cr .( testing embedded objects )

:class point <super object
  cell bytes x
  cell bytes y
  :m show: ( -- x y ) x @  y @  ;m
  :m dot: ( -- x y ) self show: ;m \ must late bind to self for demo
  :m :init 0 x !  0 y ! ;m
;class

:class rectangle <super object  
  point ul
  point lr
  :m :init ul :init lr :init ;m
  :m show: ( -- x1 y1 x2 y2 ) ul dot:  lr dot: ;m
  :m dot: ( -- x1 y1 x2 y2 )  self show: ;m
;class


rectangle r

r dot: 0 ?? 0 ?? 0 ?? 0 ??
 

cr .( testing open recursion )

:class label-point <super point
  :m show: ( -- x+1 y+1 ) x @ 1+  y @ 1+ ;m
;class


label-point poo

poo dot: 1 ?? 1 ??


[defined] floats [if]
cr .( testing class farray )

6 farray f 

6e f :add
88e f :add
f :each  -1 ?? 6e f??
f :each -1 ?? 88e f??
f :each 0 ??

f :each  -1 ?? 6e f??
f :each -1 ?? 88e f??
f :each 0 ??

[then]


[defined] begin-structure [if]
cr .( testing structures in classes )



 begin-structure point'
   1 cells +field p.x 
   1 cells +field p.y
 end-structure
 
 begin-structure rectangle' 
   point' +field r.ul
   point' +field r.lr 
 end-structure


 
:class rectangle-struct <super object 
   rectangle' bytes rect
   :m addr: ( -- addr ) rect ;m
   :m :init 0 rect r.ul p.x !
            0 rect r.ul p.y !
            0 rect r.lr p.x !
            0 rect r.lr p.y ! ;m
   :m show: ( -- x1 y1 x2 y2 )
      rect r.ul p.x @
      rect r.ul p.y @
      rect r.lr p.x @
      rect r.lr p.y @ ;m

;class 

 
rectangle-struct t1

cr t1 addr: r.ul p.x . \ 1236932 ok
cr t1 addr: r.ul p.y . \ 1236936 ok
cr t1 addr: r.lr p.x . \ 1236940 ok
cr t1 addr: r.lr p.y . \ 1236944 ok
cr here . \ 1236948 ok
cr

888 t1 addr: r.lr p.y !
t1 show: 888 ?? 0 ?? 0 ?? 0 ??
[then]



cr .( testing array object as instance variable )

:class indexed-test <super object  
  cell bytes x
  array c
  cell bytes y
  :m :init 7 x !  99 y ! 5 c :init
      5 0 do i c :add loop ;m
  :m d: ( -- x c0 c1 c2 c3 c4 c5 y )
     x @ 5 0 do i c :at loop y @ ;m
;class

indexed-test t
 
t d: 99 ?? 4 ?? 3 ?? 2 ?? 1 ?? 0 ?? 7 ?? 



cr .( testing exit in a method )

:class int3 <super int
 :m exit: ( n1 -- 10 100 )
     begin
      1+ dup
      10 = if 100 exit then
     again ;m
;class

0 int3 v3
2 v3 exit: 100 ?? 10 ??

cr .( testing long string input )
\ checking used in VFX and MFonVFX
\ must be turned off for multi-whiles
[defined] checking [if] checking off [then]

: <text>  ( obj -- caddr u )
   >r
   begin
      refill
   while
      10 word count 2dup s" </text>" compare
   while
      r@ :add bl r@ :ch+
   repeat then 2drop r> drop
;

[defined] checking [if] checking on [then]

0 0 >string value ss3


ss3 <text>
Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod
tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim
veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea
commodo consequat. Duis aute irure dolor in reprehenderit in voluptate
velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint
occaecat cupidatat non proident, sunt in culpa qui officia deserunt
mollit anim id est laborum.
</text>


ss3 :size 446 ??

ss3 <free 



[defined] floats [if]
cr .( testing integer list i{ ... } )

i{ 0 9 1 8
7 6 5 4 3 2 } value b

5 b :at 6 ??

9 b :at 2 ??
b :size 10 ??

b <free


cr .( testing fp list f{ ... } )

f{ 23 89e 3.4 677777e20 1 } to b

0 b :at 23e f??

4 b :at 1e f??
b :sort

2 b :at 23e f??

b <free
 

cr .( testing object lists o{ ... } )

o{ 'dog' 'cat' } value f  


s" dog" 0 f :at := true ??



o{ 'the dog' 'cat in the hat' } to f

s" cat in the hat" 1 f :at := true ??

f <free 


o{ 1 'frog' 3.5e } to f

0 f :at :@  1 ??



s" frog" 1 f :at :@ compare 0  ?? 

2 f :at :@ 3.5e f??

f <free

o{ 'dog' { 1 { 3 4 5 } 2 } 'g' { 3e 4e 'cat' } } to f
f :. 

f <free 



[then]

 
cr .( Testing Hash-Table)

hash-table t 

8888 s" Now is the time." t :insert
45 s" witch" t :insert
88 s" goofy frog" t :insert 
99 s" dog" t :insert 
100 s" mama" t :insert 
101 s" boy-boy" t :insert 
509 s" 2nd amendment" t :insert
7 s" foo bar" t :insert 
601 s" Presidential" t :insert

s" mama" t :delete .
s" goofy frog" t :delete .


cr cr .( FMS2VT Tests Concluded Successfully)


