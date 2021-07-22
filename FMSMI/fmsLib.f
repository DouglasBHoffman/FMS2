\ 01/20/12 dbh
\ require object-list objects only be instantiated via add: method
\ added an example 2 dimensional array class
\ added an example balanced binary tree class

\ fixed bug in string+ insert: method
\ fixed string+ search: and CIsearch:
\ added cr# and class file
\ added replLast: method to string+
\ changed string+ word: method to be simpler and more consistent

\ string+ added skipChars: and use it in word:
\ fixed two cases of illegal locals| use in class string+
\ reworked class ptr
\ added set: method to class cellarray
\ changed map: method in class obj-list to do nothing if list
\    is empty (it was issuing an abort)
\ changed =: to =sub: inclass string+, changed action of
\    =: to compare the given text to the entire string
\ added !: method to classes string and string+
\ "<SUPER OBJECT" is now optional
\ limited string+ dump to 38 chars
\ fixed bug in string+ CIsearch:
\ added delete: method for ARRAY class 
\ fixed stack bug in search: method of string+
\ Added OBJECT-LIST class.
\ Added explicit zero init: method to VAR class.
\ Changed free: method of class PTR to 0 the ptr address.
\ STRING+ searches no longer modify the search-for text.
\ Corrected skipBlanks: method in class STRING+.


[DEFINED] macforth.picture
[IF] 13 
[ELSE] 10 
[THEN] constant cr# \ newline char

:class var 
  cell bytes data
 :m !: ( n -- ) data ! ;m
 :m +: ( n -- ) data +! ;m
 :m -: ( n -- ) negate data +! ;m
 :m @: ( -- n ) data @ ;m
 :m p:  data @ . ;m \ print self
;class


:class bool 
  1 bytes bdata
  :m set: -1 bdata c! ;m
  :m clear: 0 bdata c! ;m
  :m @: ( -- flag ) bdata c@ 255 = ;m \ will return 0 or -1
  :m p: self @: . ;m
;class



0 [IF]
SEQUENCE is a generic superclass for classes which have multiple items which
frequently need to be looked at in sequence.  At present the main function of
Sequence is to implement the EACH: method, which makes it very simple to
deal with each element.  The usage is

 BEGIN  <obj> each:  WHILE <elem> (do something with the element)  REPEAT

Sequence can be a superclass for any class which implements the
FIRST?: and NEXT?: methods.  The actual implementation details are quite
irrelevant, as long as these methods are supported.

[THEN]

makeSelect next?: 
makeSelect first?: 



:class sequence <super object
 bool each_started?
:m each:  \ ( -- <varies> T  |  -- F )
  each_started? c@
  IF \ Subsequent time in:
   [self] next?: \ next?: is declared as a selector but there is no method yet
   IF  true  ELSE  0 each_started? c!  false  THEN
  ELSE \ First time in:       
   [self] first?: \ first?: is declared as a selector but there is no method yet
      0= IF 0 exit THEN
   -1 each_started? c!
   true  \ Yes, we've got the 1st element
  THEN ;m
:m uneach: \ Use to terminate an EACH: loop before the end.
  each_started? clear: ;m  \ could have used   0 each_started? c!
;class



:class dicPtr <super var
  var size \ size, in bytes, of memory allotted/allocated
  :m size: ( -- n )  size @ ;m
 :m new:  ( size -- ) \ size in bytes
    DUP ALIGN HERE SWAP ALLOT  self !  size ! ;m
;class


:class ptr <super var
 var size \ size, in bytes, of memory allotted/allocated
 :m size: ( -- n )  size @ ;m
 :m free:
    self @ ?DUP IF FREE ?MEMERR 0 self ! THEN
        0 size ! ;m   \ 12/14/10 dbh
 :m new:  ( size -- ) \ size in bytes
    self free:
    DUP ALLOCATE ?MEMERR  self !   size !: ;m
 :m resize:  ( newsize -- ) \ newsize in bytes
    self @ OVER RESIZE ?MEMERR  self !  size !  ;m
;class



makeSelect ^elem:

\ cellArray is a generic metaclass, meant only for subclassing
:class cellArray <super sequence
  var current

 :m to: ( n idx -- ) [self] ^elem: ! ;m
 :m +to: ( n idx -- ) [self] ^elem: +! ;m
 :m at: ( idx -- n ) [self] ^elem: @ ;m
 :m p: [self] size: 0 ?DO cr I DUP . self at: . LOOP ;m
 :m fill:  ( n -- )  [self] size: 0 ?DO DUP I self to: LOOP DROP ;m

 :m set: ( <varies> cnt -- ) \ adds cnt items to array
     1- locals| cnt |
   \ example usage: 3 5 7 9 12  5 <myobj> set:
   0 cnt ?DO I self to: cnt 1- to cnt -1 +LOOP ;m

 :m first?: ( -- elem t | f )
    0 current !
    0 [self] at: true ;m
  
 :m next?:  ( -- elem t | f )
  1 current +:   current @  dup  [self] size: <
  IF [self] at: true
  ELSE drop false
  THEN ;m

;class




\ cell size 1-dimension array, not resizable, alloted in the dictionary
\ but could also be cast as a heap object using heap>
:class dicArray <super cellArray cell <indexed
 :m ^elem: ( idx -- addr ) ^elem ;m 
 :m size: ( -- #elems ) limit ;m
;class

\ cell size 1-dimension array, dynamically resizable, allocated in heap
:class array <super cellArray
  var #elems
  ptr ardata
 :m size: ( -- #elems )  #elems @ ;m
 :m new: ( #elems -- ) DUP  #elems ! CELLS ardata new: ;m
 :m resize: ( n -- ) DUP  #elems ! CELLS ardata resize: ;m
 :m free:  ardata free:
    0  #elems ! ;m

 :m ?idx: ( idx -- idx )
    dup 
    0 #elems @: \ idx idx 0 #elems
    within IF exit THEN true ABORT" Index out of range" ;m
fmsCheck? [IF]
 :m ^elem: ( idx -- addr ) self ?idx:  CELLS ardata @  + ;m
 [ELSE]
 :m ^elem: ( idx -- addr ) CELLS ardata @ + ;m
 [THEN]
 :m delete: ( idx -- ) \ delete elem at idx and shrink array by 1 cell
    dup 1+ #elems @ <>
    IF
     dup >r 1+ self ^elem: ( src)
           r@ self ^elem: ( dest) #elems @ r> - cells ( len) MOVE
    ELSE drop
    THEN
      #elems @ 1 - self resize:
    ;m

;class

\ 01/24/12 dbh  eliminate addObj: method.  Must only use add: method for adding
\ new objects.  This way we are assured that <free will work on all objects
\ in the list.
\ All list objects are allocated in the heap.
:class object-list <super array
  :m delete: ( idx -- ) \ delete obj at idx and shrink list by 1 cell
     dup self at: <free
     ( idx ) super delete: ;m

\   :m addObj: ( ^obj -- ) \ add any arbitrary object
\      ardata @ 0= IF 0 super new: THEN \ initialize ptr if necessary
\      super size: dup >r 1+  super resize:
\      r> self to: ;m
  :m add: ( class-xt -- )  \ use: ' or ['] classname myObject-list add:
     >body ( ^class ) (heapObj) 
     ardata @ 0= IF 0 super new: THEN \ initialize ptr if necessary
     super size: dup >r 1+  super resize:
     r> self to: ;m
fmsCheck? [IF]
   :m error?: self size: 0= ABORT" object-list is empty" ;m
[ELSE]
  :m error?: ;m
[THEN]
  :m obj: ( -- ^obj ) \ returns last object added to list
     self error?:
     self size: 1- self at: ;m
  :m map: ( xt -- ) \ apply xt to each object in the list
     \ self error?:
     self size: 0= IF drop exit THEN    \ 02/23/11 dbh  
       LOCALS| xt |
      BEGIN self each: WHILE xt execute REPEAT ;m
  :m free:
      ['] <free self map:
      super free: ;m

  :m p: ['] p: self map: ;m \ Yes, we can tick selectors with FMS.
  :m dump:
      self size: 0 ?DO cr i . i self at: classname: TYPE LOOP ;m
;class



\ dynamically resizable string, allocated in the heap
:class string <super ptr

 :m new: ( addr len -- )
    DUP super new: ( addr len ) self @ SWAP ( addr self len ) MOVE ;m
 :m add: ( addr len -- ) \ add text to end of string
   DUP ( addr-src len len )
    size @ DUP >R + self resize:  \ addr-src len
   self @ R> + ( addr-src len dest) SWAP MOVE ;m
 :m @: ( -- addr len ) self @  size @ ;m
 :m !: ( addr len -- ) self free: pad 0 self new: self add: ;m
 :m p: self @: TYPE ;m
 :m +: ( char -- ) \ add char to end of string
     size @ 1+ self resize:   self @: + 1- c! ;m
;class

true value case-sensitive? \ used for searches in string+ objects

:class string+ <super string
\ We use the TextEdit metaphor of "selected" text with a starting position
\ for the selection START and an ending position END to define substrings
\ within the string object.  The positions are
\ zero-based and there will always be one more selection position than
\ the number of chars in the entire string.  For example:
0 [if]

0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0
 h e l l o   w o r l d
            S
                      E
start=6  end=11  size=11

In the above START=6 and END=11 so the text "world" is selected.
So in out TextEdit metaphor we can think of "world" as being hilighted.
We can say that the "w" belongs to position 6.  The SIZE of the
text is 11 chars.
There are 12 possible positions for both START and END ( 0 thru 11).
The last character in the string belongs to position 10.
It would not make sense for END to be in front of START, though
START and END could well be, and often are, the same value.
[then]
  var start  \ selection start
  var end    \ selection end
  1 bytes theChar \ used for char searches
 :m reset: 0 start !  0 end !  ;m
 :m new: ( addr len -- ) super new:  self reset: ;m
 :m !: ( addr len -- ) super !:  self reset: ;m
 :m start: ( -- pos-addr ) start ;m
 :m end: ( -- len-addr ) end ;m
 \ the number of chars remaining after the selection
 :m rem: ( -- remainder ) size @ end @ - ;m
 :m 1st: ( -- char ) \ return first char of substring 
    self @ start @ + ( addr ) c@ ;m
 :m last: ( -- char ) \ return last char of substring 
    self @ end @ + 1- ( addr ) c@ ;m
      
fmsCheck? [IF]
 :m ?idx: ( idx -- idx )
     dup 0 size @ 
     WITHIN 0= IF TRUE ABORT" string+ index out of range" THEN ;m 
[ELSE]
 :m ?idx: ;m
[THEN]
\ at: and to: indexes refer to the entire string
 :m at: ( idx -- char )
     self ?idx:
     self @ + c@ ;m
 :m to: ( char idx -- )
     self ?idx:
     self @ + c! ;m
 :m upper: \ converts entire string to upper case
      self @: to-upper ;m

 :m @sub: ( -- addr len ) \ fetch substring
    self @ start @ + ( addr ) end @ start @ - ;m

 :m selectAll: \ select entire string
    0 start ! size @ end ! ;m

\ compare addr1 len1 to the current *substring*
 :m =sub: ( addr1 len1 -- f ) \ observes case setting; true if equal, false if not
    DUP end @ start @ - <> IF 2drop FALSE EXIT THEN  \ get out early if length mismatch
    0 0  locals| str1 selfStrCopy len1 addr1 |
    case-sensitive?
    IF addr1 len1
       self @sub: COMPARE 0=
    ELSE
    self heap: self heap: to str1 to selfStrCopy
    self @sub: selfStrCopy new: \ make a temporary duplicate string object in the heap
    addr1 len1 str1 new: \ make a temporary duplicate string object in the heap
    selfStrCopy upper:   str1 upper: \ make both string copies uppercase
    selfStrCopy @:  str1 @: COMPARE 0=
    selfStrCopy <free str1 <free
    THEN
    ;m

 \ compare addr1 len1 to the entire string
 :m =: ( addr1 len1 -- true | false ) \ observes case setting; true if equal, false if not
     self selectAll:
     self =sub:
     ;m

\ 12/16/10 dbh  CIsearch: no longer modifies the search-for text addr1 len1
\ case insensitive search
\ Do not invoke CIsearch: directly.  Rely on the case-sensitive? switch.
 :m CIsearch: ( addr1 len1 -- true | false )
    self heap: self heap: locals| str1 selfStrCopy len1 addr1 |
    self @: selfStrCopy new: \ make a temporary duplicate string object in the heap
    start @ selfStrCopy start: !   end @ selfStrCopy end: !
    addr1 len1 str1 new: \ make a temporary duplicate string object in the heap
    str1 @: TO len1 TO addr1
    selfStrCopy upper:   str1 upper: \ make both string copies uppercase
    
        selfStrCopy @ selfStrCopy end: @ + ( start-addr) selfStrCopy rem: ( len )
            addr1 len1 search \ true    \ 01/23/11 dbh  
        IF \ found
          ( u3 ) drop
          ( c-addr3 ) selfStrCopy @ - dup len1 + end ! start !
          true
      \ ELSE  nip nip false
        ELSE  2drop false
        THEN
        str1 <free selfStrCopy <free \ dispose the temp strings
   ;m


 :m search: ( addr len -- true | false )
     locals| len addr |
     addr len
    \ first do rationality check
    \ return false if len to find is greater than remainder
      dup self rem: > IF 2drop false exit THEN
    case-sensitive?
    IF 2drop \ do case sensitive search
      self @ end @ + ( start-addr) self rem: ( len)  addr len search
      IF \ found
        ( u3 ) drop
        ( c-addr3 ) self @ - dup len + end ! start !
        true
      \ ELSE  nip nip false
      ELSE  2drop false
      THEN
    ELSE \ do case insensitive search
       self CIsearch:
    THEN
    ;m

:m chsearch: ( char -- flag )
   theChar c!  theChar 1 self search: ;m

 :m delete:  \ deletes the substring defined by START and END
             \ leaves START at the same place, END is set to START
     end @  start @ - 1 < IF exit THEN
     self @ end @ +   \ src 
     self @ start @ + \ src dest
     self rem: \ src dest cnt
     move
    size @  end @ start @ - -  self resize:
    start @ end !
     ;m

\ inserts text starting at END, START and END are moved to end of inserted text
 :m insert: \ { addr len -- }
    locals| len addr |
    size @ len + self resize:
\    self @ end @ + dup ( src src ) len + ( dest ) self rem: ( cnt ) MOVE
\ 9-17-11 dbh fixed bug
    self @ end @ + dup ( src src ) len + ( dest ) self rem: len - ( cnt ) MOVE
    
    addr ( src ) self @ end @ + ( dest ) len  MOVE
    end @ len + dup start ! end ! ;m

\ inserts char at END, START and END are moved to just past inserted char
 :m chinsert: ( c -- )
    theChar c!  theChar 1 self insert: ;m 
 
\ replace selected text, if any, with given text
 :m replace: ( addr len -- )
     self delete: self insert: ;m

\ Search for text1 starting at END.
\ If found replace with text2.
\ Success flag is returned.
 :m sch&repl:  \ { addr1 len1 addr2 len2 -- flag }
    locals| len2 addr2 len1 addr1 |
    addr1 len1 self search: dup
    IF addr2 len2 self replace: THEN ;m

\ Reset self and replaces all occurrences of (addr1 len1) by (addr2 len2)
\ in the WHOLE of self.  Self is lastly reset again.
 :m replall: \ { addr1 len1 addr2 len2 -- }
    locals| len2 addr2 len1 addr1 |
 self reset:
 BEGIN
   addr1 len1 self search:
 WHILE
  addr2 len2 self replace:
 REPEAT
 self reset:
;m
    

 :m d:  \ formatted dump of string for debugging
   cr ."                     1                   2                   3                   4"
   cr ." 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0"
   cr  self size: 38 min 0 ?DO space i self at: emit LOOP
   cr start @ 40 min 2* spaces [char] S emit
   cr end @ 40 min 2* spaces [char] E emit
   cr ." start= " start p:  ."  end= " end p:  ."  rem= " self rem: . ."  size= " size p:
      ."   case-sensitive?= " case-sensitive? .
 ;m

:m skipBlanks: \ skip leading blanks, tabs, etc
    BEGIN
      end @ size @ = IF exit THEN
      end @ self at: 33 <  
    WHILE
      1 end +!
    REPEAT
     end @ start ! ;m

:m skipChars: ( char -- )
    locals| c |
    BEGIN
      end @ size @ = IF exit THEN
    
    end @ self at:
    case-sensitive? 0=
    IF dup lowerCase? IF 32 - THEN
    THEN
     c =
    WHILE
      1 end +!
    REPEAT
     end @ start ! ;m

:m CIword: \ { c -- flag }
    dup ( c c ) lowerCase? IF  32 - THEN
    dup self skipChars:
    self @ start @ + \ c addr
    self rem: \ c addr len
    over    \ c addr len addr
    +       \ c addr addr+len
    swap    \ c addr+len addr
    ?DO dup I C@ dup lowerCase? IF 32 - THEN
         = IF I self @ - end ! UNLOOP drop TRUE EXIT THEN LOOP
    drop FALSE
    ;m      

\ Parse the string for text ending with char c.
\ Leading blanks are skipped.
\ Use @sub: to retrieve the substring if true is returned.
\ Subsequent use of word: will automatically advance just past
\ the last "hit" and continue to skip leading blanks.
:m word: \ { c -- flag }
    case-sensitive? 0= IF ( c ) self CIword: exit THEN
    dup self skipChars:
    self @ start @ + \ c addr
    self rem: \ c addr len
    over    \ c addr len addr
    +       \ c addr addr+len
    swap    \ c addr+len addr
    ?DO dup I C@ = IF I self @ - end ! UNLOOP drop TRUE EXIT THEN LOOP
    drop FALSE
    ;m      

:m replLast: ( char -- ) \ replace last char in string with given char
   self @: + 1- c! ;m

;class


\ a (restricted resizeable) string that is alloted in the dictionary
\ although it could still be cast as a HEAP> object
:class xstring <super object 1 <indexed
  var current \ current size

:m @: ( -- addr len )
    idxBase  current @ ;m
:m !: \ { addr len  -- }
     locals| len addr |
     len limit > abort" xstring !: not enough room"
     addr ( src ) idxBase ( dest ) len MOVE
     len current ! ;m
:m add: \ { addr len -- }
     locals| len addr |
   current @ len + limit > abort" xstring add: not enough room"
   addr ( src ) idxBase current @ + ( dest ) len MOVE
   len current +! ;m
:m +: ( char -- )
     current @ 1+ limit > abort" xstring +: not enough room"
     idxBase current @ + c!
     1 current +! ;m
:m p: ( -- ) self @: TYPE ;m
:m size: ( -- u )  current @ ;m
;class


:class ordered-col  <super dicarray
 var cursize    \ # elements in list
 
:m size: \ ( -- cursize )  Returns #elements currently in list
  cursize @  ;m

:m clear:
   0 super fill:  0 cursize ! ;m

:m add:  \ ( elem -- )  add elem to end of list
  cursize @ dup limit  =  ABORT" Ordered-col full"
  ( cursize ) super to:   1 cursize +:  ;m

:m last:  \ ( -- last )  Returns contents of end of list
   cursize @ dup 0= ABORT" Empty ordered-col"
    1-  super at:  ;m

:m delete:  \ ( indx  -- ) \ Removes the element at indx
     0 locals| cnt indx |
     cursize @  indx -  1-  to cnt
     cnt 0<  IF true ABORT" Can't delete: empty ordered-col"  THEN
     -1 cursize +:
     cnt  0= IF exit THEN
     indx  super ^elem: dup >r
     CELL+  r>  cnt CELL *  move ;m

\ Finds a value in a collection.
:m search:  \ { val -- indx T  | -- F }
    locals| val |
    self size: 0 ?DO i self at: val = 
        IF i unloop  true exit THEN
        LOOP false ;m

 :m map: \ { xt -- } \ apply xt to each element in the list
    locals| xt |
    BEGIN
      self each:
    WHILE
      xt execute
    REPEAT ;m

;class


\ ordered-col+ is modeled after the Smalltalk implementation
:class ordered-col+ <super ordered-col

:m first:  ( -- n )
 cursize @ 0= ABORT" Empty ordered-col"
 0 self at: ;m

:m addFirst: ( n -- ) \ adds n, makes n the first element in the array
 \ so add: is really an addLast:, but no need to change that
   cursize @  limit < 0=  ABORT" Ordered-col full" \ size check as for add: super
   cursize @ locals| idx |
   BEGIN
     idx 0>
   WHILE
     idx 1- dup to idx
     ( idx ) self at:  idx 1+ self to:
   REPEAT
 ( n ) 0 self to: \ place n at the begining
 1 cursize +: ;m  \ finally, increase current size by one

:m removeFirst: ( -- )
 0 super delete: ;m

:m set: ( <varies> cnt -- ) \ adds cnt items to collection
 \ example usage: 3 5 7 9 12  5 <myobj> set:
 0 ?DO self addFirst: LOOP ;m

:m sum: ( -- sum )
 0 BEGIN
  self each:
   WHILE
     +
   REPEAT ;m

:m max: ( -- max ) \ return maximum number in collection
     0 locals| max |
 BEGIN
  self each:
 WHILE
    dup max > IF to max ELSE drop THEN
 REPEAT max ;m

:m min: ( -- min ) \ return maximum number in collection
    self size: 2 < IF 1 < IF true ABORT" empty collection" THEN
                          0 self at: 
                   THEN
 1 self at: locals| min |  \ must start with something in min
 BEGIN
  self each:
 WHILE
    dup min < IF to min ELSE drop THEN
 REPEAT min ;m

:m removeAll: ( n -- ) \ remove all occurances of n from the list
    locals| n |
 BEGIN
  n self search:
 WHILE
  super delete:
 REPEAT ;m

:m occurrencesOf: ( n -- cnt ) \ number of times n is in collection
 0 locals| cnt n |
 BEGIN
  self each:
 WHILE
  n = IF cnt 1+ to cnt THEN
 REPEAT cnt ;m

:m conform: ( xt -- flag ) \ test if all elements meet condition
    locals| xt |
 BEGIN
  self each:
 WHILE
  xt execute ( flag ) 0= IF self uneach:  false exit THEN
 REPEAT true ;m

\ NOTE: for accept: reject: and collect: we return a new collection.  The original
\ collection is unchanged. This new collection returned
\ will be nameless and dynamically allocated in the heap.  Thus if you use one 
\ of these methods, the resulting collection must eventually get a <FREE.

:m accept: ( xt -- ^obj ) \ return new collection of elements that pass test
 self size:  self heap: locals| newCol xt |
 BEGIN
  self each:
 WHILE
  dup xt execute ( flag ) IF ( passed test) newCol add: ELSE drop THEN
 REPEAT newCol ;m

:m reject: ( xt -- ^obj ) \ return new collection of elements that fail test
 self size:  self heap: locals| newCol xt |
 BEGIN
  self each:
 WHILE
  dup xt execute ( flag ) IF ( passed test) drop ELSE ( failed test) newCol add: THEN
 REPEAT newCol ;m

:m collect: ( xt -- ^obj ) \ transform each element for a new collection
 self size:  self heap: locals| newCol xt |
 BEGIN
  self each:
 WHILE
  xt execute  newCol add:
 REPEAT newCol ;m

;class

[DEFINED] floats
[IF]
:class fp <super object
  1 floats  bytes rdata
:m !: ( F: r -- ) rdata f! ;m
:m @: ( F: -- r ) rdata f@ ;m
:m  +:  ( F: r -- ) rdata f@ f+ rdata f! ;m
:m  -:  ( F: r -- ) rdata f@ fswap f- rdata f! ;m
:m p: [self] @: f. ;m
;class
[THEN]

:class file <super object
   var ID
   bool open?
   string+ name
   var fam \ file access method

:m init: r/w fam ! ;m

:m open: ( "<filename>" -- ior )
   open? @: ABORT" file already open in open: attempt"
   name !:
   name @: fam @ OPEN-FILE
   SWAP ID !
   open? set:
   ;m

:m create: ( "<filename>" -- ior )
   2dup name !:
   fam @ CREATE-FILE
   SWAP ID !
   open? set:
   ;m

:m read: ( str-obj -- n ior ) \ n is actual bytes read
      locals| ^str |
   open? @: 0= ABORT" read: attempt file not open"
   ID @ FILE-SIZE
   ABORT" read: FILE-SIZE failed"
   ( ud ) d>s ^str class_as> ptr new:
   ^str @: ( addr len ) ID @ READ-FILE
   ;m

:m !pos: ( n -- )
   open? @: 0= ABORT" !pos: attempt when file not open"
   s>d ID @ REPOSITION-FILE
   ABORT" !pos: REPOSITION-FILE failed"
   ;m

:m @pos: ( -- n )
   open? @: 0= ABORT" @pos: attempt when file not open"
   ID @ FILE-POSITION 
   ABORT" @pos: FILE-POSITION failed"
   D>S ;m

:m write: ( addr len -- ior )
      locals| len addr |
   open? @: 0= ABORT" write: attempt when file not open"
   len s>d ID @ RESIZE-FILE 
   ABORT" write: RESIZE-FILE failed"
   ID @ FLUSH-FILE drop
   0 self !pos: \ start write at beginning of file
   addr len ID @ WRITE-FILE
   ;m

:m close: ( -- ior )
   open? @: 0= ABORT" close: attempt when file not open"
   ID @ CLOSE-FILE
   open? clear:
   name free:
   ;m

:m delete:  ( -- ior ) \ 05/13/11 dbh  untested
   name @: DELETE-FILE
   open? clear: 
   name free:
   ;m
   
;class

\ very basic 1-dim array class ( cell size elements)
:class 1-array <super object  cell <indexed
 :m to: ( n idx -- ) ^elem ! ;m
 :m at: ( idx -- n ) ^elem @ ;m
 :m size: ( -- n ) limit ;m
 :m p: limit 0 ?do cr i . i self at: . loop ;m
;class


\ support for a 2-dimension array class

0 value rowDim
0 value colDim

: dimension ( #rows #cols -- )
 to colDim to rowDim
 rowDim colDim * ;

\ Usage:   10 20 dimension 2-array myArray

:class 2-array <super object  cell <indexed
 var #ofRows
 var #ofCols
 var stride

:m init:
 colDim #ofCols !
 rowDim #ofRows !
 #ofCols @  cell * stride !
 ;m

:m check:  ( row# col# -- )
  #ofCols @ 1 -  > swap
  #ofRows @ 1 -  > or abort" 2-array indice(s) out of bounds." ;m

:m ^elem:  \ { row# col# -- addr }
     locals| col# row# |
 fmsCheck? IF row# col# self check: THEN
 idxbase stride @  row# * +  cell col# * +
 ;m

:m to: ( n row# col# -- )
  self ^elem: ! ;m

:m at: ( row# col# -- n )
 self ^elem: @  ;m

:m size: ( -- #ofRows #ofCols )
 #ofRows @ #ofCols @ ;m

:m p: \ print the array
 #ofRows @ 0 ?DO cr
   #ofCols @ 0 ?DO j i self at: . LOOP LOOP ;m

;class


\ begin binary tree code

0 [IF]
The basic tree engine is based on an example from Marcel Hendrix posted in usenet: 
 
  * DESCRIPTION : binary-tree 
  * AUTHOR      : Marcel Hendrix 
  * LAST CHANGE : July 29, 2006, Marcel Hendrix 

        REVISION -trees Binary trees        Version 1.00 

    From: 'Algoritms' Robert Sedgewick, ISBN 0-201-06672-6, page 178 - 185. 

Tree balancing has been added, in addition to making a tree class.  dbh
[THEN]

[undefined] about-win32forth [if]

:class node <super object
  rec{ var left
       var right
       var key
       var info }rec
;class

: display-char
   ." (" 0 .R ." ) " ;


:class btree <super object
  var size
  var oc-key \ container for keys ordered-col \ ordered-col will be sorted
  var oc-info \ container for info ordered-col, ordered as per key oc
  node head  
  node z 
  var key-display-xt
  var info-displ-xt
  var map-xt

:m size: ( -- size ) size @ ;m  
:m init:
    0 size !
    0 head [iv] key !
    0 head [iv] left !
    z head [iv] right !
\     ['] emit key-display-xt !
\     ['] display-char info-displ-xt !
    ;m
    
\ -- To search for a record with key v, do v 'head' tree-search ( -- link ) 
\ -- An unsuccessful search returns 'z'. 
:m search: \ { v | link -- link2 true | false }
  0 locals| link v |
  head to link
  v z [iv] key !
  BEGIN
    v link [iv] key @ <  IF   link [iv] left  @ to link
          ELSE link [iv] right @ to link 
          THEN
    link [iv] key @ v =
  UNTIL
   link dup z = IF drop false ELSE true THEN
   ;m

\ -- To insert a node in the tree, we just do an unsuccessful search for it, 
\ -- then hook it on in place of 'z' at the point where the search was terminated. 
\ -- When a new node whose key is already in the tree is inserted, it goes 
\ -- to the right of the node already in the tree. All records with key equal to v 
\ -- can be processed by successively setting t to tree-search(v,t). 
:m (insert): \ { v link | f -- link2 }
  0 locals| f link v |
    1 size +!
    BEGIN
     link to f 
     v link [iv] key @ <  IF   link [iv] left  @ to link
           ELSE link [iv] right @ to link 
           THEN
       link z =
    UNTIL
    heap> node to link
    v link [iv] key !
    z link [iv] left !
    z link [iv] right !
    v f [iv] key @ < IF   link f [iv] left !
         ELSE link f [iv] right !
         THEN
    link ;m

:m insert: \ { key inf -- } \ inf=info, can be anything that fits in one cell
   locals| inf key |
   key head self (insert): inf swap [iv] info ! ;m

:m (.nodes): \ { link -- }
         locals| link |
         link z = IF EXIT THEN
         link [iv] key @  key-display-xt @ execute  link [iv] info @  info-displ-xt @ execute 
         link [iv] left  @ DUP z <> IF recurse ELSE DROP THEN 
         link [iv] right @ DUP z <> IF recurse ELSE DROP THEN
         ;m

:m .nodes:
     head [iv] right @  self (.nodes): ;m

:m (map): \ { link -- }
         locals| link |
         link z = IF EXIT THEN
            link [iv] info @  \ get info to stack   
            map-xt @ execute  \ transform info 
            link [iv] info !  \ place transformed stack item into info
         link [iv] left  @ DUP z <> IF recurse ELSE DROP THEN 
         link [iv] right @ DUP z <> IF recurse ELSE DROP THEN
         ;m

:m map: ( xt -- ) \ apply xt to ( info @ ) for each node in the tree
     map-xt !
     head [iv] right @  self (map): ;m

:m (.sorted): \ { link -- }
         locals| link |
         link z = IF EXIT THEN 
         link [iv] left  @  recurse 
         link [iv] key   @  key-display-xt @ execute 
         link [iv] right @  recurse
         ;m
         
:m .sorted:
    head [iv] right @ self (.sorted):
         ;m
         
:m (free): \ { link -- }
   locals| link |
   link z = IF EXIT THEN
   link [iv] right @ IF link [iv] right @ recurse
          link [iv] left @ recurse
          THEN
   link <free ( cr ." free node" ) ;m

:m free-tree:
    head [iv] right @  self (free):
    self init: ;m
:m free:
   self free-tree:
   oc-key @ ?dup IF <free 0 oc-key ! THEN
   oc-info @ ?dup IF <free 0 oc-info ! THEN ;m

:m (ord-col): \ { link -- }
         locals| link |
         link z = IF EXIT THEN 
         link [iv] left  @  recurse 
         link [iv] key   @  oc-key @ add:
            link [iv] info @ oc-info @ add:
         link [iv] right @  recurse
         ;m


:m ord-cols: ( -- oc-key oc-info ) \ ordered-cols will be sorted
   self size: heap> ordered-col oc-key !
   self size: heap> ordered-col oc-info !
   head [iv] right @ self (ord-col): 
   oc-key @ oc-info @
   ;m

:m ((balance)):
  oc-key @ size:  0 ?DO I oc-key @ at:  I oc-info @ at:  self insert:
              LOOP ;m

:m (balance): \ { | idx odd -- }
  0 0 locals| idx odd |
  oc-key @ size: 3 < IF self ((balance)): exit THEN
  oc-key @ size: 2 /mod to idx to odd
  idx oc-key @ at: ( key) idx oc-info @ at: ( info) self insert:
  idx odd IF 1+ THEN 1
           DO idx I - oc-key @ at: ( key) idx I - oc-info @ at: ( info) self insert:
              idx I + oc-key @ at: ( key) idx I + oc-info @ at: ( info) self insert:
           LOOP
   odd 0=
   IF 0 oc-key @ at: ( key)  0 oc-info @ at: ( info)  self insert: THEN ;m

:m balance:
   self ord-cols: 2drop \ write out the tree to two ordered-col's (sorted)
   self free-tree:    \ clear the tree
   self (balance): \ re-build the tree as a balanced tree
   oc-key @ <free oc-info @ <free \ free the ordered-cols
   0 oc-key !  0 oc-info !
   ;m

\ as a side-effect delete: will also balance the tree
:m delete: \ { n -- true | false } \ n = key to delete, true if successful
   self ord-cols: 2drop \ write out the tree to two ordered-col's (sorted)
   ( n ) oc-key @ search: ( idx T | F )
   IF ( idx ) dup oc-key @ delete:
                  oc-info @ delete:
      self free-tree:
      self (balance):
      oc-key @ <free oc-info @ <free
      0 oc-key ! 0 oc-info !
      true
    ELSE
      false
    THEN ;m

;class

[then]

cr .( fmsLib 02/18/12 dbh Class Library is Loaded )
