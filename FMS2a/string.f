\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Jan 2020 Douglas B. Hoffman
\ dhoffman888@gmail.com
\ corrected check 12/9/2019
\ changed to strict 0-127 ascii chars 1/3/2020

[undefined] ptr [if] .( file ptr.f required ) abort [then]
[undefined] array [if] .( file array.f required ) abort [then]

:class string <super ptr \ ( adr len -- ) heap> or ( adr len max -- ) dict>
\ len will contain the current size in bytes, <= maxize if a static instance
  cell bytes maxsize \ if zero, then string is allocated in the heap  
  cell bytes start
  cell bytes end
  cell bytes current-idx \ for use with :each

\ *** begin Boyer-Moore search engine
\ ref. "A Fast String Searching Algorithm", Robert S. Boyer, J Strother Moore
\ http://www.cs.utexas.edu/users/moore/publications/fstrpos.pdf

: set-deltaTable  \ { patternA patLen deltaTable | r -- }
  1 locals| r deltaTable patLen |
  deltaTable 128 patLen fill
  ( patternA) patLen over + swap ?do 
        patLen r -   i c@   deltaTable + c!  r 1+ to r loop ;
\      patLen r -    = number to store in deltaTable
\      i c@ = index into deltaTable
[undefined] noop [if] : noop ; [then]

\ text is text to be searched for the pattern substring.
\ If the search is successful n is the offset into the text where
\ pattern was found, otherwise return 0.
\ flag=true  then do a case-insensitive search
\ flag=false then do a case-sensitive   search

defer lower
[undefined] >lower [if] : >lower ( char -- char') 32 or ; [then] \ return lower-case character of c

\ if flag is true (case insensitive search) then the pattern text will already be lower case
: fast-search ( patternA patLen textA textLen deltaTable flag  -- n true | false )
  ( flag) if  ['] >lower else ['] noop then is lower 
  0 0 locals| textIdx patIdx deltaTable textLen textA patLen patternA |
  patLen 1- to textIdx
  patLen to patIdx
  patternA patLen deltaTable set-deltaTable   
  begin
    textIdx 1- textLen >= if false exit then
    textIdx textA + c@ lower dup  patIdx 1- patternA + c@ = 
    if
      drop
      textIdx 1- to textIdx  patIdx 1- to patIdx
    else
      patLen patIdx - 1+
      swap deltaTable + c@
      max textIdx + to textIdx
      patLen to patIdx 
    then
    patIdx 1 <
  until
  textIdx 1+ true ;

\ *** end Boyer-Moore search engine

fmsCheck? [if]

\ Last Revision:  9 Dec 2019  06:39:19  dbh added dup 0= if 2drop exit then
: check ( n --) maxsize @ dup 0= if 2drop exit then > abort" string max-size exceeded" ;
[else] : check drop ;
[then]
 :m :resize ( newsize -- )
    maxsize @
    if  dup check len ! 
    else  super :resize
    then ;m
 :m :reset 0 start !  0 end !  ;m

\ get is a private non-virtual method ( self does not need setting)
 : get ( -- adr len ) data @ len @ ;
 :m :@ ( -- addr len ) get ;m

 :m :copy ( -- obj ) \ return string object copy in dict or heap, same as original
    self :@ maxsize @
    if   maxsize @ dict> string
    else heap> string
    then ;m

 :m :delete  \ deletes the substring defined by START and END
             \ leaves START at the same place, END is set to START
     data @ end @ +   \ src 
     data @ start @ + \ src dest
     len @ end @ - \ src dest cnt
     move
    len @  end @ start @ - -  self :resize
    start @ end ! ;m

 :m :add ( addr len -- ) \ add text to end of string
   maxsize @
   if dup len @ + check >r get + r@ move r> len +!
   else
     dup ( addr-src len len )
     len @ dup >r + self :resize 
     data @ r> + swap move
   then ;m
 :m :+ ( strObj -- ) \ add all text from strObj to end of string
    :@ self :add ;m

 :m :! ( addr len -- ) maxsize @
    if dup check dup len ! data @ swap move
    else dup super :resize data @ swap move
    then ;m


 :m :init \ ( adr len -- ) or if static: ( adr len max --)
    ?alloc 
    if dup super :init self :! 0 maxsize !
    else dup maxsize ! align here swap allot data ! self :! 
    then 0 current-idx ! self :reset ;m
 :m :. get type ;m

fmsCheck? [if]
: ?idx ( idx -- idx )
     dup len @ 1- > abort" string index out of range" ; 
[else] : ?idx ;
[then]
\ :at and :to indexes refer to the entire string
 :m :at ( idx -- char )
     ?idx data @ + c@ ;m
 :m :to ( char idx -- )
     ?idx data @ + c! ;m 

 :m :remove ( idx -- char) \ removes char at idx and shrinks string size by one
                           \ removed char is returned
    dup >r self :at
    r> dup start ! 1+ end ! self :delete ;m
 
 :m :uneach 0  current-idx ! ;m

 :m :each ( -- char true | false)
     current-idx @ dup  len @ <
    if 1 current-idx +! self :at true else drop self :uneach false then ;m

 : lowerCase? ( char -- flag ) \ flag is true if char is lower case
  [CHAR] a [CHAR] z 1+  within ;

: >upper ( char -- char') \ return upper-case character of char
  dup lowerCase? if 32 xor then ;
: >lower ( char -- char') 32 or ; \ return lower-case character of char

: to-lower ( adr len -- ) \ convert entire string to lowercase in-place
  over \ addr cnt addr
  + swap  \ cnt+addr addr
  ?do i c@ >lower i c!
  loop ;

 :f :upper \ converts entire string to upper case
     get 
     over \ addr cnt addr
	 + swap  \ cnt+addr addr
	 ?do i c@ dup
	  lowercase?
	  if 32 xor i c!
	  else drop
	  then
	 loop ;f
 :f :lower \ converts entire string to lower case
     get to-lower ;f

 :f :@sub ( -- addr len ) \ fetch substring
    data @ start @ + ( addr ) end @ start @ - ;f

 :f :selectAll \ select entire string
    0 start ! len @ end ! ;f

 :f :=sub ( addr1 len1 -- b )  \ case sensitive
    dup end @ start @ - <> if 2drop false exitf then  \ get out early if length mismatch
    self :@sub compare 0= ;f

 :f :=subCI ( addr1 len1 -- b ) \ case insensitive
    dup end @ start @ - <> if 2drop false exitf then  \ get out early if length mismatch
    ( addr1 len1) heap> string  >r self :@sub heap> string  
    dup :lower   r@ :lower \ make both string copies lowercase
    dup :@  r@ :@ compare 0=
    swap <free r> <free ;f

 \ compare addr1 len1 to the entire string
 :m := ( addr1 len1 -- true | false ) \ case sensitive
     self :selectAll
     self :=sub ;m
 :f :=CI ( addr1 len1 -- true | false ) \ case insensitive
     self :selectAll
     self :=subCI ;f

: (search)1 ( addr len -- flag ) dup len @ end @ - > ;
: str-obj ( -- str-obj) heap> string 128 allocate throw ;
: (search)2 ( -- len) data @ end @ + ( start-addr) len @ end @ - ( len) ;
: (search)3 end @ + dup start ! over :size + end ! true ;

 :m :search ( addr len -- true | false ) \ case sensitive  
    \ first do rationality check
    \ return false if len to find is greater than remainder
   (search)1 if 2drop false exit then
   str-obj >r \ str
   dup :@ (search)2 r@ false fast-search
   if (search)3
   else false
   then swap <free r> free throw ;m

:f :searchCI ( addr len -- true | false ) \ case insensitive
    \ first do rationality check
    \ return false if len to find is greater than remainder
   (search)1 if 2drop false exitf then
   str-obj >r \ str  
   dup :@ 2dup to-lower (search)2 r@ true fast-search
   if (search)3
   else false
   then swap <free r> free throw ;f

\ inserts text starting at END, START and END are moved to end of inserted text
 :m :insert \ { addr len -- }
    >r
    len @ r@ + self :resize
    data @ end @ + dup ( src src ) r@ + ( dest ) len @ end @ - r@ - ( cnt ) move
    ( addr) ( src ) data @ end @ + ( dest ) r@  move
    end @ r> + dup start ! end ! ;m
 
\ replace selected text, if any, with given text
 :m :replace ( addr len -- )
     self :delete self :insert ;m

 :f :start ( -- start-addr ) start ;f

 :f :end ( -- len-addr ) end ;f
 
fmsCheck? [if]
 :m :d  ( -- ) \ formatted dump of string for debugging and illustration of method effects
        \ Only displays the first 40 chars
   cr ."                     1                   2                   3                   4"
   cr ." 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0"
   cr  self :size 40 min 0 ?DO space i self :at emit LOOP
   cr start @ 40 min 2* spaces [char] S emit
   cr end @ 40 min 2* spaces [char] E emit
   cr ." start= " start @ .  ."  end= " end @ .   ."  size= " self :size .
   ." maxsize= " maxsize @ . 
 ;m
 [then]
 
 :f :ch+ ( char -- ) \ add char to end of string
     len @ 1+ self :resize  get + 1- c! ;f

: chsearch ( c xt -- flag )
   is lower
    lower >r
    begin
     self :each 
    while
     lower
     r@ = if current-idx @ dup 1- start ! end ! r> drop true exit then
    repeat r> drop false ;
       
:f :chsearch ( c -- flag ) 
   ['] noop chsearch ;f
    
:f :chsearchCI ( c -- flag )
   ['] >lower chsearch ;f
 

\ inserts char at END, START and END are moved to just past inserted char
:f :chinsert ( c -- ) pad c!  pad 1 self :insert ;f 

:m :first ( -- c ) 0 self :at ;m
:m :second ( -- c ) 1 self :at ;m
:m :last ( -- c ) self :size 1- self :at ;m

;class


\ string HOFs

\ make a string in the heap
: >string ( adr len -- obj ) heap> string ; 



\ Search for text1 starting at END.
\ Will only replace one occurrence
\ If found replace with text2.
\ Success flag is returned. (sch&repl) is not used directly
 : (sch&repl)  \ { addr1 len1 addr2 len2 str-obj xt -- flag }
    locals| xt obj len2 addr2 len1 addr1 |
    addr1 len1 obj xt execute dup
    if addr2 len2 obj :replace then ;
 : :sch&repl  \ { addr1 len1 addr2 len2 str-obj -- flag }
    ['] :search (sch&repl) ;
 : :sch&replCI  \ { addr1 len1 addr2 len2 str-obj -- flag }
    ['] :searchCI (sch&repl) ;

 

 
\ Reset obj and replaces all occurrences of (addr1 len1) by (addr2 len2)
\ in the WHOLE of obj.  Obj is lastly reset again. 
\ (replall) is not used directly
: (replall) \ { addr1 len1 addr2 len2 str-obj xt  -- }
    locals| xt obj len2 addr2 len1 addr1  |
 obj :reset
 begin
   addr1 len1 obj xt execute
 while
  addr2 len2 obj :replace
 repeat
 obj :reset ;

 : :replall \ { addr1 len1 addr2 len2 str-obj -- } \ case sensitive
   ['] :search (replall) ;
 : :replallCI \ { addr1 len1 addr2 len2 str-obj -- } \ case insensitive
   ['] :searchCI (replall) ;
 



\ find substring(s) delimited by:
\ 1) start of string and char
\ 2) and char and char
\ 3) and char and end of string
\ return all of them as an array of string objects allocated in the heap
: :split ( char str-obj -- 1-arry-obj )
    heap> array 0 locals| strt arr obj c |
   obj :reset
   begin
     c obj :chsearch
   while
    obj :start @ obj :end @
    strt obj :start ! -1 obj :end +!
    obj :@sub heap> string arr :add
    dup to strt
    obj :end ! obj :start !
   repeat
    1 obj :start +!
    obj :size obj :end !
    obj :@sub heap> string arr :add
   arr ;


\ remove leading and trailing chars, removes more than one char(s) occurring consecutively between words
\ original string is untouched, new heap string is returned
: :remove-extra-chars ( c str-obj -- newstr )
   0 0 heap> string true locals| last-char-was-c? newstr obj c  |
   obj :size 0 ?do i obj :at dup c =
                    if last-char-was-c? 0= if newstr :ch+ true to last-char-was-c? else drop then
                    else newstr :ch+ false to last-char-was-c?
                    then
                loop
                last-char-was-c? if newstr :size 1- newstr :resize then
                newstr ;
