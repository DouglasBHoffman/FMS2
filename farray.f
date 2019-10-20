\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Oct 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com

[undefined] array [if] .( file array.f required ) abort [then]

[undefined] floats [if] cr .( floating point extension is missing) abort
[then]

:class farray <super array
 cell bytes astart \ for shell sort

 :m :init \ ( -- ) or if static: ( max#elems --)
    ?alloc dup  alloc? c!
    if 0 super :init  
    else ( max#elems ) dup len ! floats align here swap allot data !
    then
    0 #elems !
     1 floats  elemSize !
     ;m

 :m :@elem ( addr -- elem ) f@ ;m

 :m :to ( idx -- ) ( F: elem -- )  ^elem  f! ;m
 :m :at ( idx -- ) ( F: -- elem ) ^elem  f@ ;m
 :m .elem ( F: elem -- ) f. ;m

\ SHELLSORT     v1.3    28 October 1994         cgm     
\ (c) Copyright 1994 Charles G. Montgomery.  Permission is granted by the
\ author to use this software for any purpose provided this copyright
\ notice is preserved.
\ Shell-Metzger in-place ascending sort of floating array
\   see, e. g., Press et al, Numerical Recipes, Cambridge (1986)

: shellsort ( nsize xt -- )
    locals| xt |
    0 ^elem astart !
    DUP
    BEGIN       ( nsize mspacing )
      2/ DUP    
    WHILE       ( n m )
      2DUP - 0
      DO        ( n m )
       0 I DO   ( n m )

\ compare Ith and (I+M)th elements 
              DUP I + DUP               ( n m l l )
              I FLOATS astart @ + F@      ( n m l ;F: Al Ai )
              FLOATS astart @ + F@        
              xt execute  

\ switch them if necessary
              IF  DROP LEAVE            ( n m )
              THEN                      ( n m l )
              FLOATS astart @ + DUP F@
              I FLOATS astart @ + DUP F@  ( n m &Al &Ai ;F: Al Ai )
              SWAP F! F!

              DUP NEGATE                ( n m -m )
            +LOOP
      LOOP
    REPEAT   2DROP
;


\ use ' f< for ascending sort
 :m :sortWith ( xt -- ) #elems @  swap shellsort ;m

 :m :sort ['] f< self :sortWith ;m

 :m :search ( -- idx true | false ) ( F: r -- ) 
    self :size 0 ?do fdup i self :at f=
          if fdrop i true unloop exit then loop fdrop false ;m

;class


: >farray heap> farray ;


