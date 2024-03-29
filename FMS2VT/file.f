
\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Feb 8, 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com

\ after a :read the file will be sent the :close message \ Dec 2020
\ :read-line default max length is 500
\ :write changed to a message

[undefined] string [if] .( string.f required ) abort [then]

:class file  ( c-a u -- ) \ file name
  cell bytes id
  cell bytes name 
  cell bytes fam  \ file access method
  1 bytes open?
  cell bytes one-line 
  cell bytes buffer 
  cell bytes dflt-line-len

:m :!line-len ( n -- ) dflt-line-len ! ;m

fmscheck? [if]
:m :d
   cr ." id " id ?
   cr ." name " name @ :.
   cr ." open? " open? c@ .
   cr ." one-line " one-line @ :.
   ;m
[then]

:m :init ( c-a u -- ) heap> string name ! 0 0 heap> string one-line !
   false open? c!
   r/w fam ! \ default fam is r/w
   0 0 heap> string buffer !
   500 dflt-line-len !
   ;m

:m :size ( -- u )
   open? c@ if id @ FILE-SIZE throw d>s
            else -1 abort" file not open"
            then ;m
            
:m :fam ( fam -- ) fam ! ;m

:m :open 
   open? c@ if exit then
   name @ :@ fam @ OPEN-FILE throw
   id !
   true open? c!
   ;m

: ?open open? c@ 0= if self :open then ;

:m :delete  
   ?open
   name @ :@ DELETE-FILE throw
   0 open? c! 
   name @ <free  one-line @ <free buffer @ <free
   ;m

:m :create ( -- )
   name @ :@
   fam @ CREATE-FILE throw
   id !
   true open? c!
   ;m

:m :flush
   id @ FLUSH-FILE drop ;m

:m :close 
   open? c@ 0= if exit then
   id @ CLOSE-FILE throw
   0 open? c!
   ;m

:m :read ( -- str-obj )
   ?open
   id @ FILE-SIZE ABORT" :read FILE-SIZE failed"
   ( ud ) d>s buffer @ :resize 
   buffer @ dup :@ ( addr len ) id @ READ-FILE throw drop
   self :close
   ;m

\ added :uneach to fix bug  12-27-2021 dbh
:m :read-line ( -- str-obj true | false )
   ?open
   dflt-line-len @
   one-line @ :resize one-line @ :@ ( addr len )
   id @ READ-LINE throw
   if one-line @ :resize
      one-line @ dup :reset dup :uneach  true
   then ;m


:m :write-line ( addr len -- ) 
   ?open 
   ( addr len ) id @ WRITE-LINE throw
;m

:m :!pos ( n -- ) 
   ?open
   s>d id @ REPOSITION-FILE ABORT" :!pos REPOSITION-FILE failed"
   ;m

   \ added :each and :uneach 12-27-2021 dbh
:m :each ( -- str-obj t | f )
    self :read-line ;m
    
:m :uneach
    0 self :!pos ;m


:m :@pos ( -- n )
   ?open
   id @ FILE-POSITION ABORT" :@pos FILE-POSITION failed"
   d>s ;m

:m :write ( addr len -- )
   ?open
   ( addr len) id @ WRITE-FILE throw
   ;m


 :m :free  self :close name @ <free  one-line @ <free buffer @ <free ;m

;class

: >file heap> file ;

