\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Dec 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com


[undefined] string [if] .( string.f required ) abort [then]

:class file   ( c-a u -- ) \ file name
  cell bytes id
  cell bytes name 
  cell bytes fam  \ file access method
  1 bytes open?
  cell bytes one-line 
  cell bytes buffer 

:m :init ( c-a u -- ) heap> string name ! 0 0 heap> string one-line !
   false open? c!
   r/w fam ! \ default fam is r/w
   0 0 heap> string buffer !
   ;m

:m :size ( -- u )
   open? c@ if id @ FILE-SIZE throw d>s
            else -1 abort" file not open"
            then ;m
            
:f :fam ( fam -- ) fam ! ;f

:f :open 
   open? c@ if exitf then
   name @ :@ fam @ OPEN-FILE throw
   id !
   true open? c!
   ;f

: ?open open? c@ 0= if self :open then ;

:m :delete  
   ?open
   name @ :@ DELETE-FILE throw
   0 open? c! 
   name @ <free  one-line @ <free buffer @ <free
   ;m

:f :create ( -- )
   name @ :@
   fam @ CREATE-FILE throw
   id !
   true open? c!
   ;f

:f :flush
   id @ FLUSH-FILE drop ;f

:f :read ( -- str-obj )
   ?open
   id @ FILE-SIZE ABORT" read: FILE-SIZE failed"
   ( ud ) d>s buffer @ :resize 
   buffer @ dup :@ ( addr len ) id @ READ-FILE throw drop
   ;f

:f :read-line \ { m -- str-obj true | false } \ m is max chars to be read per line
   ?open
   one-line @ :resize one-line @ :@ ( addr len )
   id @ READ-LINE throw
   if one-line @ :resize
      one-line @ dup :reset  true
   then ;f


:f :write-line ( addr len -- ) 
   ?open 
   ( addr len ) id @ WRITE-LINE throw
;f

:f :!pos ( n -- ) 
   ?open
   s>d id @ REPOSITION-FILE ABORT" :!pos REPOSITION-FILE failed"
   ;f
 

:f :@pos ( -- n )
   ?open
   id @ FILE-POSITION ABORT" :@pos FILE-POSITION failed"
   d>s ;f

:f :write ( addr len -- )
   ?open
   ( addr len) id @ WRITE-FILE throw
   ;f

:f :close 
   open? c@ 0= if exitf then
   id @ CLOSE-FILE throw
   0 open? c!
   ;f

 :m :free  name @ <free  one-line @ <free buffer @ <free ;m

;class
