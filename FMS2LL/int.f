\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Feb 8, 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com

: integer>str ( n -- adr len) 
  s>d dup >r dabs <# #s r> sign #> ; 

:class int 
  cell bytes idata 
 :m :init ( n -- ) idata ! ;m
 :m :! ( n -- )  idata ! ;m
 :m :@ ( -- n )  idata @ ;m
 :m :.  idata @ integer>str type ;m \ print self without a trailing space
 :m := ( obj -- flag ) :@ idata @ = ;m
 :m :> ( obj -- flag ) :@ idata @ > ;m
 :m :write ( str -- ) locals| str |
     idata @ integer>str str :add ;m
;class

: >int ( n -- obj ) heap> int ;

