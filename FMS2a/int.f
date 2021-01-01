: integer>str ( n -- adr len) 
  s>d dup >r dabs <# #s r> sign #> ; 

:class int  
  cell bytes data 
 :m :init ( n -- ) data ! ;m
 :m :! ( n -- )  data ! ;m
 :m :@ ( -- n )  data @ ;m
 :m :.  data @ integer>str type ;m \ print self without a trailing space
 :m := ( obj -- flag ) :@ data @ = ;m
 :m :> ( obj -- flag ) :@ data @ > ;m
 :m :write ( str -- ) locals| str |
     data @ integer>str str :add ;m
;class

: >int ( n -- obj ) heap> int ;
