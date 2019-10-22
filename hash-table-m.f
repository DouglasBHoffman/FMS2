\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Oct 16 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com



[undefined] hash-table [if] .( requires class hash-table to be loaded) abort [then]





\ Since the same join attribute, Name, occurs more than once
\ in both tables for this problem we need a hash table that
\ will accept and retrieve multiple identical keys if we want
\ an efficient solution for large tables. We make use
\ of the hash collision handling feature of class hash-table.

\ Subclass hash-table-m allows multiple entries with the same key.
\ After a :@ hit one can inspect for additional entries with
\ the same key by using :next until false is returned.

:class hash-table-m <super hash-table

\ called within :insert method in superclass 
 :m :search ( node idx hash -- idx hash false )
    rot drop false ;m 

 :m :next ( -- val true | false )
    last-node @ dup
    if
      begin
       ( node ) :next dup
      while
        dup :key@ :@ key-addr @ key-len @ compare 0=
             if dup last-node ! :val@ true exit then
      repeat 
    then ;m


;class

 
 
 
0 [if]

hash-table-m r  

s" Whales "   >string s" Jonah" r :insert
s" Spiders "  >string s" Jonah" r :insert
s" Ghosts "   >string s" Alan"  r :insert
s" Buffy "    >string s" Glory" r :insert 
s" Zombies "  >string s" Alan"  r :insert
s" Vampires " >string s" Jonah" r :insert
 
R is redefined ok
 


s" Jonah" r :@ . .  -1 12630160 ok

12630160 :. \ Whales  ok Whales  ok

r :next . \  -1 ok \ 1  -1 ok \ 1 

:. \ Spiders  ok Spiders  ok

r :next . \ -1 ok \ 1  -1 ok \ 1 

:. \ Vampires  ok Vampires  ok

r :next . \ 0 ok 0 ok



[then]

