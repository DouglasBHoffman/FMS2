\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Oct 16 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com



[undefined] string [if] .( requires classes array and string to be loaded) abort [then]

:class hash-table-node
 cell bytes hash
 string key
 cell bytes val
 cell bytes next
 :m :init 0 0 key :init ;m
 :f init ( val kaddr klen -- ) \ Initialise the node with the val, key
     key :!  val !  0 next ! ;f
 :m :free key :free ;m
 :f :key@ ( -- obj ) \ will be a string object
     key ;f
  :f :val@ ( -- val ) val @ ;f
 :f :val! ( -- val ) val ! ;f
 :m :next ( -- next-node ) next @ ;m
 :f :next! ( next-node -- ) next ! ;f
 :m :@ ( -- hash ) hash @ ;m
 :m :! ( -- hash ) hash ! ;m
 fmscheck? [if]
 :m :d \ dump
    cr ." hash " hash ?
    cr ." key " key :.
    cr ." val " val ?
    cr ." next " next ?
    cr ;m
  [then]
;class



0 [if]
from https://en.wikipedia.org/wiki/Hash_table#In_programming_languages

Associative arrays
Hash tables are commonly used to implement many types of in-memory tables.  They are used to implement associative
arrays (arrays whose indices are arbitrary strings or other complicated objects), especially in interpreted
programming languages like Perl, Ruby, Python, and PHP. 

When storing a new item into a typical associative array and a hash collision occurs, but the actual keys themselves
are different, the associative array likewise stores both items.

\ The following is how class hash-table works: an :insert with an existing key will simply over-write the value
However, if the key of the new item exactly matches the key of an old item, the associative array typically erases the
old item and overwrites it with the new item, so every item in the table has a unique key. 

\ But see class hash-table-m for the ability to store multiple identical keys with differing values
\ and how to retrieve them later.

[then]


\ Hash collisions are handled by separate chaining with head records in the bucket array.
:class hash-table
 cell bytes table  \ will contain an array object \ array of pointers to the nodes 
 cell bytes #nodes \ number of nodes
 cell bytes load \ load factor times 100
 cell bytes val
 cell bytes key-addr
 cell bytes key-len
 cell bytes last-node
 
 :m :init heap> array table !
    0 #nodes !
    100 load !
    3 0 do 0 table @ :add loop \ initialize with 3 cells 
 ;m

: hash-iv  ( addr len -- hash ) \ from Dick Pountain JFAR Vol3 Number 3 p68
  32 min 0 swap 0 do over i + c@ i 1+ * + loop swap drop ;

\ idx to the table location is returned if false
 : do-search \ { -- node idx hash true | idx hash false }
    0 0 locals| hsh idx |
    key-addr @ key-len @ hash-iv dup to hsh table @ :size mod abs ( idx) dup to idx  table @ :at
    ( node-obj)
    begin
      dup if dup :key@ :@ key-addr @ key-len @ compare 0= if ( node-obj ) idx hsh true exit then then
      dup
    while
      :next
    repeat drop idx hsh false ;

: ll-delete \ { node idx -- true }
   locals| idx node |
   node :key@ :@ idx table @ :at :key@ :@ compare 0= if node :next idx table @ :to
                                                    node <free  -1 #nodes +! true exit
                                                 then
   idx table @ :at \ walk linked-list, node to delete is not in table slot
   begin
    dup :next ?dup
   while
    ( parent-node child-node ) dup :key@ :@ node :key@ :@ compare 0=
    if \ found it, must relink the child of child-node to parent-node
       ( parent-node child-node ) :next swap :next! node <free -1 #nodes +! true exit
    then
   repeat abort" failure in ll-delete" ; \ should never get here

:m :delete \ { kaddr klen -- flag } \ true if key was found (and hence deleted), false if not
   key-len ! key-addr !
   do-search
   if ( node idx hash ) drop ll-delete
   else ( idx hash ) 2drop false exit
   then ;m
 
 :m :@ ( key-addr key-len -- val true | false )
    key-len ! key-addr !
    do-search
    if ( node idx hash ) 2drop dup last-node ! :val@ true 
    else ( idx hash ) 2drop 0 last-node ! false
    then ;m

: transfer-insert \ { node new-table new-size -- }
    locals| new-size new-table |
    ( node) dup :@ new-size  mod abs ( idx ) new-table  :^elem \ compute new table location
    ( node-addr) dup @
    if  \ slot not empty, must add node-obj to hash collision linked-list 
      @ ( pre-existing node-obj in new table)
      begin  \ walk linked list to end
        dup :next ?dup
      while
        ( parent-node child-node ) nip 
      repeat 
        \ end of linked-list, add transferred node there
        ( node parent-node ) over swap  :next! \ link in node 
    else
      \ found empty slot in new-table
      over swap ! \ insert node in new-table
    then
    0 swap :next! \ zero out next in transferred node
    ;

: transfer \ { new-size new-table -- }
    locals| new-table new-size |
    table @ :size 0 do i table @ :at \ step thru each element of the old table
    ?dup if ( parent-node) dup :next swap new-table new-size transfer-insert  \ we have found a node in the old table
              \ note that we grab next before calling transfer-insert because transfer-insert
              \ will store 0 in the parent-node next, wiping out any existing child-node
              begin \ step thru linked list for additional nodes
               ?dup
              while
               dup :next swap new-table new-size transfer-insert
              repeat
         then
    loop
    table @ <free 
    new-table table ! ;


\ new-node is a normal colon definition but is private to this class
: new-node ( hash -- new-node )
   1 #nodes +! \ increment #nodes
   heap> hash-table-node >r
   val @ key-addr @ key-len @ r@ init
   ( hash ) r@ :! r> ;

:m :search ( node idx hash -- true )
      2drop 
      val @ swap :val! true
   ;m

:m :insert \ { val key-addr key-len | idx node hash -- }
    0 0 0 0  locals| new-table node hsh idx |
   key-len ! key-addr ! val !
   do-search
   if \ already present so just update val
      self :search if exit then
   then
   ( idx hash ) to hsh dup to idx table @ :at
    ( node-obj) dup 0=
    if drop   \ found empty slot in table
       hsh new-node  idx table @ :to
    else
    \ must add new node-obj to hash collision linked-list                 
      ( node-obj)  
      begin \ walk linked list to end 
        dup to node 
        :next dup 0<>
      while
      repeat drop
       \ end of linked-list, add new node there
       hsh new-node  node :next!
    then
       \ lastly test for need to increase table size
       \ and do it if required
       #nodes @ table @ :size load @ 100 */ >
       if table @ :size 2* 1+ ( new-size )
          heap> array ( new-size new-table )
          2dup to new-table 0 ?do 0 new-table :add loop
          transfer then
       ;m 

: (free) \ { node }
   >r
   r@ :next ?dup if ( next-node) recurse
                   then r> <free ;

:m :free
    begin
      table @ :each
    while
      ?dup if ( node ) (free)
            then
    repeat table @ <free ;m

: free-node-val \ { node }
  :val@ <free ;

fmsCheck? [if]
\ dump the entire hash table and each node
 :m :d table @ :.
     cr ." #nodes " #nodes ?
     cr ." table size " table @ :size .
     cr
    table @ :size 0 do
      cr i table @ :at dup 0=
      if .
      else dup :d
	      begin \ dump linked-list, if any linked nodes
	        dup
	      while
	        :next dup 0<> if dup :d then
	      repeat drop
	  then
    loop
    ;m
[then]

;class
 
 


0 [if]


hash-table t2  

8888 s" Now" t2 :insert   
6 s" dog" t2 :insert  
77 s" cat" t2 :insert 
55 s" frog" t2 :insert 
100 s" pony" t2 :insert 
200 s" fish" t2 :insert 
300 s" tree" t2 :insert 
400 s" double" t2 :insert 
500 s" build" t2 :insert 
600 s" trying" t2 :insert 
700 s" oh well" t2 :insert 
800 s" my oh my" t2 :insert 
 
T2 is redefined ok
 
T2 is redefined ok
  ok
 
T2 is redefined ok
 ok
 ok
: foo t2 ; \ error: control structure mismatch 
T2 is redefined ok
 
s" fish" t2 :@ . .  -1 200 ok




s" fish" t2 :delete .  -1 ok



s" fish" t2 :@ .  0 ok





 
T2 is redefined  
t2 :d          
0 11987200 
1 12408960 
2 0 
3 0 
4 12332944 
5 0 
6 11715376 
7 0 
8 12250128 
9 0 
10 12356896 
11 12346640 
12 11725456 
13 0 
14 0 
#nodes 12 
table size 15 


hash 2295 
key trying 
val 600 
next 0 


hash 631 
key dog 
val 6 
next 12373328 

hash 1051 
key tree 
val 300 
next 0 

0 
0 

hash 1579 
key build 
val 500 
next 12522224 

hash 3334 
key my oh my 
val 800 
next 0 

0 

hash 2211 
key double 
val 400 
next 0 

0 

hash 1148 
key pony 
val 100 
next 11953008 

hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 11916000 

hash 2800 
key oh well 
val 700 
next 0 


hash 641 
key cat 
val 77 
next 0 


hash 657 
key Now 
val 8888 
next 0 

0 
0 ok

0 11697312 
1 11720864 
2 0 
3 0 
4 12365168 
5 0 
6 11810336 
7 0 
8 11685024 
9 0 
10 12332896 
11 12353696 
12 11680768 
13 0 
14 0 
#nodes 12 
table size 15 


hash 2295 
key trying 
val 600 
next 0 


hash 631 
key dog 
val 6 
next 11753872 

hash 1051 
key tree 
val 300 
next 0 

0 
0 

hash 1579 
key build 
val 500 
next 11650640 

hash 3334 
key my oh my 
val 800 
next 0 

0 

hash 2211 
key double 
val 400 
next 0 

0 

hash 1148 
key pony 
val 100 
next 11569488 

hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 12380272 

hash 2800 
key oh well 
val 700 
next 0 


hash 641 
key cat 
val 77 
next 0 


hash 657 
key Now 
val 8888 
next 0 

0 
0 ok

0 15343696 
1 15406688 
2 0 
3 0 
4 15460272 
5 0 
6 15349344 
7 0 
8 14762272 
9 0 
10 14718992 
11 15365136 
12 15424768 
13 0 
14 0 
#nodes 12 
table size 15 


hash 2295 
key trying 
val 600 
next 0 


hash 631 
key dog 
val 6 
next 15466768 

hash 1051 
key tree 
val 300 
next 0 

0 
0 

hash 1579 
key build 
val 500 
next 15242272 

hash 3334 
key my oh my 
val 800 
next 0 

0 

hash 2211 
key double 
val 400 
next 0 

0 

hash 1148 
key pony 
val 100 
next 14958304 

hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 15323712 

hash 2800 
key oh well 
val 700 
next 0 


hash 641 
key cat 
val 77 
next 0 


hash 657 
key Now 
val 8888 
next 0 

0 
0 ok

0 13133024 
1 13186416 
2 0 
3 0 
4 13402672 
5 0 
6 13467520 
7 0 
8 13190496 
9 0 
10 13391024 
11 13158336 
12 13299792 
13 0 
14 0 
#nodes 12 
table size 15 


hash 2295 
key trying 
val 600 
next 0 


hash 631 
key dog 
val 6 
next 13273488 

hash 1051 
key tree 
val 300 
next 0 

0 
0 

hash 1579 
key build 
val 500 
next 13353008 

hash 3334 
key my oh my 
val 800 
next 0 

0 

hash 2211 
key double 
val 400 
next 0 

0 

hash 1148 
key pony 
val 100 
next 12744832 

hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 13313696 

hash 2800 
key oh well 
val 700 
next 0 


hash 641 
key cat 
val 77 
next 0 


hash 657 
key Now 
val 8888 
next 0 

0 
0 ok

0 11672736 
1 11839936 
2 0 
3 0 
4 11571936 
5 0 
6 12517648 
7 0 
8 12411584 
9 0 
10 12489344 
11 11625104 
12 12192352 
13 0 
14 0 
#nodes 12 
table size 15 


hash 2295 
key trying 
val 600 
next 0 


hash 631 
key dog 
val 6 
next 12388512 

hash 1051 
key tree 
val 300 
next 0 

0 
0 

hash 1579 
key build 
val 500 
next 11615168 

hash 3334 
key my oh my 
val 800 
next 0 

0 

hash 2211 
key double 
val 400 
next 0 

0 

hash 1148 
key pony 
val 100 
next 12000384 

hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 12302272 

hash 2800 
key oh well 
val 700 
next 0 


hash 641 
key cat 
val 77 
next 0 


hash 657 
key Now 
val 8888 
next 0 

0 
0 ok

0 0 
1 15435728 
2 15094000 
3 0 
4 15583344 
5 0 
6 15217520 
7 15128672 
8 0 
9 0 
10 0 
11 15388544 
12 0 
13 0 
14 15556208 
15 0 
16 15034864 
17 0 
18 0 
19 0 
20 0 
#nodes 12 
table size 21 

0 

hash 631 
key dog 
val 6 
next 14996784 

hash 1051 
key tree 
val 300 
next 0 


hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 15098096 

hash 1579 
key build 
val 500 
next 0 

0 

hash 2211 
key double 
val 400 
next 15043616 

hash 2295 
key trying 
val 600 
next 12618544 

hash 657 
key Now 
val 8888 
next 0 


hash 2800 
key oh well 
val 700 
next 0 

0 
0 
0 

hash 641 
key cat 
val 77 
next 0 

0 
0 

hash 1148 
key pony 
val 100 
next 0 

0 

hash 3334 
key my oh my 
val 800 
next 0 

0 
0 
0 
0 ok

0 0 
1 12590608 
2 12606448 
3 0 
4 12789296 
5 0 
6 12735744 
7 12706576 
8 0 
9 0 
10 0 
11 12668512 
12 0 
13 0 
14 12789344 
15 0 
16 12790208 
17 0 
18 0 
19 0 
20 0 
#nodes 12 
table size 21 

0 

hash 631 
key dog 
val 6 
next 12606496 

hash 1051 
key tree 
val 300 
next 0 


hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 12735792 

hash 1579 
key build 
val 500 
next 0 

0 

hash 2211 
key double 
val 400 
next 12706528 

hash 2295 
key trying 
val 600 
next 12667072 

hash 657 
key Now 
val 8888 
next 0 


hash 2800 
key oh well 
val 700 
next 0 

0 
0 
0 

hash 641 
key cat 
val 77 
next 0 

0 
0 

hash 1148 
key pony 
val 100 
next 0 

0 

hash 3334 
key my oh my 
val 800 
next 0 

0 
0 
0 
0 ok

0 0 
1 11779840 
2 11537200 
3 0 
4 12290768 
5 0 
6 11836544 
7 11868544 
8 0 
9 0 
10 0 
11 11629472 
12 0 
13 0 
14 11933328 
15 0 
16 11639232 
17 0 
18 0 
19 0 
20 0 
#nodes 12 
table size 21 

0 

hash 631 
key dog 
val 6 
next 12060336 

hash 1051 
key tree 
val 300 
next 0 


hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 12091296 

hash 1579 
key build 
val 500 
next 0 

0 

hash 2211 
key double 
val 400 
next 12270608 

hash 2295 
key trying 
val 600 
next 11856032 

hash 657 
key Now 
val 8888 
next 0 


hash 2800 
key oh well 
val 700 
next 0 

0 
0 
0 

hash 641 
key cat 
val 77 
next 0 

0 
0 

hash 1148 
key pony 
val 100 
next 0 

0 

hash 3334 
key my oh my 
val 800 
next 0 

0 
0 
0 
0 ok

0 0 
1 12291360 
2 12516032 
3 0 
4 15896576 
5 0 
6 246483232 
7 16414080 
8 0 
9 0 
10 0 
11 12434032 
12 0 
13 0 
14 15821088 
15 0 
16 16646720 
17 0 
18 0 
19 0 
20 0 
#nodes 12 
table size 21 

0 

hash 631 
key dog 
val 6 
next 220645104 

hash 1051 
key tree 
val 300 
next 0 


hash 1073 
key fish 
val 200 
next 0 

0 

hash 1075 
key frog 
val 55 
next 16592672 

hash 1579 
key build 
val 500 
next 0 

0 

hash 2211 
key double 
val 400 
next 16691168 

hash 2295 
key trying 
val 600 
next 16710480 

hash 657 
key Now 
val 8888 
next 0 


hash 2800 
key oh well 
val 700 
next 0 

0 
0 
0 

hash 641 
key cat 
val 77 
next 0 

0 
0 

hash 1148 
key pony 
val 100 
next 0 

0 

hash 3334 
key my oh my 
val 800 
next 0 

0 
0 
0 
0 ok


s" cat" t2 :@ . .   -1 77 ok

s" frog" t2 :@ .  0 ok

s" dog" t2 :@ . .  -1 6 ok
s" Now" t2 :@ . . -1 8888 ok

s" Now" t2 :delete . -1 ok


[then]