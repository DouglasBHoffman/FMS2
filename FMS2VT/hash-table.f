
\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Feb 8, 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com

\ require <super object

[undefined] string [if] .( requires classes array and string to be loaded) abort [then]

defer free-val

:class hash-table-node <super object
 cell bytes hash
 string key
 cell bytes val
 cell bytes next
 :m :init 0 0 key :init ;m
 :m init ( val kaddr klen -- ) \ Initialise the node with the val, key
     key :!  val !  0 next ! ;m
\ :m :free key :free ;m \ ###
 :m :free key :free val @ free-val ;m \ only use val @ <freeAll when val is a heap allocated array
 :m :key@ ( -- obj ) \ will be a string object
     key ;m
  :m :val@ ( -- val ) val @ ;m
 :m :val! ( -- val ) val ! ;m
 :m :next ( -- next-node ) next @ ;m
 :m :next! ( next-node -- ) next ! ;m
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


\ Hash collisions are handled by separate chaining with head records in the bucket array.
:class hash-table <super object
 cell bytes table  \ will contain an array object \ array of pointers to the nodes 
 cell bytes #nodes \ number of nodes
 cell bytes load \ load factor times 100
 cell bytes key-addr
 cell bytes key-len
 cell bytes last-node \ required for subclass hash-table-m
 cell bytes current-idx \ for :each
 
 :m :init  heap> array table !
    0 #nodes !
    100 load !
    3 0 do 0 table @ :add loop \ initialize with room for 3 nodes 
 ;m

: hash-iv  ( addr len -- hash ) \ from Dick Pountain JFAR Vol3 Number 3 p68
  32 min 0 swap 0 do over i + c@ i 1+ * + loop swap drop ;


 : (do-search) ( node -- flag ) dup :key@ :@ key-addr @ key-len @ compare 0= ;
 
\ idx to the table location is returned if false
 : do-search \ { -- node idx hash true | idx hash false }
    0 0 locals| hsh idx |
    key-addr @ key-len @ hash-iv dup to hsh table @ :size mod abs ( idx) dup to idx  table @ :at
    ( node-obj)
    begin
      dup if (do-search) if ( node-obj ) idx hsh true exit then then
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
    ( node) dup :@ new-size  mod abs ( idx ) new-table :^elem \ compute new table location
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
: new-node ( hash val -- new-node )
   1 #nodes +! \ increment #nodes
   heap> hash-table-node >r
   ( val ) key-addr @ key-len @ r@ init
   ( hash ) r@ :! r> ;

:m :search ( node idx hash val -- true )
      nip nip 
      ( val ) swap :val! true
   ;m

:m :insert \ { val key-addr key-len -- }
    0 0 0 0  0 locals| new-table node hsh idx val |
   key-len ! key-addr ! to val 
   do-search
   if \ already present so just update val
      val eself :search if exit then
   then
   ( idx hash ) to hsh dup to idx table @ :at
    ( node-obj) dup 0=
    if drop   \ found empty slot in table
       hsh val new-node  idx table @ :to
    else
    \ must add new node-obj to hash collision linked-list                 
      ( node-obj)  
      begin \ walk linked list to end 
        dup to node 
        :next dup 0<>
      while
      repeat drop
       \ end of linked-list, add new node there
       hsh val new-node  node :next!
    then
 
       \ lastly test for need to increase table size
       \ and do it if required
       #nodes @ table @ :size load @ 100 */ >
       if table @ :size 2* 1+ ( new-size )
          heap> array ( new-size new-table )
          2dup to new-table 0 ?do 0 new-table :add loop
          transfer then

       ;m 

\ :add is for supporting some HOFs
:m :add ( node -- )
   dup >r
   :val@ r> :key@ :@ eself :insert ;m

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

: free-node-val \ { node }
  :val@ <free ;
 
 :m :uneach 0  current-idx ! 0 last-node ! ;m

 :m :each ( -- node true | false)
 
     last-node @ dup
     if :next dup if dup last-node ! true exit
                  else drop  1 current-idx +!
                  then
     else drop
     then
    begin
     current-idx @ dup  table @ :size <
    while 
      table @ :at dup 0<>
      if dup last-node ! true exit
      else drop 1 current-idx +!
      then
    repeat drop false eself :uneach ;m

' drop is free-val \ special setup required for freeing nodes in hash-table

;class

: >hash-table ( -- obj ) heap> hash-table ;
   
0 [if]

\ note, key can be case insensitive: what is best way?
' <freeAll is free-val
.mem  

clr-mem ok


0 unFREEd pointers ok

' drop is free-val ok

hash-table t  ok ok ok

 
T is redefined ok

 
T is redefined ok




10 s" fish" t :insert  ok ok ok ok ok








.mem  
0 15219120 
1 15218880 
2 14714400 
3 15387248 
4 unFREEd pointers ok


0 12242976 
1 11592048 
2 12020864 
3 12069072 
4 unFREEd pointers ok

t :d  
0 0 
1 0 
2 14714400 
#nodes 1 
table size 3 

0 
0 

hash 1073 
key fish
val 10 
next 0 
ok

0 0 
1 0 
2 12020864 
#nodes 1 
table size 3 

0 
0 

hash 1073 
key fish
val 10 
next 0 
ok



20 s" dog" t :insert 
30 s" carp" t :insert 
40 s" cat" t :insert 
50 s" frog" t :insert 
 ok
t :free ok ok
.mem 
0 unFREEd pointers ok


 ok

s" cat" t :@ .s ( 2 ) \ 40 \ -1 ok \ 2 

 
T is redefined ok
 
T is redefined ok

t :d    
0 0 
1 13023936 
2 14779008 
3 0 
4 12969552 
5 12634896 
6 0 
#nodes 5 
table size 7 

0 

hash 631 
key dog
val 20 
next 0 


hash 1073 
key fish
val 10 
next 0 

0 

hash 641 
key cat
val 40 
next 12997136 

hash 1075 
key frog
val 50 
next 0 


hash 1083 
key carp
val 30 
next 0 

0 ok

t :free ok ok



.mem  
0 unFREEd pointers ok


0 15219120 
1 15218880 
2 14714400 
3 unFREEd pointers ok

clr-mem ok


0 0 
1 12264000 
2 178324864 
3 0 
4 11629696 
5 12592736 
6 0 
#nodes 5 
table size 7 

0 

hash 631 
key dog 
val 20 
next 0 


hash 1073 
key fish 
val 10 
next 0 

0 

hash 641 
key cat 
val 40 
next 11728544 

hash 1075 
key frog 
val 50 
next 0 


hash 1083 
key carp 
val 30 
next 0 

0 ok

[then]

