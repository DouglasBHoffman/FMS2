0 [IF]
The basic tree engine is based on an example from Marcel Hendrix posted on usenet: 
 
  * DESCRIPTION : binary-tree 
  * AUTHOR      : Marcel Hendrix 
  * LAST CHANGE : July 29, 2006, Marcel Hendrix 

        REVISION -trees Binary trees        Version 1.00 

    From: 'Algorithms' Robert Sedgewick, ISBN 0-201-06672-6, page 178 - 185. 

Tree balancing has been added, in addition to making a tree class.  
[THEN]


:class node <super object
   cell bytes left
   cell bytes right
   cell bytes nkey
   cell bytes info
   
  :m :left! ( n -- ) left ! ;m
  :m :right! ( n -- ) right ! ;m
  :m :key! ( n -- ) nkey ! ;m
  :m :info! ( n -- ) info ! ;m
  :m :left ( -- n ) left @ ;m
  :m :right ( -- n ) right @ ;m
  :m :key ( -- n ) nkey @ ;m
  :m :info ( -- n ) info @ ;m
;class



:class btree <super object
  cell bytes size
  cell bytes oc-key \ container for keys ordered-col \ ordered-col will be sorted
  cell bytes oc-info \ container for info ordered-col, ordered as per nkey oc
  node head  
  node z 
  cell bytes key-display-xt
  cell bytes info-displ-xt
  cell bytes map-xt

:m :init
    0 size !
    0 head :key!
    0 head :left!
    z head :right!
    ;m

\ -- To search for a record with nkey v, do v 'head' tree-search ( -- link ) 
\ -- An unsuccessful search returns 'z'. 
:m :search \ { v | link -- link2 true | false }
  
  head >r
  dup ( v) z :key!
  BEGIN
    dup ( v) r@ :key <  IF   r> :left >r
          ELSE r> :right >r 
          THEN
    r@ :key over ( v nkey v) =
  UNTIL drop
   r> dup z = IF drop false ELSE true THEN
   ;m

\ -- To insert a node in the tree, we just do an unsuccessful search for it, 
\ -- then hook it on in place of 'z' at the point where the search was terminated. 
\ -- When a new node whose nkey is already in the tree is inserted, it goes 
\ -- to the right of the node already in the tree. All records with nkey equal to v 
\ -- can be processed by successively setting t to tree-search(v,t). 


: (insert) \ { v link | f -- link2 }
  0 locals| f link v |
    1 size +!
    BEGIN
     link to f 
     v link :key <  IF   link :left to link
           ELSE link :right to link 
           THEN
       link z =
    UNTIL
    heap> node to link
    v link :key!
    z link :left!
    z link :right!
    v f :key < IF   link f :left!
         ELSE link f :right!
         THEN
    link ;

:m :insert \ { nkey inf -- } \ inf=info, can be anything that fits in one cell
   swap ( inf nkey ) head  (insert) ( inf link2 ) :info! ;m

: (.nodes) \ { link -- }
         >r
         r@ z = IF r> drop EXIT THEN
         r@ :key  key-display-xt @ execute  r@ :info  info-displ-xt @ execute 
         r@ :left DUP z <> IF recurse ELSE DROP THEN 
         r> :right DUP z <> IF recurse ELSE DROP THEN
         ;

:m :. \ print the nodes
     head :right  (.nodes) ;m

: (map) \ { link -- }
         >r
         r@ z = IF r> drop EXIT THEN
            r@ :info  \ get info to stack   
            map-xt @ execute  \ transform info 
            r@ :info!  \ place transformed stack item into info
         r@ :left DUP z <> IF recurse ELSE DROP THEN 
         r> :right DUP z <> IF recurse ELSE DROP THEN
         ;

:m :map ( xt -- ) \ apply xt to ( info @ ) for each node in the tree
     map-xt !
     head :right  (map) ;m

: (.sorted) \ { link -- }
         >r
         r@ z = IF r> drop EXIT THEN 
         r@ :left  recurse 
         r@ :key  key-display-xt @ execute 
         r> :right  recurse
         ;

:m :.sorted \ print sorted
    head :right  (.sorted)
         ;m

: (free) \ { link -- }
   >r
   r@ z = IF r> drop EXIT THEN
   r@ :right IF r@ :right recurse
          r@ :left recurse
          THEN
   r> <free ( cr ." free node" ) ;

: free-tree
    head :right (free)
    self :init ;
    
:m :free
    free-tree
   oc-key @ ?dup IF <free 0 oc-key ! THEN
   oc-info @ ?dup IF <free 0 oc-info ! THEN
   ;m

:m :setDisplay ( xt-key xt-info -- )
   info-displ-xt !
   key-display-xt ! ;m



: (ord-col) \ { link -- }
         >r
         r@ z = IF r> drop EXIT THEN 
         r@ :left  recurse 
         r@ :key oc-key @ :add
         r@ :info oc-info @ :add
         r> :right recurse ;

: ord-cols ( -- oc-key oc-info ) \ ordered-cols will be sorted
\   size @ heap> ordered-col oc-key !
\   size @ heap> ordered-col oc-info !
   heap> array oc-key !
   heap> array oc-info !
   head :right  (ord-col) 
   oc-key @ oc-info @
   ;

: ((balance))
  oc-key @ :size  0 ?DO I oc-key @ :at  I oc-info @ :at  self :insert
              LOOP ;


: (balance) \ { | idx odd -- }
  0 0 locals| idx odd |
  oc-key @ :size 3 < IF ((balance)) exit THEN
  oc-key @ :size 2 /mod to idx to odd
  idx oc-key @ :at ( key) idx oc-info @ :at ( info) self :insert
  idx odd IF 1+ THEN 1
           DO idx I - oc-key @ :at ( key) idx I - oc-info @ :at ( info) self :insert
              idx I + oc-key @ :at ( key) idx I + oc-info @ :at ( info) self :insert
           LOOP
   odd 0=
   IF 0 oc-key @ :at ( key)  0 oc-info @ :at ( info)  self :insert THEN ;


:  balance
     ord-cols 2drop \ write out the tree to two ordered-col's (sorted)
     free-tree    \ clear the tree
    (balance) \ re-build the tree as a balanced tree
   oc-key @ <free oc-info @ <free \ free the ordered-cols
   0 oc-key !  0 oc-info !
   ; 

\ as a side-effect delete: will also balance the tree
:m :delete \ { n -- true | false } \ n = nkey to delete, true if successful
     ord-cols 2drop \ write out the tree to two ordered-col's (sorted)
   ( n ) oc-key @ :search ( idx T | F )
   IF ( idx ) dup oc-key @ :delete
                  oc-info @ :delete
        free-tree
        (balance)
      oc-key @ <free oc-info @ <free
      0 oc-key ! 0 oc-info !
      true
    ELSE
      false
    THEN ;m

\ a side effect of size: will be to also balance the tree
:m :size ( -- size ) size @
   balance ;m  
;class





0 [if]
cr .( Testing Binary Tree - With Recursion )

: display-char ." (" 0 .R ." ) " ; 

btree b
\ ' emit b iv key-display-xt ! 

\ ' display-char b iv info-displ-xt ! 
' emit ' display-char b :setDisplay 

cr .( insert t d e r a )
char t dup b :insert 
char d dup b :insert
char e dup b :insert
char r dup b :insert
char a dup b :insert

cr .( b :. )  b :.   
b :. t(116) d(100) a(97) e(101) r(114) ok

\ b :. t(116) d(100) a(97) e(101) r(114) ok

\ t(116) d(100) a(97) e(101) r(114) 

cr .( b :size . b :. ) b size: . b :.  
b :size . b :. 
\ e(101) d(100) a(97) r(114) t(116) 

cr .( char e b :delete b :. )
T{ char e b :delete -> -1 }T
 b :. 
\ r(114) d(100) a(97) t(116) 

cr .( b :map )  b :map 
\ adrt

\ b :map adertok



b :free

btree b
[undefined] noop [if] : noop ; [then]
\ ' noop b iv key-display-xt !
\ ' drop b iv info-displ-xt !

' . ' drop b :setDisplay ok ok



char t dup b :insert
char d dup b :insert
char e dup b :insert
char r dup b :insert
char a dup b :insert
 ok

 
T{ b :. -> 116 100 97 101 114 }T
b :. 116 100 97 101 114 ok

T{ b :size . b :. -> 101 100 97 114 116 }T
b :size . b :. 5 ok \ 5 
.s ( 5 ) \ 101 \ 100 \ 97 \ 114 \ 116 ok \ 5 




T{ char e b :delete -> -1 }T
char e b :delete .s ( 1 ) \ -1 ok \ 1 

T{ b :. -> 114 100 97 116 }T
b :. ok \ 4 
.s ( 4 ) \ 114 \ 100 \ 97 \ 116 ok \ 4 

T{ b :map -> 97 100 114 116 }T
b :map ok \ 4 
.s ( 4 ) \ 97 \ 100 \ 114 \ 116 ok \ 4 


b :free ok

[then]
