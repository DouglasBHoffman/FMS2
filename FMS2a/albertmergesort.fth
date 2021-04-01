\ This meerge sort code was created by Albert Albert van der Horst
\ and posted by albert in usenet comp.lang.forth
\ It is an excellent and very fasy linked list merge sort.



\ ---------------------------------------
\ (MERGE)       \ AvdH A3dec02
\ list : sorted   ulist : unsorted   listp : list level
\ For EL1 and EL2, return EL1 and EL2 plus "el1 IS lower".
: LL< >r 2DUP r> EXECUTE ;
\ For LIST1 ( > ) LIST2 return LIST1 (>) LIST2' advanced
: FIND-END { xt }  BEGIN DUP >R @   DUP IF xt LL< 0= ELSE 0 THEN
   WHILE R> DROP REPEAT DROP R> ;
\ Merge LIST1 ( > ) LIST2.
: (MERGE) { xt } BEGIN xt FIND-END   DUP >R  DUP @ >R !
   R> R>   OVER 0= UNTIL 2DROP ;
\ Merge LIST1 and LIST2, leave merged LIST.
: MERGE dup { xt } LL< IF SWAP THEN DUP >R xt (MERGE) R> ;
\ Cut ULIST in two. Return LIST and remaining ULIST.
: SNIP >r DUP BEGIN DUP @  DUP IF r@ LL< ELSE 0 THEN
   WHILE NIP REPEAT r> drop  >R 0 SWAP ! R> ;
\ Keep on merging as long as two listp 's have the same level.
: TRY-MERGES { xt } BEGIN >R  OVER R@ =
   WHILE NIP xt MERGE R> 1+ REPEAT R> ;
\ Expand zero, ulist into zero list, level .... list, level
: EXPAND { xt }  BEGIN xt SNIP >R 1 xt TRY-MERGES R> DUP WHILE REPEAT DROP ;
\ Keep on merging list-level pairs until end-sentinel.
: SHRINK >r DROP BEGIN OVER WHILE NIP r@ MERGE REPEAT r> drop ;
\ For linked LIST compare XT, leave a sorted LIST1.
: MERGE-SORT  >r   0 SWAP r@ EXPAND r> SHRINK NIP ;
\ ---------------------------------------




\ The stack diagram of MERGE-SORT is ( list1 comparison-XT -- list2 )
: ll-nodeH ( n -- node) 2 cells allocate throw >r 0 r@ ! r@ cell+ ! r> ;
: linkH ( node n -- node) ll-nodeH tuck ! ;
: ll-print ( node -- ) cr dup cell+ @ . cr
  begin @ dup while dup cell+ @ . cr repeat drop ;
: ll-size ( node -- ) 1 begin swap @ dup while swap 1+
  repeat drop ;

0 [if]

: ints->? ( adr1 adr2 -- flag) \ sort integers -> descending 
  cell+ @ swap cell+ @ < ;
: build-linkedlistINT ( size -- )
  1000000 choose ll-nodeH swap
  1 do 100000 choose linkH loop  ;

stopincluding


 
 50000 build-linkedlistINT . 246173920 ok


246173920 timer-reset ' ints->? MERGE-SORT .elapsed    12.4 msecok \ 1 
. 245744704 ok


(( 
 15.9 msec ok
 15.9 msec ok
 15.9 msec ok
 15.9 msec ok
 15.9 msec ok
 15.9 msec ok
 16.9 msec ok
 16.0 msec ok
 16.1 msec ok
 15.9 msec ok
 ))

 
(( 50,000 results:
 15.8 msec ok
 14.7 msec ok
 14.7 msec ok
 14.6 msec ok
 14.6 msec ok
 14.6 msec ok
 14.6 msec ok
 14.6 msec ok
 15.1 msec ok
 15.9 msec ok
 ))
 
stopincluding
timer-reset list ' ints-<? MERGE-SORT .elapsed \   14.9 msecok \ 1 

. 12217888 ok


. 1261632 ok

. 2050416 ok


timer-reset head ' ints-<? MERGE-SORT .elapsed \  15.8 msecok   11.9 msecok \ 1  12.0 msecok \ 1 

value ll 
LL is redefined ok





: d cr . ; ok \ 1 
. 1646632 ok

\ apply xt to each data elem in linked-list
 ok
 ok

1646632 ' d walk 
50 ok
[then]