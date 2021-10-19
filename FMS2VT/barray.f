
:class barray <super array
 
 :m :init \ ( -- ) or if static: ( max#elems --)
    ?alloc dup  alloc? c!
    if 0 dup allocate throw data ! len !  
    else ( max#elems ) dup len ! align here swap allot data !
    then
    len @ #elems !
     1  elemSize !
     ;m
\ addr len char 
 :m :fill { c -- } data @ #elems @ c fill ;m

 :m :@elem ( addr -- elem ) c@ ;m

 :m :to ( idx -- ) ( F: elem -- )  ^elem  c! ;m
 :m :at ( idx -- ) ( F: -- elem ) ^elem  c@ ;m
 :m .elem . ;m
;class
