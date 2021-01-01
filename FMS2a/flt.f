[undefined] floats [if] cr .( floating point required) abort [then]

 [undefined] f> [if] : f> ( -- f ) ( F: r1 r2 --) f- f0< invert ; [then]

:class flt   
  1 floats bytes data
 :m :init ( R: r -- ) data f! ;m
 :m :! ( R: r -- )  data f! ;m
 :m :@ ( R: -- r )  data f@ ;m
 :m :. self :@ f. ;m \ print self
 :m := ( obj -- flag ) :@ self :@ f= ;m
 :m :> ( obj -- flag ) :@ self :@ f> ;m
;class

: >flt ( -- obj ) ( F: r -- ) heap> flt ;

