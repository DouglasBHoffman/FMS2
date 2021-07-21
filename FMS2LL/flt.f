\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Feb 8, 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com
\ changed instance variable DATA name to FDATA

[undefined] floats [if] cr .( floating point required) abort [then]

[undefined] f> [if] : f> ( -- f ) ( F: r1 r2 --) f- f0< invert ; [then]

3 CONSTANT DECIMALS
1E1 DECIMALS S>D D>F F** FCONSTANT FSCALE

: f>string      ( -- ca u F: x -- )
        FSCALE F*
        F>D TUCK DABS <# DECIMALS 0 DO # LOOP [CHAR] . HOLD #S ROT SIGN #> ;

:class flt   
  1 floats bytes fdata
 :m :init ( R: r -- ) fdata f! ;m
 :m :! ( R: r -- )  fdata f! ;m
 :m :@ ( R: -- r )  fdata f@ ;m
 :m :. self :@ f. ;m \ print self
 :m := ( obj -- flag ) :@ self :@ f= ;m
 :m :> ( obj -- flag ) :@ self :@ f> ;m
 :m :write ( str -- ) locals| str |
     fdata f@ f>string str :add ;m
;class

: >flt ( -- obj ) ( F: r -- ) heap> flt ;

0 [if]
3.33e >flt value f    

0 0 >string value s    

s f :write  ok
 
s :.  3.330ok
[then]





