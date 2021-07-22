\ fmsHarnVfx.f - VFX Forth harness

\ This is a VFX Forth harness.

: fmsBuild$ \ -- caddr len
\ Return the FMS build, generic or implementation specifific.
  s" (VFX Forth)"  ;

: LINK  ( addr -- )   HERE  OVER @ ,  SWAP ! ;
\ : RESERVE  ( n -- ) \ now defined in file fmsDispatch.f
\   HERE OVER ALLOT ( n addr) SWAP ERASE ;

: lowerCase? ( char -- flag ) \ flag is true if char is lower case
  [CHAR] a [ CHAR z 1+ ] LITERAL WITHIN ;

\ Converts lower-case characters to upper case, modifying the contents
\ starting at addr for cnt chars
: to-upper   ( addr cnt -- ) upper  ;

: ?MEMERR  ( ior -- )  ABORT" Memory allocation error" ;
comp:  discard-sinline doLayAbsCall  ;

40 CONSTANT maxnameSize \ ( in aus) set this to a large enough size for your Forth

: PL POSTPONE LITERAL ;

\ cell +user currobj \ already in VFX kernel

\ : [self] \ -- optr
\   currobj @
\ ;

: ^base \ -- optr
  currobj @
;

\ : setSelf \ optr --
\   currobj !
\ ;

: set^base \ optr --
  currobj !
;

\ : EXECUTE-METHOD  ( ^obj xt -- )
\   currobj @ >R  SWAP ( xt ^obj ) currobj !  EXECUTE  R> currobj !  ;

\ : EXECUTE-METHOD-FAST  ( xt ^obj -- ) \ eliminates a runtime SWAP
\   currobj @ >R ( xt ^obj ) currobj !  EXECUTE  R> currobj !  ;

0 VALUE lastOffset

\ slowest
\ the offset here was obtained from the dispatch table via w@
: EXECUTE-METHOD  ( ^obj xt offset -- )
   currobj @  >R ( ^obj xt offset )  DUP
   TO lastOffset
   ROT ( xt offset ^obj )
   +  currobj !  EXECUTE  R>
   currobj ! ;

\ faster version
\ can only use when all 3 parameters are known at compile-time
\ eliminates a run-time rot
: EXECUTE-METHOD'  ( xt ^obj offset -- )
   currobj @  >R ( ^obj xt offset )  DUP
   TO lastOffset
   +  currobj !   EXECUTE  R>
   currobj ! ; 

 \ faster yet
 \ no offset to add, but must record that it was zero
: EXECUTE-METHOD''  ( xt ^obj -- )
   currobj @  >R
   0 TO lastOffset
     currobj !   EXECUTE
   R> currobj ! ; 

 \ fastest
 \ no need to maintain lastOffset
: EXECUTE-METHOD'''  ( xt ^obj -- )
   currobj @  >R
     currobj !   EXECUTE
   R> currobj ! ; 

\ : HASH-IVAR  ( addr len -- n ) \ now defined in file fmsDispatch.f
\   TUCK  bounds
\   ?DO  6 LSHIFT  I C@ 32 OR XOR  LOOP
\   DUP 0< IF EXIT THEN  INVERT ;
