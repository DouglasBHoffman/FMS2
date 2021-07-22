\ fmsHarnGen.f - generic tools for all Forths

\ This is a generic harness that should work for all ANS Forths.
\ You can use this as the basis of an implementation-specific
\ optimised harness.

: fmsBuild$	\ -- caddr len
\ Return the FMS build, generic or implementation specifific.
  s" (generic)"  ;

[UNDEFINED] CELL [IF] 1 CELLS CONSTANT CELL [THEN]

: RESERVE  ( n -- )  HERE OVER ALLOT ( n addr) SWAP ERASE ;

\ Build link to list head at addr
: LINK  ( addr -- )   HERE  OVER @ ,  SWAP ! ;

: lowerCase? ( char -- flag ) \ flag is true if char is lower case
  [CHAR] a [ CHAR z 1+ ] LITERAL WITHIN ;

\ Converts lower-case characters to upper case, modifying the contents
\ starting at addr for cnt chars
: to-upper   ( addr cnt -- )
 OVER \ addr cnt addr
 + SWAP  \ cnt+addr addr
 ?DO I C@ DUP
  lowerCase?
  IF 32 - I C!
  ELSE DROP
  THEN
 LOOP ;

: ?MEMERR  ( ior -- )  ABORT" Memory allocation error" ;

40 CONSTANT maxnameSize \ ( in aus) set this to a large enough size for your Forth

: PL POSTPONE LITERAL ;

0 VALUE [SELF]	\ -- optr

: setSelf	\ optr --
  s" to [self]" evaluate
; immediate

: EXECUTE-METHOD  ( ^obj xt -- )
 [SELF] >R SWAP ( xt ^obj ) TO [SELF]  EXECUTE R>  TO [SELF] ;

: EXECUTE-METHOD-FAST  ( xt ^obj -- ) \ eliminates a runtime SWAP
 [SELF] >R ( xt ^obj ) TO [SELF]  EXECUTE R>  TO [SELF] ;

: HASH-IVAR  ( addr len -- n ) TUCK OVER + SWAP ?DO  6 LSHIFT  I C@ 32 OR XOR  LOOP
  DUP 0< IF EXIT THEN  INVERT ;
