\ fmsBuildVfx.f - Build FMS for VFX Forth (Win/Lin/Mac)

\ You can use this as the basis of your application's build.


\ ======================
\ Configuration settings
\ ======================
\ These flags should be set according to the required configuration.

true constant fmsDispatch? \ -- flag
\ If true, the dispatch table version (larger, but faster) is used.
\ For most desktop systems, true should be the default.

true CONSTANT fmsCheck?  \ -- flag  ( was errorCheck )
\ When true, debug code and extra error messages are compiled
\ at the expense of run-time speed. Set fmsCheck? to FALSE after
\ program is debugged

true constant fmsTest?  \ -- flag
\ True to compile and run the test harnesses.


\ ==============
\ Load the files
\ ==============

here     \ start of code

  include %idir%/fmsHarnVfx.f  \ include the Vfx harness code
fmsDispatch? [if]
  include %idir%/fmsDispatch.f  \ Dispatch table version
[else]
.( 8 way link version Does not exist for Multiple Inheritance )
[then]
  include %idir%/fmsLib.f  \ library

: mdis  \ "class" "method" --
  mxt disasm/f  ;

cr
cr .fmsVer .(  is Loaded )
cr
cr ." Code takes " here swap - . ." bytes"
cr

fmsTest? [if]
  include %idir%/ttester.f
  include %idir%/fmsTester.f
  cr
  cr .( Set fmsTest? false not to load test code )
  cr
[then]


\ ========
\ All done
\ ========
