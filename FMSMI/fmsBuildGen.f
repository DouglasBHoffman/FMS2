\ fmsBuildGen.f - Build FMS with no implementation specifics

\ This build file assumes that the Forth build system has already
\ changed the working drive/directory to the FMS build directory.

\ You can use this as the basis of your application's build.


\ ======================
\ Configuration settings
\ ======================
\ These flags should be set according to the required configuration.

TRUE CONSTANT fmsDispatch?
\ If true, the dispatch table version (larger, but faster) is used.
\ For most desktop systems, true should be the default.

false CONSTANT fmsCheck?		\ -- flag
\ When true, debug code and extra error messages are compiled
\ at the expense of run-time speed. Set fmsCheck? to FALSE after
\ program is debugged

true CONSTANT fmsTest?		\ -- flag
\ True to compile and run the test harnesses.


\ ==============
\ Load the files
\ ==============

here				\ start of code

include fmsHarnGen.f		\ include the generic harness code
fmsDispatch? [if]
  include fmsDispatch.f		\ Dispatch table version
[else]
  include fmsLinked.f		\ 8 way link version
[then]
[DEFINED] macforth.picture [IF]	\ Carbon MacForth
  myfolder.include" fmsLib.f"
[ELSE]				\ gforth, VFX Forth, SwiftForth, iForth
  include fmsLib.f
[THEN]

cr
cr .fmsVer .(  is Loaded )
cr
cr ." Code takes " here swap - . ." bytes"
cr

fmsTest? [IF]
[DEFINED] macforth.picture [IF]	\ Carbon MacForth
  myfolder.include" ttester.f"
  myfolder.include" fmsTester.f"
[ELSE]				\ gforth, VFX Forth, SwiftForth, iForth
  include ttester.f
  include fmsTester.f
[THEN]
  cr
  cr .( Set fmsTest? false not to load test code )
  cr
[THEN]


\ ========
\ All done
\ ========