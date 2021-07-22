\ 01/24/12 dbh
\ "<SUPER OBJECT" or "SUPER{ OBJECT }" declaration is now optional, i.e.,
\     the default superclass is OBJECT if <super or super{ ... } is omitted.
\ added dict> for nameless dictionary object creation
\ removed STATE everywhere except for one place: the dot parser (100% backward compatible)
\ optimized versions of EXECUTE-METHOD used where possible
\ An optional "Dot Parser" methodless ivar access syntax is provided
\ factored some definitions

\ fixed nested primitive ivars bug in ITRAV
\ fixed an edge condition bug in SUPER
\ fixed an edge condition bug in SELF
\ multiple inheritance is supported, 100% backward compatibility with SI FMS
\ object-message syntax
\ dispatch tables are used for dynamic method binding
\ All messages to SELF are early-bound, use [SELF] for late

\ The method compiler is gone.  Wordlists are used instead.

\ message names must end with colon(:)

\ This extension has an environmental dependency in that it requires
\ more than eight wordlists:  one wordlist for each class

\ This extension has an environmental dependency in that it requires
\ more than eight wordlists for set-order

\ This extension has an environmental dependency.  It needs two non-standard words:
\ uw in stack effects below is an unsigned integer with maximum value of one-half cell
\ w! ( uw addr -- ) \ Stores the (n-bit)/2 value w at addr.
\ w@ ( addr -- uw ) \ Returns the (n-bit)/2 value at addr.  Does not sign extend w to a full cell.


DECIMAL

FORTH-WORDLIST  SET-CURRENT

: fmsVer$ \ -- caddr len
\ Return the FMS version, generic or implementation specifific.
  s" FMS version MI41b, dispatch"  ;

: .FMSver \ --
\ Display the FMS version and build
  fmsVer$ type space fmsBuild$ type  ;

WORDLIST  CONSTANT  nclass               \ create separate wordlist ***
nclass SET-CURRENT                       \ for class def'ns
GET-ORDER  nclass  SWAP 1+  SET-ORDER    \ make nclass findable

\ set fmsCheck? to FALSE after program is debugged
\ TRUE CONSTANT fmsCheck? \ now in file fmsBuidXXX.f

\ maxnameSize now in file fmsHarnXXX.f
\ 40 CONSTANT maxnameSize \ ( in aus) set this to a large enough size for your Forth

[DEFINED] .signon [IF] ( iForth  INCLUDE C:\iForth-4.0.6-eval\dfwforth\include\miscutil.frt )  : w@ 16b@ ; : w! 16b! ;   [THEN]
[UNDEFINED] CELL [IF] 1 CELLS CONSTANT CELL [THEN]
[UNDEFINED] BOUNDS [IF] : BOUNDS ( addr len -- addr+len addr ) OVER + SWAP ; [THEN]
\ : ?MEMERR  ( ior -- ) \ now in file fmsHarnXXX.f
\     ABORT" Memory allocation error" ;
\ : PL POSTPONE LITERAL ; \ now in file fmsHarnXXX.f
: RESERVE  ( n -- )  HERE OVER ALLOT ( n addr) SWAP ERASE ;

: HASH-IVAR  ( addr len -- n ) TUCK BOUNDS ?DO  6 LSHIFT  I C@ 32 OR XOR  LOOP
  DUP 0< IF EXIT THEN  INVERT ;

\ Converts lower-case characters to upper case, modifying the contents
\ starting at addr for cnt chars
\ : to-upper   ( addr cnt -- ) \ now in file fmsHarnXXX.f
\  OVER \ addr cnt addr
\  + SWAP  \ cnt+addr addr
\  ?DO I C@ DUP
\   lowerCase?
\   IF 32 - I C!
\   ELSE DROP
\   THEN
\  LOOP ;

\ 0 VALUE ^base \ defined in file fmsHarnXXX.f
0 VALUE newObject \ object being created

\ ^class contains the address of cell 0 below.
\ Outside of a class definition the ^class can be obtained
\ by executing ' <classname> >BODY

0 VALUE ^class

\ cell 0 contains a pointer to the method xt dispatch table
: IFA ( ^class -- addr_ifa )    CELL  + ; \ ivar dict Latest field
: DFA ( ^class -- addr_dfa )  [ 2 CELLS ] LITERAL + ; \ datalen of named ivars
: XFA ( ^class -- addr_xfa )  [ 3 CELLS ] LITERAL + ; \  elem width for indexed area, <= 0 if not indexed
: SFA ( ^class -- addr_sfa )  [ 4 CELLS ] LITERAL + ; \ superclass ptr field
: WIDA ( ^class -- addr_wid ) [ 5 CELLS ] LITERAL + ; \ wid field
: TAG ( ^class -- addr_tag )  [ 6 CELLS ] LITERAL + ; \ class tag field
: ClassName ( ^class -- $ptr ) [ 7 CELLS ] LITERAL + ; \ class name (all uc)

8 CELLS maxnameSize + CONSTANT classSize

CREATE classTag  \ contents of tag field for valid class

: ?isClass  ( pfa -- f )  \ is this a valid class?
 TAG @ classTag = ;

: @width  ( ^class -- elWidth )  \ return the indexed element width for a class
  XFA @ ; 

: classAllot  ( n -- ) ^class DFA +! ;

\ ========================= begin code unique to dispatch table ===============
: badMessage  TRUE ABORT" message not understood" THROW ;

: notUnderStood 0 TO ^class badMessage ;

 \ only used to error check
: >xt ( SelId ^dispatchTable -- xt )  \ error check
    2DUP @ ( SelId ^dispatchTable SelId maxSelID )
    > IF   badMessage THEN
   + @ ;

\ ***** heap table accessing
\ the heap heap table is a temporary table that only exists during the
\ definition of a new class.  At the end of the class definition the
\ contents of the heap table are combined with the superclass table
\ to construct the final dispatch table that is allotted in the dictionary.

0 VALUE heapTable \ will be an allocated pointer
0 VALUE heapTableSize \ size in bytes

: rsize ( n -- 1.5*n ) cells dup 2/ + ;

1 rsize CONSTANT recordSize \ in aus, will be 6 for a 32-bit system
: initHeapTable ( n -- ) \ n is the initial number of records
  rsize DUP ALLOCATE ?MEMERR  \ allocate 1.5 cells for each method record
                              \ 1 cell for the xt, 0.5 cell for the MI class offset
  TO heapTable TO heapTableSize
  heapTable heapTableSize ERASE ; \ initialize all cells to zero
  
: freeHeapTable
  heapTable FREE ?MEMERR ;

: hTableSize ( -- n ) heapTableSize CELL dup 2/ + / ; \ n= number of records

: resizeHeapTable ( n -- ) \ n is the new number of records
  rsize DUP heapTable SWAP RESIZE ?MEMERR
  TO heapTable TO heapTableSize ;

: records ( n -- recordSize*n ) recordSize * ;
: XThElemAddr ( Idx -- addr) records  heapTable + ; \ Idx is record#
: OffsethElemAddr ( Idx -- addr) XThElemAddr cell+ ; \ Idx is record#

: XTtoHeapTable ( xt Idx -- ) XThElemAddr ! ;
: OffsettoHeapTable ( offset Idx -- ) OffsethElemAddr w! ; \ offset is an uw ( half-cell maximum )

: XTatHeapTable ( Idx -- xt ) XThElemAddr @ ;
: OffsetatHeapTable ( Idx -- offset ) OffsethElemAddr w@ ; \ offset is an uw ( half-cell maximum )

: incrHeapTable ( -- ) \ increase size by 1 record
  hTableSize 1+ resizeHeapTable
  0 hTableSize 1-  XTtoHeapTable \ zero the record
  0 hTableSize 1- OffsettoHeapTable ;

\ ***** dispatch table accessing

: dispTableSize ( ^class -- #records) \ not counting record(0), i.e. 1-based
   @ \ ^dispatchTable
   dup 0= IF exit THEN
   @ \ dispatchTable recordXT(0) = table size in aus
   recordSize / ;

0 VALUE ^nway

\ return largest superclass dispatch table size
: largestSuperTableSize ( -- #records )
  ^nway cell+ 0 locals| LtableSize addr |
  ^nway @ 0 ?DO  addr @ ( ^supclassi )
       dispTableSize LtableSize max to LtableSize
       addr cell+ cell+ to addr
       LOOP LtableSize ;

\ dispatch table records are a 1-based array of 1.5cell ( often 6 byte) records
: XTdisTable ( idx ^class -- addr ) \ address of dispatchtable record n
  @ >r ( idx ) records r> + ;
: OffsetdisTable ( idx ^class -- addr ) \ address of dispatchtable record n
  XTdisTable cell+ ;

: XTtoDisTable ( xt Idx ^class -- )  
  XTdisTable ! ;
: OffsettoDisTable ( offset Idx ^class -- ) \ offset is an uw ( half-cell maximum )
  OffsetdisTable w! ;

: XTatDisTable ( idx ^class -- xt )  
  XTdisTable @ ;
: OffsetatDisTable ( idx ^class -- offset ) \ offset is an uw ( half-cell maximum ) 
  OffsetdisTable w@ ;

0 value record#
0 value curSupClass
0 value current-cum-offset

\ FindSuperclMethod searches sequentially up the MI superclass chain
\ But it should search recursively shoudn't it?  NO!  All methods will have been
\  migrated down the inheritance chains to these primary superclasses.
: FindSuperclMethod ( record# -- true | false ) \ true if found
 to record#
 0 to current-cum-offset
 ^nway cell+ locals| addr |
 ^nway @ 0 ?DO addr @ ( ^supclassi ) to curSupClass
                addr cell+ @ to current-cum-offset  \ critical step 
     record#   curSupClass dispTableSize 1+  <
      IF \ this table is large enough to look in
         record# curSupClass XTatDisTable ( xt )
         ['] notUnderStood <> 
         IF \ we found it
            unloop true EXIT THEN
      THEN
       addr cell+ cell+ to addr
      LOOP ( we didn't find it ) false ;

: curSupClass-offset ( ^class -- offset ) \ get offset from ^nway list
 ^nway cell+ locals| addr ^cls |  \ step through addr of each superclass
                                  \ until a match is found
 ^nway @ 0 ?DO addr @  ^cls  =  IF addr cell+ @ unloop exit THEN
      addr cell+ cell+ to addr \ step to next superclass
      LOOP true abort" didn't find ^class in curSupClass-offset" ;

: AdvanceSuperclMethodXTs \ from multiple supTables to single heapTable as necessary
  \ also set the offset values in the XT records of the dispatch table
 hTableSize 1
 DO I XTatHeapTable 0=
  IF \ we have a zero record, so check superclasses
     I FindSuperclMethod
     IF 
      \ transfer xt(i) and offset(i) from superclass table to heap table
       I curSupClass XTatDisTable ( xt) I XTtoHeapTable
     \ Now add the offset from the nway list for the given superclass
     \ to the offset from the superclass dispatch table for the given message,
     \ and place that combined offset in the dispatch table for the
     \ new class being defined.  This is important to keep straight.
     i ( message-idx ) curSupClass OffsetatDisTable ( offset-from-message )
     curSupClass curSupClass-offset ( offset-from-nway ) + I OffsettoHeapTable
     ELSE
       ['] notUnderStood I XTtoHeapTable  0 I OffsettoHeapTable
     THEN
   ELSE \ we don't have a zero record so
     \ this method is in the current class definition, just set the offset
     \ based on the current nway offset in the first superclass
     ^nway cell+ cell+ @ ( offset ) i OffsettoHeapTable
  THEN
 LOOP ;

: transferMethodXTs  \ transfer from heap table to newly allotted table
  \ covert 0 xts into notUnderStood xts
  hTableSize 1 \ for cells# 1 through heap table size
  ?DO I XTatHeapTable ( xt) \ must use ?DO
     DUP 0= IF DROP ['] notUnderStood THEN   
     I ^class XTtoDisTable
     
     i OffsetatHeapTable ( offset )
     i ^class OffsettoDisTable
  LOOP
      hTableSize 1- records ( aus ) 0 ^class XTtoDisTable ; \ store table max offset ( aus ) in cell zero

\ ========================= end code unique to dispatch table ===============

 \ lastOffset is needed to adjust ^base in [SELF] and indexed words

0 [IF] \ these words are now defined in file fmsHarnXXX.f

0 VALUE lastOffset

\ slowest
\ the offset here was obtained from the dispatch table via w@
: EXECUTE-METHOD  ( ^obj xt offset -- )
   ^base  >R ( ^obj xt offset )  DUP
   TO lastOffset
   ROT ( xt offset ^obj )
   +  TO ^base  EXECUTE  R>
   TO ^base ;

\ faster version
\ can only use when all 3 parameters are known at compile-time
\ eliminates a run-time rot
: EXECUTE-METHOD'  ( xt ^obj offset -- )
   ^base  >R ( ^obj xt offset )  DUP
   TO lastOffset
   +  TO ^base   EXECUTE  R>
   TO ^base ; 

 \ faster yet
 \ no offset to add, but must record that it was zero
: EXECUTE-METHOD''  ( xt ^obj -- )
   ^base  >R
   0 TO lastOffset
     TO ^base   EXECUTE
   R> TO ^base ; 

 \ fastest
 \ no need to maintain lastOffset
: EXECUTE-METHOD'''  ( xt ^obj -- )
   ^base  >R
     TO ^base   EXECUTE
   R> TO ^base ; 
[THEN]

: >SelID \ input stream: ( "spaces<messagename>" -- SelID )
  ' >BODY @ ;

HERE CONSTANT selectorTag  \ for marking words as selectors

\ true if next word in input stream is a selector
\ other stack items are provided for use by getSelect
: ?isSel  ( -- in addr true | in pfa/str false )
           \ input stream: "spaces<name>"
   >IN @ BL WORD FIND
   IF
     ( in xt ) >BODY ( in pfa )
     DUP
     IF ( in pfa )
       DUP ( in pfa pfa )
       CELL+ @ selectorTag = ( in pfa flag )
     ELSE 
       ( in pfa ) FALSE
     THEN
   ELSE
     ( in str ) FALSE
   THEN ;

: scanForMessage ( -- flag ) \ true if a message follows
  ?isSel NIP SWAP >IN ! ;

-1 [IF]  \ option to early bind to named dictionary objects if you are willing to
        \ accept STATE
: ?execute-method \ Interpreting: ( ^obj -- ^obj )
    \ Compiling:    ( ^obj "<message:>" -- )  early bind message send to obj
    \     or        ( ^obj "<non-message>" -- ^obj ) just leave ^obj 
  STATE @
  IF \ compiling
         ( ^obj )
          scanForMessage
          IF \ early bind to following message
           >SelID \ ^obj selID 
           OVER CELL - @  \ ^obj selID ^dispatch
           + \ ^obj addr-xt
           SWAP >R
           DUP \ addr-xt addr-xt
           @   \ addr-xt xt
           PL  \ addr-xt
           CELL+ W@ \ offset
           R> \ offset ^obj
           PL PL POSTPONE EXECUTE-METHOD'
          ELSE
            \ just compile the ^obj as a literal
            PL
          THEN
  THEN ; 

\ The runtime action of an object is to return the address of its data,
\ which is one cell after the PFA. The PFA contains the address of the
\ first cell of the method dispatch table for the class of that object.
\ If compiling then scan ahead in the input stream.  If the scan shows that
\ a message follows the object's name then early bind to that message.
\ If no message directly follows then just leave the address of the object.
: (Obj) \ Compile time ( "spaces<name>" -- )
          CREATE  IMMEDIATE
        \ Run time: ( -- ^obj )
        \   or execute: ^obj <message:>
          DOES>
          CELL+ ?execute-method ; 
[ELSE]

: (Obj) \ Compile time ( "spaces<name>" -- )
          CREATE  \ IMMEDIATE
        \ Run time: ( -- ^obj )
        \   or execute: ^obj <message:>
          DOES>
          CELL+ ; 
[THEN]


FORTH-WORDLIST  SET-CURRENT

\ Force an early bind when you know the class. Use with care.
\ compile-time-only
: CLASS_AS> \ Compile time: ( -- )
           \ Input stream: "<className>" "<messageName>"
            \ Run time ( ^obj -- )
\  STATE @ 0= ABORT" CLASS_AS> is a compile-time-only word"
  ' >BODY DUP ?isClass 0= ABORT" CLASS_AS> not followed by a class name"
  @ \ ^dispatchTable )
  scanForMessage 0= ABORT" CLASS_AS> classname not followed by a message"
  >SelID \ ^dispatchTable SelID )
  + \ addr-xt
  DUP \ addr-xt addr-xt
  CELL+ w@  \ addr-xt offset
  SWAP @  \ offset xt
  PL PL POSTPONE EXECUTE-METHOD
  ; IMMEDIATE

nclass SET-CURRENT \ ***

\ Wrap catch so that it preserves the current object
[DEFINED] CATCH [IF]
: CATCH  ( -- n )  ^base >R   CATCH   R> set^base ;
[THEN]
\ =====================================================================
\ An instance variable record consists of five cell-sized fields.
\ 
\     Offset   Name      Description
\     ------   ----      ---------------------------------------
\        0     link      points to link of next ivar in chain
\        1     name      32-bit hash value of name
\        2     ^class     pointer to class for this ivar
\        3     offset    offset in object to start of this ivar data
\        4     #elems    number of indexed elements if indexed
\        5     rec?      is this ivar a record?
\
\ The IFA field of a class points to the latest ivar link-addr.
\ =====================================================================

\ ivar Linked List item access
: @class ( link-addr -- ^class )    [ 2 cells ] LITERAL + @ ; 
: @IvarOffs ( link-addr -- ^class ) [ 3 cells ] LITERAL + @ ; 
: @IvarElems ( ivar -- #elems )     [ 4 CELLS ] LITERAL + @ ;
: @IvarRec? ( ivar -- rec? )        [ 5 CELLS ] LITERAL + @ ;

CREATE ^Self 0 ,

CREATE Meta classSize RESERVE
^Self  Meta IFA ! \ latest ivar
classTag Meta TAG ! \ class tag

CREATE scan$ maxnameSize ALLOT

: move$ ( src$ptr\dest$ptr --) \ copy src to dest, dest must be long enough
  OVER C@ 1+ MOVE ;

: do-scan ( $ptr -- $ptr ) \ always converts to upper case
  DUP >IN @ BL WORD ROT move$ >IN ! 
  DUP COUNT to-upper ;

0 VALUE ^objectClass  \ will contain ^class for class object

: #nways ( ^class -- n )
  sfa @ @ ;

: build-search-order \ ( widn ... wid1 n ^cls -- widm ... wid1 m )
  LOCALS| ^cls |
  ^cls wida @  \ get the wid for this class
  SWAP 1+      \ add it to the search order build
  \ move on to ^cls's primary superclass(es)
  ^cls #nways 0 DO \ #nways will always be 1 or greater
             ^cls sfa @ CELL+ i 2* CELLS + @ ( ith primary superclass )
             DUP ^objectClass <>
                IF ( ^supclassi ) DUP >R RECURSE
                   R> wida @ \ get the wid for this class
                   SWAP 1+   \ add it to the search order build
                ELSE DROP
                THEN
           LOOP ;

\ =====================================================================
\ SUPER-IVAR-FIND traverses the tree of multiply inherited superclasses
\ in a class, searchinging for the given hashed ivar name,
\ returning the ivar's offset if the ivar name is found.
\ just look at each ivar name in one class, given that class's IFA link entry address

: IVAR-FIND ( link-addr ivname offset -- offset ^class true | false )
              LOCALS| offset ivname |
              BEGIN
              ( link-addr )
              DUP CELL+ @
              ivname = IF \ found it
                         ( link-addr ) DUP @IvarOffs ( link-offset )
                         offset + ( link-addr ivar-offset )
                         SWAP @class ( ivar-offset ivar-class )
                         TRUE EXIT \ stop thread here because we found the ivar
                       THEN
              \ didn't find it yet, so keep going
               ( link-addr ) 
              @ DUP \ next-link-addr next-link-addr
              WHILE \ stop thread if next-link-addr = 0
              REPEAT ( 0 ) \ return 0 and stop thread here
              ;

: SUPER-IVAR-FIND  \ { ivar-name ^cls offset -- offset ^class true | false } \ ivar-name is the 32-bit hashed name of the ivar to search for
   0 LOCALS| temp offset ^cls ivname |
  ^cls #nways 0 \ #nways will always be 1 or greater
         DO
            \ first look in the IFA linked-list ivars for this class
            ^cls ifa @ 0<> \ but only look if this class *has* any ivars
            IF \ yes, there is at least one ivar
            
             ^cls ifa @ ( link-addr ) ivname offset IVAR-FIND
             IF \ we found it
               TRUE UNLOOP EXIT THEN \ stop thread here
         THEN
         \ didn't find it, so move on to next primary superclass
         ^cls sfa @ CELL+ i 2* cells + dup to temp @ ( ith primary superclass )
              DUP ^objectClass <> \ stop this subthread if ^class=OBJECT because OBJECT has no ivars
            IF ( ^cls ) \ ith primary superclass 
              ivname  SWAP  ( ^cls sfa @ CELL+ CELL+ i 2* CELLS +) temp cell+ @ ( ith cumulative offset )
                  offset +
                 \ recurse into the primary superclasses of this superclass
                 RECURSE
                 \ return here after this recurse thread gets stopped
                 ( offset ^class true | false )
                 IF TRUE UNLOOP EXIT \ stop thread here because we found the ivar
                 THEN
            ELSE DROP
            THEN  
         LOOP 0 ; \ stop thread
        
\ =====================================================================

: ?execute-method-ivar ( addr0 -- ) \ from DOES> action of ivar
    \ input stream:    ( "<message:>" -- )  early bind message send to ivar if a message directly follows ivar name
    \     or        ( "<non-message>" -- ^ivar ) just leave ^ivar if a message does not directly follow
          @ ( ivar-hashName ) ^class 0 SUPER-IVAR-FIND
          IF ( offset ^class )
            over IF \ offset is non-zero
                scanForMessage 
                IF  \ early bind to following message
                   >SelID ( offset ^ivar-class selID )
                   SWAP @ ( offset selID ^dispatch ) + ( offset addr) dup >R @ ( offset xt )
                   PL ( offset )
                   POSTPONE ^base PL POSTPONE + ( ^obj )
                   R> CELL+ w@ ( offset ) ?DUP IF PL POSTPONE EXECUTE-METHOD'
                                               ELSE  POSTPONE EXECUTE-METHOD''
                                               THEN
                ELSE  \ just leave ^ivar       
                 DROP ( offset )
                 PL POSTPONE ^base POSTPONE +
                THEN
           ELSE \ offset is zero, so optimize
             nip \ get rid of 0
                scanForMessage 
                IF  \ early bind to following message
                   >SelID ( ^ivar-class selID )
                   SWAP @ ( selID ^dispatch ) + ( addr) dup >R @ ( xt )
                   PL 
                   POSTPONE ^base ( ^obj )
                   R> CELL+ w@ ( offset ) ?DUP IF PL POSTPONE EXECUTE-METHOD'
                                               ELSE  POSTPONE EXECUTE-METHOD'''
                                               THEN
                ELSE  \ just leave ^ivar
                 DROP
                 POSTPONE ^base
                THEN           
           
           THEN
          ELSE -1 ABORT" ivar name not found"
          THEN ;

: ivar  \ Compile time: ( ivar-hashName -- )
         \ Input stream: ( "spaces<name>" -- ) \ the name of the ivar
          CREATE IMMEDIATE ( ivar-hashName ) ,
          DOES> ( addr0 )
          ?execute-method-ivar ; 

0 VALUE rec?
: rec{ TRUE TO rec? ;
: }rec FALSE TO rec? ;

: <Var ( #elems ^ivar-Class | ^ivar-Class -- )
      \ Input stream: "spaces<ivar-name>" 
  >IN @ BL WORD COUNT HASH-IVAR DUP >R    \ get hash value of name = ivar-hashName
  SWAP >IN !   \ restore input stream location
  ALIGN ^Class IFA LINK ,   \ store link and hashed name
  DUP ,     \ store ivar-class
  rec? 0= IF
     CELL classAllot \ allow for dispatch table ptr only if not a RECORD
  THEN
  ^class DFA @ ,    \ offset to ivar data
     dup @width dup
     IF rot dup ,  * cell+  \ #elems, cell for idx-hdr
     ELSE 0 , \ #elems = 0
     THEN
     rec? ,  \ store RECORD status
  swap DFA @ +  classAllot  \ Account for named ivar lengths
  ^class wida @ SET-CURRENT
   R> ( ivar-hashName ) ivar \ create a name = ivar-name in the wordlist for this class
  FORTH-WORDLIST SET-CURRENT ;

\ given an object and a selectorID, send the corresponding message (late bound)
\ to the object
fmsCheck?
[IF]
: Send ( ^obj SelID -- )
   OVER \ ^obj SelID ^obj
   CELL -  @ \ ^obj SelID ^dispatchTable
   2dup      \ ^obj SelID ^dispatchTable SelID ^dispatchTable
   >xt       \ ^obj SelID ^dispatchTable xt   >xt performs the SelID validity check
   >R
   +         \ ^obj addr-xt
   CELL+ w@  \ ^obj offset
   R>    \ ^obj offset xt
   swap
   EXECUTE-METHOD ; \ ^obj offset xt EXECUTE-METHOD
[ELSE]
: Send ( ^obj SelID -- )
   POSTPONE OVER \ ^obj SelID ^obj
   POSTPONE CELL POSTPONE -  POSTPONE @ \ ^obj SelID ^dispatchTable
   POSTPONE +         \ ^obj addr-xt
   POSTPONE DUP       \ ^obj addr-xt addr-xt
   POSTPONE @         \ ^obj addr-xt xt
   POSTPONE SWAP POSTPONE CELL+ POSTPONE w@ \  ^obj xt offset
   POSTPONE EXECUTE-METHOD ; IMMEDIATE \ ^obj xt offset EXECUTE-METHOD
[THEN]

\ **** begin init: code

0 VALUE (init:) \ will contain init: SelID

: InitIvar  ( ivar offset -- )
 OVER @IvarOffs + newObject +   ( ivar addr )
 (init:)  \ ivar addr SelID
 ROT      \ addr SelID ivar
 @class   \ addr SelID ^class
 @        \ addr SelID ^dispatchTable 
 +        \ addr addr-xt
 DUP      \ addr addr-xt addr-xt
 @        \ addr addr-xt xt
 SWAP
 CELL+ w@ \ addr xt offset
\ EXECUTE-METHOD ;
 ?DUP IF EXECUTE-METHOD ELSE SWAP EXECUTE-METHOD''' THEN ;

: Init  ( -- )  \ implicitly send the init: message to the newly instantiated newObject
  newObject ( ^obj ) (init:)  ( ^obj SelID ) Send ; 

\ =====================================================================
\ SUPER-ITRAV traverses the tree of multiply inherited superclasses
\ in a class, and any nested ivar definitions, building the necessary
\ dispatch table headers.

DEFER SUPER-ITRAV \ { ^cls offset -- } \ for recursion from ITRAV

: ITRAV ( link-addr offset -- )
              >R  \ offset to R
              BEGIN
              ( link-addr )
              dup 0 <>
              WHILE
              dup \ link-addr link-addr              
              @class \ link-addr ^class-link
              dup ^objectClass <>
              IF
              ( link-addr ^class-link ) over @IvarOffs R@ +
               SUPER-ITRAV 
             \ return here after this SUPER-ITRAV thread gets stopped
              ( link-addr )
                 dup @class \ link-addr ^class-link
                over @IvarOffs \ link-addr ^class-link link-offset
                R@ + newObject +
                ( link-addr ^class-link ivarAddr )                
            2 PICK @IvarRec? 0= \ only store a header if not a record
            IF                
                2dup ( link-addr ^class-link ivarAddr ^class-link ivarAddr )
                
                cell - \ link-addr ^class-link addr   \ addr = addr in new object
                swap @ swap \ convert ^class-link to ^dispatch
                  ! \ store the ^dispatch as a header at the given address in the new object
                  THEN
      ( link-addr ^class-link ivarAddr )
      over ( link-addr ^class-link ivarAddr ^class-link )
      @width \ link-addr ^class-link ivarAddr elemWidth
      IF
        \ yes, this is an indexed ivar
        ( link-addr ^class-link ivarAddr )
        swap dfa @ + over @IvarElems swap ! \ store indexed upper limit
      ELSE
        2drop
      THEN
                  dup R@ InitIvar  \ send implicit init: message to ivar
         ELSE drop
         THEN
              @  \ next-link-addr 
              REPEAT R> ( 0 offset ) 2drop ; \ stop thread
              
  : (SUPER-ITRAV)  \ { ^cls offset -- }
   0 locals| temp offset ^cls |
  ^cls #nways 0
         DO ^cls sfa @ cell+ i 2* cells + dup to temp @ ( ith primary superclass )
              dup ^objectClass <> \ skip to LOOP if ^class=OBJECT
            IF  
              ( ^cls sfa @ cell+ cell+ i 2* cells +) temp cell+ @ offset + ( ith cumulative offset )
               SUPER-ITRAV 
               \ return here after this SUPER-ITRAV thread gets stopped
             ELSE drop
            THEN  
          LOOP
            \ handle the linked-list ivars
            \ ( yes, this will get all superclass ivars and main class ivars )
            ^cls ifa @ ?DUP \ check for the case when the class has no ivars
            IF \ yes, there is at least one ivar
               ( link-addr ) offset ITRAV 
              \ return here after this ITRAV thread gets stopped
              \ stop thread
            THEN ;
' (SUPER-ITRAV) is SUPER-ITRAV

\ =====================================================================

: SUPERS-INIT ( ^class offset -- )
   0 0 0 LOCALS| temp1 temp2 temp3 offset ^cls |
  ^cls #nways 0 \ #nways will always be 1 or greater
       DO  
         ^cls sfa @ CELL+  i 2* CELLS + dup to temp1 @ dup to temp2 ( ith-primary-superclass )
         DUP ^objectClass <> \ skip to LOOP if ^class=OBJECT
         IF
          ( ^cls sfa @ CELL+ CELL+ i 2* CELLS +) temp1 cell+ @ offset + dup to temp3 ( ith-cumulative-offset )
          RECURSE
         ELSE DROP
         THEN 
         ( ^cls sfa @ CELL+ i 2* CELLS + @ ) temp2 ( ith-primary-superclass )
         @ ( ^dispatchi ) (init:) + @ ( xt ) newObject ( xt ^obj )
         ( ^cls sfa @ CELL+ CELL+ i 2* CELLS + @ offset +) temp3 ( xt ^obj ith-cumulative-offset )
         + EXECUTE-METHOD'''
       LOOP ;

\ Compile the indexed data header into an object
: IDX-HDR   ( #elems ^Class | ^Class -- indlen )
  @width DUP IF  OVER , ( limit )  *   THEN ;

: Build   ( ^Class -- )
 ^Class
  IF <Var \ yes, so this must be an embedded object-as-ivar declaration
  ELSE    \ no, so we must instantiate a new named dictionary object
    (Obj)
     DUP >R @ ,  \ store dispatch table pointer in this object
     R@ XFA @ IF depth 1 < ABORT" Indexed object missing Limit"
              THEN
     HERE TO newObject  \ remember current ^object: used in ITRAV  
     R@ DFA @ RESERVE   \ allot space for ivars
     R@ IDX-HDR RESERVE \ allot space for indexed data
     R@ ( ^class ) 0 SUPER-ITRAV \ setup all ivar headers in this object
    Init \ send INIT: message implicitly to newly created object
    R> 0 SUPERS-INIT  \ make sure all nested superclasses also receive init:
THEN ;

: classAlign  ( -- )  \ Align class data size (optional)
 ^Class DFA @  ALIGNED  ^Class DFA ! ;

CREATE classname$ maxnameSize ALLOT

\ : scanForSuper
\   scan$ do-scan DUP COUNT S" <SUPER" COMPARE  \ $ptr flag
\   SWAP COUNT S" SUPER{" COMPARE \ flag flag
\   and
\   ABORT" Missing <SUPER declaration after class name" ;

: scanForSuper
  scan$ do-scan DUP COUNT S" <SUPER" COMPARE  \ $ptr flag
  SWAP COUNT S" SUPER{" COMPARE \ flag flag
  and
  IF S" <SUPER OBJECT" EVALUATE THEN ; \ 01/29/12 dbh  

0 VALUE temp-wid \ 01/29/12 dbh  

FORTH-WORDLIST   SET-CURRENT

: :CLASS ( "spaces<name>" -- ) \ name of the new class being defined
  ^objectClass \ will be zero until after we define class object below
  IF  \ create a wordlist for the current class \ 01/29/12 dbh  
     WORDLIST TO temp-wid THEN \ will properly store wid in POST-SUPER
    FALSE TO rec?
    classname$ do-scan drop
    CREATE IMMEDIATE  \ 01/24/12 dbh  for buildLocal
    scanForSuper
    DOES>  Build ;

nclass SET-CURRENT \ ***

\ These values are used in processing the superclass list.

0 VALUE ^sup
0 VALUE #sup
0 VALUE #sup-indexed
0 VALUE ivlen

\ store cumulative offsets
: next_super  ( ^sup -- )
  DUP ?isClass 0= ABORT" not a class"
 TO ^sup
 ^sup ,       \ Add ^class to n-way
 ivlen ,       \ store cumulative offset
 ^sup DFA @  ivlen +  TO ivlen \ And add ivar length of new class
 
 ^sup XFA @ 
    IF \ sup is indexed
    #sup-indexed 1+ TO #sup-indexed
    #sup-indexed 1 > ABORT" only one superclass can be indexed"
       \ Class we are building is *not* already indexed.
       \ So make it so. Note that we only allow one indexed superclass
       \ and it must be the first superclass.
       ^sup @width ^class XFA !
    THEN
 
 #sup 1+  TO #sup 
 ;

: }  ABORT" Unmatched }"  ; IMMEDIATE

: supers_loop
 BEGIN      \ Loop over superclasses:
  >IN @
  BL WORD     \ See if } follows
  COUNT 1 =
  IF C@
   [CHAR] } =
   IF  DROP EXIT  THEN
  ELSE DROP
  THEN
  >IN !
  '      \ cfa of next item on list
  >BODY  next_super  \ handle next superclass
 AGAIN  ;

: POST-SUPER   \ POST-SUPER{ or POST-<SUPER
  GET-ORDER  \ save prior search order for later restore
  ^objectClass \ will be zero until after we define class object below
  IF
  \ create a wordlist for the current class
  temp-wid ^class wida ! \ store in wida field \ 01/29/12 dbh  
  GET-ORDER
  nclass SWAP 1+ \ add nclass to the search order build \ ***
  ^class build-search-order SET-ORDER
  classname$  ^class ClassName move$ \ save class name
  THEN
  ^class SFA @ ( ^nway ) cell+ @ Meta = \ will be true only for class OBJECT
  IF \ compiling class object, so there are no superclass dispatch tables,
     \ therefore we must start a new heap table from scratch.
   1 initHeapTable \ cell 0 will be the #ofXTs for this class
  ELSE \ get initial size from superclass(es)
   largestSuperTableSize ( size of largest superclass dispatch table in records) 
     1+ initHeapTable \ start with a heap table of same size as largest superclass
  THEN ;

: PRE-SUPER   \ PRE-SUPER{ or PRE-<SUPER
  HERE TO ^class   \ save current class
  classSize RESERVE   \ reserve rest of class data
  classtag ^class TAG ! ;  \ tag it as a class

FORTH-WORDLIST   SET-CURRENT

: SUPER{ ( "spaces<name1>" "spaces<name2>" ... -- )  \ <name> is the name of the superclass(es)
  PRE-SUPER
  HERE DUP TO ^nway   \ n-way for superclasses will start here
  ( HERE ) ^class SFA !  \ store pointer to n-way as superclass ptr
  0 TO ivlen  0 to #sup 0 to #sup-indexed
  0 , \ initial size of n-way is 0
  supers_loop \ loop over each superclass
  #sup ^nway ! \ store the number of superclasses at ^nway
  ivlen  ^class DFA !   \ Set total ivar length in this class
  POST-SUPER ;

\ maintain backwards compatibility with this syntax for single-inheritance
: <SUPER ( "spaces<name>" -- ) \ name of the superclass
  PRE-SUPER
  ' >BODY ( ^superclass )
  DUP ^class classSize MOVE
  0 ^class IFA !
  HERE DUP TO ^nway   \ n-way for superclasses will start here
  ( HERE ) ^class SFA !  \ store pointer to n-way as superclass ptr
  1 , \ size of n-way is always 1 for single inheritance
  ( ^superclass ) , \ Add ^class to n-way
  0 ,  \ store cumulative offset, always 0 for single inheritance
  POST-SUPER ;

nclass SET-CURRENT \ ***

: ;CLASS
  classAlign  \ align class data (optional)
  align
  ^class ,  \ store ^class at one cell before the dispatch table
  HERE ^class ! \ now make ^class point to the first cell of the dispatch table
   hTableSize records ALLOT \ allot the dictionary dispatch table
  ^class SFA @ ( ^nway ) cell+ @ Meta <>
  IF \ Don't do AdvanceSuperclMethodXTs when compiling class object.
   \ Move XTs from multiple superclass tables to empty cells in single heap table.
   AdvanceSuperclMethodXTs
  THEN
   transferMethodXTs \ from the heap table to the dispatch table
   freeHeapTable
   SET-ORDER  \ restore original search order from SUPER{ or <Super
  FORTH-WORDLIST  SET-CURRENT 
    0 TO ^class
    0 TO current-cum-offset ;

0 VALUE lastSelectorIndex
0 VALUE curSelIdx

: Selector  ( "spaces<name:>" -- ) 
    CREATE \ IMMEDIATE
    lastSelectorIndex recordSize + DUP TO lastSelectorIndex ,
    selectorTag ,   \  mark this word as a selector
    DOES> ( pfa ) @ Send ;

: no-colon  ( str -- flag )  \ true if selector at addr does *not* end in colon
  DUP DUP C@ CHARS +  C@ [CHAR] :  =  SWAP C@ 1 > AND  0=  ;

: validSelector? ( str -- )
  no-colon abort" Message name must end in colon!" ;

: getSelect \ input stream: ( "spaces<messagename>" -- SelID )
  ?isSel IF ( in addr ) NIP 
         ELSE ( in n ) DROP >IN !
              >IN @ BL WORD validSelector? >IN !
              Selector HERE [ 2 CELLS ] LITERAL -
         THEN @ ;

FORTH-WORDLIST  SET-CURRENT 

: makeSelect ( "spaces<name:>"-- )
   getSelect DROP ;

nclass SET-CURRENT \ ***

0 VALUE compilingClassinit?

: scanForClassinit
 scan$ do-scan COUNT
 S" INIT:" COMPARE 0=
 IF \ we have classinit:
   -1 TO compilingClassinit? \ set flag so we compile " super init: " in :M below
 THEN ;
 
: :M  ( "spaces<name:>" -- methodXT ) 
  0 TO compilingClassinit?
  ^objectClass IF scanForClassinit THEN  
  getSelect
  ALIGN   \ align method
  recordSize / TO curSelIdx \ curSelIdx in increments of dispatch table cells
         \ one dispatch cell contains an xt and an ivar offset
  :NONAME 
   ^objectClass compilingClassinit? AND
   IF S" SUPER INIT: " EVALUATE THEN
  ;

: ;M  ( methodXT -- )
    POSTPONE ;
  \ the methodXT from above :NONAME will be on the stack
  ( methodXT ) \ save on stack, to be consumed after REPEAT
  BEGIN
    hTableSize 1- curSelIdx <
  WHILE
    incrHeapTable \ increase table size by one record
  REPEAT
  ( methodXT ) curSelIdx XTtoHeapTable  \ store xt in proper cell in dispatch table
 ; IMMEDIATE

nclass SET-CURRENT \ ***

: allotObj ( n -- addr )  HERE SWAP ALLOT ; 
  
: allocObj ( n -- addr )  ALLOCATE ?MEMERR ; 

0 VALUE allot/alloc \ will contain either allotObj or allocObj xt

: (makeObj)  ( size ^dispatchTable -- )  \ allocate object and store in newObject
 OVER CELL+  \ allow for ^dispatchTable
           \ ( size ^dispatchTable n )
 allot/alloc EXECUTE
 DUP CELL+ TO newObject  \ object address
 !   \ store the ^dispatchTable
 newObject SWAP ERASE ; \ clear to zero

: makeObj  ( #elems class xt | class -- ^obj )
  TO allot/alloc
 >R  ( save class on return stack )
 R@ DFA @  ( ivar data size )
 R@ @width ?DUP
 IF \ indexed object, add size of indexed area
  \ ( #elems size width -- )
  2 PICK * + ( indexed data )  CELL+ ( idxHdr )
  R@ @ (makeObj)
  newObject R@ DFA @ + !  ( store #elems in idxHdr )
 ELSE
  R@ @ (makeObj) \ non-indexed object
 THEN
 R@ ( ^class ) 0 SUPER-ITRAV \ setup all ivar headers in this object
 Init \ send INIT: message implicitly to newly created object
 R> 0 SUPERS-INIT  \ make sure all nested superclasses also recieve init:
 newObject  ;  \ return object address

: dictObj ( #elems class | class -- ^obj )
  ['] allotObj makeObj ;

: heapObj ( #elems class | class -- ^obj )
  ['] allocObj makeObj ;

: (heapObj) ( #elems class | class -- ^obj ) heapObj ; \ synonym for backwards compatibility

: >class  ( ^obj -- ^class )  \ get the class of an object
  CELL - @ \ ^dispatchTable
  CELL - @ ; \ ^class

: ^base-idx ( -- addr )
  ^base lastoffset  - ;

: idxBase  ( -- addr )  \ get base address of idx data area
  ^base-idx DUP >class DFA @ +  CELL+ ;

: ?idx  ( index -- index )  \ range check
 DUP idxBase CELL - @ ( index #elems )  0 SWAP  WITHIN IF EXIT THEN
 TRUE ABORT" Index out of range" ;

\ support for indexed objects
\ Set a class and its subclasses to indexed
: <Indexed  ( width -- )
  ^class XFA DUP @ ABORT" class is already indexed"
  ( ^class XFA ) !  ;

: limit    ( -- max#elems )  \ get idx limit (#elems)
  ^base-idx DUP >class DFA @ +  @ ;

: width    ( -- n )  \ width of an idx element
  ^base-idx >class XFA @ ;

fmsCheck?
[IF]
: ^elem   ( index -- addr ) \ get addr of idx element
  ?idx
  width *  idxBase + ;
[ELSE] 
: ^elem   ( index -- addr ) \ get addr of idx element
 ^base-idx >class DUP >R XFA @ *  \ index stride
 ( idxBase => ) ^base-idx R> DFA @ + CELL+
 + ;
[THEN]

: SUPER \ input stream: ( "spaces<messagename>" --  ) \ early bind to following message
 \ Must use the first matching method from one of the superclasses in the hierarchy.
 \ Need only inspect each primary superclass for a hit on SelID because all of the
 \ "superclasses of superclasses" methods will have already migrated to these primary tables.
  scanForMessage 0= ABORT" SUPER not followed by a message"
  >SelID ( selID ) 0 LOCALS| temp SelID |  
  ^class #nways 0
  DO
     SelID \ SelID
      ^class sfa @ cell+ i 2* cells + dup to temp @ ( ith primary superclass )  \ SelID ^class
      @ \ SelID ^dispatch
      2dup \ SelID ^dispatch SelID ^dispatch
      @    \ SelID ^dispatch SelID maxSelID  \ check to see if selID is in bounds for this table
      > IF  \ SelID is out of bounds for this superclass
           2drop \ continue to next primary superclass
        ELSE \ SelID ^dispatch
           + dup @ \ addr xt
           dup ['] notUnderStood =
              IF 2drop \ not found, keep searching
              ELSE \ found, so compile it
                 \ addr xt
                 PL
                 POSTPONE ^base
                  cell+ w@ (  xt-Offset )
                 ( ^class sfa @ cell+ cell+ i 2* cells +) temp cell+ @ ( ith cumulative offset ) +
                 
                 ?DUP IF PL POSTPONE EXECUTE-METHOD'
                      ELSE  POSTPONE EXECUTE-METHOD'''
                      THEN
                 UNLOOP EXIT
              THEN
        THEN
   LOOP TRUE ABORT" SUPER message not found" ; IMMEDIATE

: (SUPER>) \ { ^supcls ^cls -- offset true | false }
    0 LOCALS| temp ^cls ^supcls |
   ^cls #nways 0 \ #nways will always be 1 or greater
   DO
     ^cls sfa @ cell+ i 2* cells + dup to temp @ ( ith primary superclass )
     dup ^supcls =
     IF \ we found the specified superclass in the class hierarchry chain
        drop
        ( ^cls sfa @ cell+ cell+ i 2* cells +) temp cell+ @ ( ith cumulative offset )
        true unloop exit \ stop thread here
     THEN
     ( ith primary superclass ) dup ^objectClass = IF drop false unloop exit THEN
     ( ith primary superclass ) ^supcls swap ( ^supclsi ^clsi )
     ( ^supclsi ^clsi ) RECURSE
     ( offset true | false ) IF true unloop exit THEN
   LOOP 0 ; \ stop thread if we get here
   
: SUPER>  \ early bind to the following message in the specified superclass
 \ input stream: ( "spaces<className>" "spaces<messageName>" --  )
 ' >BODY ( ^supclass )
    DUP ?isClass 0= ABORT" SUPER> not followed by a class name"
     scanForMessage 0= ABORT" 'SUPER> classname' not followed by a message"
 >SelID ( selID ) LOCALS| selID ^supclass |
 ^supclass ^class (SUPER>) 
 ( offset true | false ) 
 IF ( offset ) >R
     ^supclass @ ( ^dispatchTable ) selID + DUP ( addr addr )
     @ ( addr xt ) PL
     POSTPONE ^base
     ( addr ) CELL+ w@ R> + ( offset )
     ?DUP IF PL POSTPONE EXECUTE-METHOD'
          ELSE  POSTPONE EXECUTE-METHOD'''
          THEN
 ELSE
  TRUE ABORT" SUPER> class not found"
 THEN ; IMMEDIATE

: SELF \ input stream: ( "spaces<messagename>" -- ) \ early bind to following message
       ( -- ^obj )  \ or just leave ^object if next word in input
                     \ stream is not a message
  0 0 0 LOCALS| ^dsp addr SelID |
  scanForMessage
  IF \ early bind to following message
       >SelID ( selID ) ^nway CELL+ TO addr TO SelID
      SelID heapTable + @ ?DUP IF ( xt ) PL POSTPONE ^base POSTPONE EXECUTE-METHOD'''
                               ELSE \ must look in superclass's tables
          ^nway @ 0 ?DO  addr @ ( ^supclassi )
              @ ( ^dispatchTable) to ^dsp
              ^dsp @ ( maxSelID ) SelID < 0=
              IF
               ^dsp SelID + @ ( xt )
               DUP 0<>  \ ?xt flag
               OVER ['] notUnderStood <> and
               IF ( xt ) PL
               POSTPONE ^base
               addr CELL+ @ ( cumOffset )
                 ?DUP IF PL POSTPONE EXECUTE-METHOD'
                      ELSE  POSTPONE EXECUTE-METHOD'''
                      THEN
                 UNLOOP EXIT
               ELSE ( xt ) DROP
               THEN
              THEN addr 2 CELLS + TO addr
              LOOP TRUE ABORT" message not understood"
          THEN
  ELSE \ just leave ^obj => ^base if not followed by message
     POSTPONE ^base 
  THEN
     ; IMMEDIATE     

\ late bind the following message to SELF
\ Note the ^base correction needed via lastOffset. lastOffset is setup by the last
\ call to EXECUTE-METHOD or any of its equivalents
: [SELF] \ Input stream: "spaces<messageName>"  \ [SELF] *must* be followed by a message
  scanForMessage 0= ABORT" [SELF] not followed by a message"
  POSTPONE ^base ( ^obj )
    POSTPONE lastOffset  POSTPONE - \ only needed-by/affects multiple inheritance
  >SelID ( SelID ) PL POSTPONE Send ; IMMEDIATE

\ Compute total length of an object.   
\ The length does not include the dispatch table pointer.
: objlen  ( -- objlen )
 ^base >class DUP DFA @  ( non-indexed data )
 SWAP @width ?DUP
 IF  idxBase CELL - @ ( #elems ) * +  CELL+  THEN
 ;

FORTH-WORDLIST  SET-CURRENT

:class object super{ Meta }
  :m classname: ( -- addr len ) self >class ClassName COUNT ;m
  :m heap: ( -- ^obj ) self CELL - @ CELL - @ heapObj ;m
  :m len: ( -- n ) objlen ;m
  :m free: ;m
  :m init: ;m
;class 

nclass SET-CURRENT \ ***

\    ^objectClass needed by ITRAV
' object >BODY to ^objectClass 

getselect init: TO (init:)  

: BYTES  ( n "spaces<name>" -- )
   ['] object >BODY
   rec? 0= IF  CELL NEGATE classAllot THEN
    <Var  classAllot ;

: (IV) ( ^obj -- ^obj ^class )
    DUP >class ;

: ((IV)) ( ^obj ^class ivarname-hash -- ivar-addr )
    SWAP 0 SUPER-IVAR-FIND
    IF ( ^obj offset ^class ) DROP
       ( ^obj offset ) +
    ELSE
     -1 abort" ivar name not found"
    
    THEN ;

: hash>  ( -- n )  BL WORD COUNT HASH-IVAR ;

FORTH-WORDLIST  SET-CURRENT

\ interpret only, cannot be compiled
: IV ( ^obj -- ivar-addr )
   \ input stream: "spaces<ivarname>"
    (IV) \ ^obj ^class
    hash> ( ^obj ^class ivarname-hash )
    ((IV)) ;

\ compile only
: [IV] ( ^obj -- ivar-addr )
   \ input stream: "spaces<ivarname>"
  POSTPONE (IV) ( ^obj ^class )
  hash> PL  ( ^obj ^class ivarname-hash )
  POSTPONE ((IV)) ; IMMEDIATE

nclass SET-CURRENT \ ***

\ ------- begin DotParse code

: add$ ( src$ptr\dest$ptr --) \ adds src$ to the end of dest$.  src$ is unchanged.
 LOCALS| $2 $1 |
 $1 1+ ( src)
 $2 DUP C@ + 1+ ( dest)
 $1 C@ ( count)
 CMOVE
 $1 C@  $2 C@ + $2 C! ;

0 value source$
0 value parsed$

: $IV C"  IV " ;
: $[IV] C"  [IV] " ;

: (convert-source$) ( xt -- )
  locals| xt |
  0 parsed$ c!
  source$ count bounds 
  ?DO I c@ [char] . =
      IF xt execute parsed$ add$
      ELSE I c@ parsed$ count + c!
            parsed$ c@ 1+ parsed$ c!
      THEN
  LOOP ;

: convert-source$ 
\   replace all "."  with " IV " or " [IV] "
  STATE @
  IF
    ['] $[IV] 
  ELSE
    ['] $IV
  THEN (convert-source$) ;

: dotParse 
     convert-source$  parsed$ count EVALUATE ;

: init-dotparse
  256 allocate ?memerr to source$
  256 allocate ?memerr to parsed$ ;

: cleanup-dotparse
  source$ free ?memerr
  parsed$ free ?memerr ;

FORTH-WORDLIST  SET-CURRENT

\ ANS compatible
: .. ( -- ) 
    \ Input (typical): MyLine.p1.y0 
    \ or ( ^obj -- )
    \ Input stream (typical): .p1.y0
  init-dotparse  
  bl word ( src )  source$ ( dest ) move$
  dotParse
  cleanup-dotparse
  ; IMMEDIATE

\ ------- end DotParse code

nclass SET-CURRENT \ ***

\ ------- begin objArray() code

: (doObjArray) \ ( idx addr -- ^obj(idx) )
   DUP >R \ idx addr
   CELL+ @  CELL+ \ idx objWidth
   *  \ offset
   R> + [ 3 CELLS ] LITERAL + \ ^obj(idx)
; 

fmsCheck? [IF]

: doObjArray \ ( idx addr -- ^obj(idx) )
   2DUP \ idx addr idx addr
   @    \ idx addr idx #objects 
   0 SWAP \ idx addr idx 0 #objects
   WITHIN 0= ABORT" Invalid index for objArray()"
    (doObjArray) ; 

[ELSE]

: doObjArray \ ( idx addr -- ^obj(idx) )
    (doObjArray) ; 

[THEN]

FORTH-WORDLIST  SET-CURRENT


: objArray() \ instantiation time: ( #objects -- )
            \ or if indexed: ( #objects #elems -- )
            \ input stream: "<spaces>className" "<spaces>name()"
             \ run time execution of name()  ( idx -- ^obj(idx) )
   ' >BODY
   ALIGN CREATE 
   ( ^class) DUP  \ #objects ^clss ^clss | #objects #elems ^clss ^clss
   xfa @   \ #objects ^clss xfa@ | #objects #elems ^clss xfa@
   SWAP    \ #objects xfa@ ^clss | #objects #elems xfa@ ^clss
   DUP dfa @ \ #objects xfa@ ^clss dfa@ | #objects #elems xfa@ ^clss dfa@
   0 0         \ #objects xfa@ ^clss dfa@ 0 0 | #objects #elems xfa@ ^clss dfa@ 0 0
   LOCALS| #elems addr0 objWidth ^clss xfa@ #objects |
   xfa@
   IF \ we have an indexed class of objects
    #objects TO #elems
    TO #objects
    #elems xfa@ * CELL+ objWidth + TO objWidth
   THEN
   #objects , objWidth , 
   HERE TO addr0
   #objects objWidth CELL+ * RESERVE
 \  | #objects | objWidth | addr0 ...
    addr0 #objects objWidth CELL+ *  + addr0
    DO  ^clss @ i ! \ store ^dispatchTable header
        i CELL+ TO newobject \ set up newobject so init routines will work
        xfa@ IF #elems  i  ^clss dfa @ CELL+ + ( addr for #elems ) ! THEN \ store #elems if indexed
        \ ^clss InitObject \ perform init routines
        
        ^clss IDX-HDR RESERVE \ allot space for indexed data
        ^clss ( ^class ) 0 SUPER-ITRAV \ setup all ivar headers in this object
        Init \ send INIT: message implicitly to newly created object
        ^clss 0 SUPERS-INIT  \ make sure all nested superclasses also receive init:
        
        
        objWidth CELL+ +LOOP \ +loop to next object in objectArray()
   
   DOES> ( idx addr )
   doObjArray 
   ;

\ ------- end objArray() code

\ heap> must only be executed at run time (used in a definition).
: HEAP>   ( "spaces<classname>" -- ^obj )
\  STATE @ 0= ABORT" HEAP> is a compile-only word"
 ' >BODY DUP ?isClass 0= ABORT" Name following HEAP> is not a class"
 PL  POSTPONE heapObj
 ; IMMEDIATE

: <FREE  ( ^obj -- )  \ free a heap object
 DUP free:
 CELL - FREE ?MEMERR ;

\ dict> must only be executed at run time (used in a definition).
: DICT>   ( "spaces<classname>" -- ^obj )
\  STATE @ 0= ABORT" DICT> is a compile-only word"
 ' >BODY DUP ?isClass 0= ABORT" Not a class"
 PL  POSTPONE dictObj
 ; IMMEDIATE

: mxt  \ "class" "method" -- xt
\ Find the xt of a method in a class.
  ' >body @    \ -- ^dispatch
  >SelID    \ -- ^dispatch SelID
  swap >xt
;


0 [IF]
words
DICT>           <FREE           HEAP>           OBJARRAY()      ..  
[IV]            IV              INIT:           FREE:           LEN:  
HEAP:           CLASSNAME:      OBJECT          MAKESELECT      <SUPER  
SUPER{          :CLASS          CLASS_AS>
[THEN]

0 [IF] \ Optional Diagnostics/Inspection code 

: (dd) ( ^cls -- )
  cr ." DUMP DISPATCH TABLE"
  locals| ^cls |
  cr ." ^dispatchTable-cell " ^cls @ cell - .  ."  = ^class => "
        ^cls @ cell - @ .
  cr ." ^dispatchTable =  " ^cls @ .
  cr ^cls @ @ 1 records / . ."  = #ofrecords "
  cr ." record#  " ." XT  "  ."   ivar-offset"
  ^cls @ @ 1 records / 1+ 0 ?DO cr i . i ^cls XTatDisTable  .
                     i ^cls OffsetatDisTable .
                 LOOP ;

: dd \ dump dispatch table
  \ usage:   dd <classname>
  ' >body ( ^cls ) (dd) ;

: dumplinked-list ( addr -- )
 cr ." DUMP IVAR LINKED-LIST"
  cr ." Link  "   ." hash-name  "  ." ^class  "  ."   Offset"
  locals| addr |
  BEGIN
    addr @
  WHILE
    cr addr @ to addr  addr .
    addr cell+ @ .
    addr cell+ cell+ @ .
    addr cell+ cell+ cell+ @ .
  REPEAT ;
    
: (di) ( ^cls )
   IFA dumplinked-list ;

: di \ dump ivar linked-list
  \ usage:   di <classname>
  ' >body ( ^cls ) (di)
 ;

: d \ { n addr  -- } \ for debugging, addr = beginning address n = # of cells to dump
  locals| addr n  |
  n 0 ?DO CR I . ADDR I CELLS + DUP . @ . LOOP ;

: (dc) ( ^cls -- )
  cr ." DUMP CLASS"
 0 locals| addr ^cls |
 cr 0 . ^cls . ^cls @ .  ." ^class @ => ^dispatchTable"
 cr 1 . ^cls IFA dup . @ . ." ^class IFA @ => ivar link addr"
 cr 2 . ^cls DFA dup . @ . ."  ^class DFA @ => total ivar data length"
 cr 3 . ^cls XFA dup . @ . ."  ^class XFA @ => elem width for indexed area, <= 0 if not indexed"
 cr 4 . ^cls SFA dup . @ . ."   ^class SFA @ => ^nway "
 cr 5 . ^cls WIDA dup . @ ( dup) . ."   ^class WIDA @ => wid" 
 cr 6 . ^cls TAG dup . @ dup . ."   ^class TAG @ => classTag" 
 cr 7 . ^cls ClassName dup .   count type ."   ^class ClassName @ count type => CLASSNAME" 
 cr 8 . ^cls SFA @ dup . @ . ."  ^nway @ => # of superclasses"
  ^cls SFA @ cell+ to addr
    ^cls SFA @ @ 0
   ?DO cr   
       addr . addr @ dup . ." => super(i) "
       dup ['] object >body = IF ."  = OBJECT" THEN
       meta = IF ."  = Meta" THEN
       addr cell+ to addr
       cr addr . addr @ .  ." cum offset"
       addr cell+ to addr
    LOOP
 ;

: dc  \ dump class
  \ usage:   dc <classname>
 ' >body ( ^cls ) (dc) ;

: da  \ dump all
  \ usage:   da <classname>

 ." DUMP ALL"
 ' >body locals| ^cls |
 ^cls (dc)
 ^cls (di)
 ^cls (dd)
 cr drop ;

: dsp ' >body @ . ;
\ usage: dsp <classname>
\ prints ^dispatch address
: cls ' >body . ;
\ usage: cls <classname>
\ prints ^class address


[THEN]


GET-ORDER  NIP  1-  SET-ORDER     \ hide nclass definitions  ***




