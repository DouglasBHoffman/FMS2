\ 01/28/12 dbh changed "heap> record rlist addObj:" to "['] record rlist add:" in newRecord
0 [IF]
\ for gforth and vfx, do a copy/paste
\ your drive letter may be different

include e:\a-way-to-file.f


[THEN]

\ instantiate all named objects here:
file f   
string+ s
string+ ss
object-list rlist
string+ what
string+ what'

0 VALUE changed?  \ flag, true if a change has been made to file
: changed true to changed? ;
: unchanged false to changed? ;

: makeKind ( n -- )
  create , DOES> @ ;
  
0 makeKind surname
1 makeKind given
2 makeKind job
3 makeKind phone
\ 4 makeKind city \ how to add fields (be sure to increment #ofFields also )

4 value #ofFields \ set # of kinds (fields) in this value

:class record <super object
  array fields \ idx 0=surname 1=given 2=job 3=phone

:m init1: #ofFields fields new:
    #ofFields 0 DO heap> string+ i fields to: LOOP ;m
:m get: ( i -- ^str-obj ) fields at: ( ^str-obj ) ;m
:m write: ( str-obj -- )
    locals| ^str |
    #ofFields 0 DO I fields at: @: ^str add: [char] , ^str +: LOOP
    cr# ^str replLast: ;m
:m free:
    #ofFields 0 DO i fields at: <free LOOP 
    fields free: ;m
;class

: newRecord
   ['] record rlist add: \ create a new record object
   rlist obj: init1: ;  \ initialize the record object

: !field ( addr len idx -- )
   >R
   2dup 1- + c@ cr# = IF 1- THEN \ trim cr# from end of string if it has one
   R> rlist obj:  get: !: ;

: LoadRecords \ from string s into our object-list
  s reset:
  BEGIN
    cr# s word: \ locate next line from string s
  WHILE
    s @sub: ss !: \ put that line in string ss
    \ one line = one record with a variable number of fields per record
    newRecord
    #ofFields 1- 0 DO [char] , ss word: -1 <> abort" LoadRecords ss word: -1 error"
           ss @sub: ( addr len ) I !field
        LOOP
        \ last field will not end with a comma
        [char] , ss word: 0 <> abort" LoadRecords ss word: 0 error"
        ss size: ss end: !
        ss @sub: #ofFields 1- !field
  REPEAT ;

: records->string
   0 0 s !:  \ set string size to zero
   BEGIN
     s rlist each:
   WHILE
     ( str-obj record-obj ) write:
   REPEAT drop ;
  
: SAVE
   records->string
   s @: f write: drop
   cr ." File saved " unchanged
   ;

: ENTER
   newRecord
   #ofFields 0 DO
       [char] , word count I !field
   LOOP changed ;

0 value kind
0 value #record
true value partialSearch?
false to case-sensitive?
: PART true TO partialSearch? ;
: WHOLE false TO partialSearch? ;
: SET   ( u -- ) TO #record ;                   
: TOP    0 SET ;    
: DOWN   #record 1+  SET ;  
: size ( -- size ) rlist size: ;
: rlist@ ( idx -- record-obj ) rlist at: ;
: do-search ( addr len ^obj -- flag )
   partialSearch?
     IF search: ELSE =: THEN ;
: (-find) ( idx -- flag )
   rlist@ ( record-obj )
   kind swap ( idx record-obj ) get:
   ( str-obj ) dup reset:  \ prepare for new search
   what @: ( str-obj addr len ) rot ( addr len str-obj )
   do-search
   ;  
   
: -find ( -- idx true | false )
  size #record 
  ?DO I (-find) IF I to #record I true unloop exit THEN
  LOOP false ;

: KBD, ( -- addr len )   [CHAR] , WORD COUNT 2dup 1- + c@ 33 < IF 1- THEN ;
: KBD-bl ( -- addr len )     bl WORD COUNT ;
: KEEP  TO kind KBD, what !: ;

0 value kind'

: KEEP' TO kind' KBD-bl what' !: ;

: missing ." Not in file " ;
: proceed 
   size #record > 0= abort" Must first do a FIND, PAIR, or FULLNAME" ;
: ?kind ( -- kind ) ' >body @ ;
: CHANGE
   proceed
   ?kind KBD, \ type addr len
   rot \ addr len type
   #record rlist@ ( record-obj )
   get: !: changed ;
 
: .name
     rlist@ ( record-obj ) >r
     given r@ get: p:
     space
     surname r> get: p: ;
     
: (pair)
  size 0 
  DO I (-find) IF 
                I rlist@ kind' swap get: dup reset:
                what' @: rot do-search IF I to #record I .NAME unloop exit THEN
             THEN
  LOOP MISSING ;

: PAIR ?kind KEEP ?kind KEEP' (pair) ;

: FULLNAME  surname KEEP  given KEEP' (pair) ;

: FIND ?kind keep top -find 
  IF .NAME
  ELSE MISSING
  THEN ;

: ANOTHER
   proceed
   down -find
   IF .NAME
   ELSE MISSING size to #record
   THEN ;

: ALL
  top BEGIN
        cr -find
      WHILE
        .NAME
        down
      REPEAT #record 1- to #record ;

: REMOVE
   proceed
   #record rlist delete: changed ;

: GET
   ?kind 
   proceed
   #record rlist@ ( record-obj ) 
   get: p: ;
 
: CLOSE
  changed?
  IF
    cr ." Save changes first? (y/n)"
    KEY dup [CHAR] y =
       swap [CHAR] Y = OR IF SAVE THEN
  THEN
  f [iv] name p:
  f close: drop
  ."  file closed"
  rlist free:
  s free:
  ss free:
  what free:
  what' free:
  cr ." heap memory FREEd" cr unchanged ;

: (open)
  f [iv] open? @: IF CLOSE THEN ;

: OPEN ( addr len -- ) \ filename
  (open)
  f open: drop
  s f read: 2drop
  s reset:
  LoadRecords
  size . ." records read from file" unchanged ;

: PRINT
   records->string
   s p: ;
   
: NEW ( addr len -- )
  (open)
  f create: drop changed ;
  
\ ------------- End user words ---------------------------------------------------------------

\ Same as Brodie example:
\ ENTER    Creates a new record, then moves four strings delimited by commas into the 
\          surname, given, job and phone fields of that record.
\     Usage: ENTER lastname,firstname,job,phone
\ REMOVE   Deletes the current record.
\ CHANGE   Changes the contents of the given field in the current record. 
\     Usage: CHANGE field-name new-contents
\ GET    Prints the contents of the given type of field from the current record.
\    Usage: GET field-name
\ FIND    Finds the record in which there is a match between the contents of the given field 
\          and the given string.
\    Usage: FIND field-name string
\ ANOTHER  Beginning with the next record after the current one, and using KIND to determine
\          type of field, attempts to find a match on WHAT. If successful, types the name;
\     otherwise an error message.
\ ALL     Beginning at the top of the file, uses KIND to determine type of field and finds 
\    all matches on WHAT. Types the full name(s).
\ PAIR    Finds the record in which there is a match between both the contents of the first 
\     given field and the first given string, and also the contents of the second given 
\    field and the second given string. Comma is delimiter.
\    Usage: PAIR field1 string1,field2 string2
\ FULLNAME Finds the record in which there is a match on both the first and last names given.
\    Usage: FULLNAME lastname,firstname

\ Added:
\ NEW      Creates a new file and opens it for all subsequent operations.
\           Usage: S" mynewfile" NEW
\ OPEN     Opens the named file and reads all records into memory.
\          Usage: S" filerdata.forth" OPEN
\          Will CLOSE the currently open file if necessary.
\ PRINT    Prints the contents of all records and fields
\ SAVE     Saves all records to the file on disc
\ CLOSE    Closes the file and frees any heap memory used.
\          Will first ask if you want to SAVE changes only if any have been made.
\ PART     Sets all subsequent text matching to partial mode.  For example:
\          FIND job cast  => Dan Rather ( newscaster )
\             PART is the initial state
\ WHOLE    Sets all subsequent text matching to whole mode.  For example:
\          FIND job news  => Not in file
\ CASE-SENSITIVE?  A value.  If false ( false is initial state) then subsequent
\           text searches are not case sensitive.  For example:
\           false to CASE-SENSITIVE? FIND given dan => Dan Rather
\           true  to CASE-SENSITIVE? FIND given dan => Not in file
\
\  Notes:
\   - All field sizes are automatically and dynamically allocated.  Any field
\     may be any size less than 255 chars (would be easy to increase that actually).
\   - An input file is comma delimited, just like using ENTER (spaces are allowed)
\   - The number of records is automatically and dynamically sized
\     (the maximum number of records is only limited by RAM and/or file size).
\   - The default field search is not case sensitive and will hit on
\     partial word searches.  See CASE-SENSITIVE?, PART, and WHOLE
\   - unlimited # of additional fields may be added by doing 3 things:
\     1) Add the KIND using MAKEKIND E.G.,  4 MAKEKIND city
\     2) Increment #ofFields E.G., 5 TO #ofFields
\     3) Then either start with a NEW file and ENTER the fields, or
\         use an editor program to add the fields directly to a text file.


0 [IF]

include e:\a-way-to-file.f

s" e:\my-data-file.txt" open

s" my-data-file.txt" open

\ 26 records read from file

print

\ Fillmore,Millard,president,NO PHONE
\ Lincoln,Abraham,president,NO PHONE
\ Bronte,Emily,writer,NO PHONE
\ Rather,Dan,newscaster,555-9876
\ Fitzgerald,Ella,singer,555-6789
\ Savitch,Jessica,newscaster,555-9653
\ Mc Cartney,Paul,songwriter,555-1212
\ Washington,George,president,NO PHONE
\ Reynolds,Frank,newscaster,555-8765
\ Sills,Beverley,opera star,555-9876
\ Ford,Henry,capitalist,NO PHONE
\ Dewhurst,Coleen,actress,555-9876
\ Wonder,Stevie,songwriter,555-0097
\ Fuller,Buckminster,world architect,555-7604
\ Rawles,John,philosopher,555-9702
\ Trudeau,Garry,cartoonist,555-9832
\ Van Buren,Abigail,columnist,555-8743
\ Abzug,Bella,politician,555-4443
\ Thompson,Hunter S.,gonzo journalist,555-9854
\ Sinatra,Frank,singer,555-9412
\ Jabbar,Kareem Abdul,basketball player,555-4439
\ Mc Gee,Travis,fictitious detective,555-8887
\ Didion,Joan ,writer,555-0009
\ Frazetta,Frank,artist,555-9991
\ Henson,Jim,puppeteer,555-0001
\ Sagan,Carl,astronomer,555-7070


find job news
\ Dan Rather
get job
\ newscaster

all

\ Dan Rather
\ Jessica Savitch
\ Frank Reynolds

close
\ my-data-file.txt file closed
\ heap memory FREEd

[THEN]

