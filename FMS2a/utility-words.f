\ utility words
: isdigit ( char -- flag ) \ true if 0 thru 9, false otherwise
  48 58 within ;

\ convert given stringÊto a signed decimal integer
: >integer ( addr len  -- n t | f)
  dup 0= if nip exit then
  0 1 0 locals| neg? dec accum len addr |
  addr c@ [char] - = to neg?
  len 1+ neg? + 1 ?do
   addr len + i - c@ dup isdigit
     if ( it's a digit 0 thru 9 )
        48 - dec * accum + to accum
        dec 10 * to dec
     else  drop false unloop exit 
     then
  loop accum neg? if negate then true ;


[undefined] parse-name [if]
: isspace? ( c -- f )
    bl 1+ u< ;

: isnotspace? ( c -- f )
    isspace? 0= ;

: xt-skip   ( addr1 n1 xt -- addr2 n2 ) \ gforth
    \ skip all characters satisfying xt ( c -- f )
    >r
    BEGIN
	dup
    WHILE
	over c@ r@ execute
    WHILE
	1 /string
    REPEAT  THEN
    r> drop ;

: parse-name ( "name" -- c-addr u )
    source >in @ /string
    ['] isspace? xt-skip over >r
    ['] isnotspace? xt-skip ( end-word restlen r: start-word )
    2dup 1 min + source drop - >in !
    drop r> tuck - ;
[then]

: refilling-parse-name ( -- c-addr u )
	begin
	   parse-name dup 0= 
	while
	  2drop refill 0= -39 and throw
	repeat ;
