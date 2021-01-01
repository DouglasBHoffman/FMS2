\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Oct 28 2019 Douglas B. Hoffman
\ dhoffman888@gmail.com


[undefined] floats [if]
cr .( Floating Point is required) abort
[then]
[undefined] array [if] cr .( file array.f is required) abort [then]

[undefined] >integer [if] .( file utility-words.f is required) abort [then]

\ i{ arrays cannot be nested, the elements are not objects
: i{ ( -- array ) 
  heap> array locals| list |
	BEGIN
	   refilling-parse-name 2dup S" }" compare  
	WHILE
	 ( addr len )
	 2dup s" .." compare 0=
	 if \ we have a range
	   2drop refilling-parse-name
	     2dup >integer
	     if
	       1+ ( end-of-range )
	       list :last 1+ ?do i list :add loop 2drop
	     else list <free true abort" invalid integer in i{...}"
	     then
     else
       >integer if ( n ) list :add
            else list <free true abort" invalid integer in i{...}"
            then
     then
	REPEAT ( addr len ) 2drop list ; 


[defined] farray [if]

\ f{ arrays cannot be nested, array elements are not objects
: f{ ( -- fp-array )
  heap> farray
	BEGIN
	 ( obj )
	   refilling-parse-name 2dup s" }" compare 
	WHILE
	 ( obj addr len )
	     >float if ( obj ) ( R: r ) dup :add
	            else ( obj ) <free true abort" invalid number in f{...}"
	            then
	REPEAT ( obj addr len ) 2drop ;

 
[then]


\ for creating a list of space delimited strings
\ the strings cannot be nested, but they are string objects
: ${ ( -- array )  
  heap> array
	BEGIN
	 ( obj )
	   refilling-parse-name 2dup S" }" compare 
	WHILE
	 ( obj addr len )
      >string over :add
	REPEAT ( obj addr len ) 2drop ;

\ from Hans Bezemer via comp.lang.forth June-26-2013
\ thread: Simple Sort - the smallest sorting routine?
\ ref:  http://de.wikipedia.org/wiki/Simplesort
: simplesort ( ^elem0 n xt -- ) locals| xt |
  cells over + dup rot
  ?do
    dup i CELL+ ?do i @ j @ xt execute
    if i @ j @ i ! j ! then 1 cells +loop
  1 cells +loop
  drop ;

: sort$s ( xt arr -- ) locals| arr xt |
  0 arr :^elem arr :size xt simplesort ;  

0 [if]

${ now is the time for all good men } value s1

\ or could also use:
\ o{ 'now' 'is' 'the' 'time' 'for' 'all' 'good' 'men' } value s1
\ s1 :. \ { 'now' 'is' 'the' 'time' 'for' 'all' 'good' 'men' }

[: :. space ;] s1 :apply \ => now is the time for all good men

[: swap :@ rot :@ compare 1 < ;] s1 sort$s

[: :. space ;] s1 :apply \ => all for good is men now the time

[then]