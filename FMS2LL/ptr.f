
\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.
\ Feb 8, 2021 Douglas B. Hoffman
\ dhoffman888@gmail.com

:class ptr 
 cell bytes data
 cell bytes len \ len, in bytes, of memory allocated
 :m :size ( -- n )  len @ ;m
 :m :free data @ free throw ;m
 
 :m :resize  ( newsize -- ) 
    dup data @ swap resize throw  data !  len !  ;m

 :m :init ( size -- )
      dup allocate throw data ! len ! ;m
;class




