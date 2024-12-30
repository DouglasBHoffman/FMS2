December 30, 2024
Changed wordlist save-order and restore-order scheme to be compatible
with classes compiled in vocabularies. Ideas/code from Ruvim.
Also assured that all message names are created in the same
root wordlist as FMS.

September 13, 2023. Updated the Documentation somewhat so that explanations are clearer.

January 25, 2023. Eliminated :f ... ;f definitions due to possible problems in certain situations.
  Eliminated message-wid wordlist and added 254 c@ tag to identify messages. Overall simplification.

FMS2 is an object programming extension to ANS Forth. It is class based, single inheritance, uses Duck Typing, and explicit references to self.
FMS2VT uses virtual tables for fast late binding. FMSVT is about 30% faster than miniFMS on one of my benchmarks with a lot of late binding. This speed increase comes at the cost of code size and complexity. See the documentation for details.

miniFMS is my idea of a minimalist ANS Forth object extension.
 
Class based: The structure and behavior of an object are defined by a class, which is a definition or blueprint, of all objects of that specific type. 

Single inheritance: A new class can inherit instance variables and methods from just one class. 

Duck Typing: See the section on Duck Typing in this document.

Explicit references to self: Only used when defining a class. Methods can call other methods on the same object (including themselves), using a special keyword called self.

The approach taken with FMS is to bridge Forth with an oop extension that makes sense given the environment of Forth data types and dealing with the dictionary and heap.
