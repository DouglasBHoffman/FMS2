FMS2 is an object programming extension to ANS Forth. It is class based, single inheritance, uses Duck Typing, and explicit references to self.
FMS2VT uses virtual tables for binding. FMSLL uses linked lists for binding. FMSVT is about 30% faster than FMSLL on one of my benchmarks with a lot of late binding. This speed increase comes at the cost of some code complexity. See the documentation for details.

miniFMS is my idea of a minimalist ANS Forth object extension.
 
Class based: The structure and behavior of an object are defined by a class, which is a definition or blueprint, of all objects of that specific type. 

Single inheritance: A new class can inherit instance variables and methods from just one class. 

Duck Typing: See the section on Duck Typing in this document.

Explicit references to self: Only used when defining a class. Methods can call other methods on the same object (including themselves), using a special keyword called self.

The approach taken with FMS is to bridge Forth with an oop extension that makes sense given the environment of Forth data types and dealing with the dictionary and heap.
