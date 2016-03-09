Basic fuzzy logic in Isabelle/HOL
=================================

Formalization of prof. Petr Hájek's Basic fuzzy logic in Isabelle/HOL.

The original code is taken from my bachelor's thesis (submitted in Aug 2014, defended in Feb 2016 at Charles University in Prague, Faculty of Arts, Department of Logic).

The thesis consists of a brief introduction to Basic Fuzzy Logic and a description of the code. It also contains a short tutorial on proving in Isabelle/HOL for potential users or followers of this very basal piece of the upcoming Fuzzy Logic Formalization project.

NOTE: The code is being prepared for publishing in Isabelle's.

Presented theories contain:

BasicLogic.thy
- formalization of the objects of BL: formula, multiple conjunction, deducibility closure, relation of provability 

BL_theorems.thy
- formalized proofs in Hilbert-like calculus of BL and the declarations of rules of inference in the calculus

BL_LocalDeduction.thy
- formalized proofs of the meta-theorems of BL: Local Deduction, Monotonicity of provability, Derivation of multiple conjunction

The definitions of the formalized object and some of the proofs are (mostly) from:

- Petr Hájek: Metamathematics of Fuzzy Logic, Springer, 1998
- Libor Běhounek, Petr Cinutla, Petr Hájek: Introduction to Mathematical Fuzzy Logic, Chapter I in Handbook of Mathematical Fuzzy Logic, Vol.1, Collage Publications, 2011 
