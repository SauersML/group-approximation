---
rg: 2
id: mf-radical-godel-word-via-proof-search
kind: route
title: Halt on a proof of the fixed point's nontriviality
target: mf-radical-godel-word
requires: [single-finitely-presented-mf-radical-computer, computable-proof-system-kleene-interface]
---

Given an index `e`, enumerate `T`-proofs and halt when a proof of `r_e != 1`
appears.  A Kleene fixed point `e_T` for this program cannot halt: soundness
would make `r_(e_T)` nontrivial, whereas the radical computer makes the word
trivial exactly on halt.  Nonhalting then makes the word nontrivial, and every
word in the family is MF-invisible independently of the fixed point.

The only open input is the named formal proof-system/recursion interface.
