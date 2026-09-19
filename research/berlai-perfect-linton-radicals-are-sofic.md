---
rg: 2
id: berlai-perfect-linton-radicals-are-sofic
kind: claim
title: The Baumslag--Berlai groups have explicit nontrivial perfect sofic Linton radicals
distinct_from:
  linton-radical-sofic: that asks for every Linton radical to be sofic and remains open; this establishes the hardest-looking perfect-radical conclusion for the explicit Baumslag--Berlai family only.
  residually-rationally-solvable-one-relator-sofic: that assumes the Linton radical is trivial; these groups have a nontrivial perfect Linton radical and are not even residually solvable.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that controls the quotient modulo `R'`, which is just the cyclic quotient for this perfect family; this proves soficity of the whole nonabelian `R=R'` and of its coupling to the cyclic shell.
  magnus-staggered-chain-sofic: that asks for every Magnus chain, including nonamenable free overlaps, to be sofic; this closes the residue-class chains of one explicit family by reducing them to cyclic-edge HNN extensions.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Use `x^y=y^(-1)xy`.  For `n!=0` and `l notin {0,-1}`, put

    B_(n,l) = <a,b | (a^l)^(a^(b^n)) = a^(l+1)>.

Let `chi:B_(n,l)->Z` send `a` to `0` and `b` to `1`, and put
`R=ker(chi)=<<a>>`.  Then:

1. `R` is nontrivial, perfect, infinitely generated, and sofic;
2. `R=B_(n,l)_Q^(omega)`, so it is exactly the Linton radical;
3. `B_(n,l)` is sofic but not residually solvable.

Thus a nontrivial perfect Linton radical and its shell action can both be
sofic.  This is the canonical calibration against treating perfectness, or
the failure of all solvable quotient tests, as evidence for a negative answer
to the one-relator soficity problem.
