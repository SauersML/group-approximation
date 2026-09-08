---
rg: 2
id: smith-prime-localization-maximality-and-word-transfer
kind: claim
title: The integral special linear subgroup is algebraically maximal in a one-prime localization, with finite-word commutator transfer
distinct_from:
  arithmetic-pair-group-factor-ultrapower-has-no-leak: that proves a conjugation spectral gap inside the canonical group-factor ultrapower; this proves exact algebraic maximality and transfers a fixed commutator leak in any tracial representation, without a spectral-gap assumption.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that characterizes an HNN model by the full distribution of a stable letter; this identifies the exact stabilizer of any subgroup-central leak for the arithmetic pair, without constructing such a model.
artifacts:
  - research/artifacts/smith-prime-localization-maximality-audit-2026-09-07.md
---

Let p be any prime, n>=2, C=SL_n(Z), and A=SL_n(Z[1/p]). Then C is a
maximal proper subgroup of A. Equivalently,

    <C,g>=A for every g in A minus C.                      (SPL1)

This is algebraic maximality, with no closedness or topology hypothesis.
It includes n=3 with p=2 or p=11. It is a known fact: Gelander--Meiri,
*Maximal subgroups of SL(n,Z)*, arXiv:1511.05767, Section 7, discussion of
Question 7.1, records it explicitly; Cornulier, *Finitely presented wreath
products*, Remark 3.3, records the n=2 case for every prime. The route
supplies a full Smith-normal-form proof.

There is a quantitative finite-word consequence. Fix g,h in A minus C.
There is an integer L_(g,h)>=1, depending only on these two matrices,
such that, for every finite tracial von Neumann algebra M, every exact
unitary representation pi:A->U(M), and every e in M commuting with pi(C),

    ||[e,pi(h)]||_2 <= L_(g,h) ||[e,pi(g)]||_2.           (SPL2)

No projection assumption on e is needed for this inequality. One can take
L_(g,h) to be the number of g or g^(-1) letters in a word for h over
C union {g,g^(-1)}. The proof gives the explicit choice

    L_(g,h)=2 p^(m-1) sum_(r=1)^(n-1) |b_r|,             (SPL3)

where diag(p^(a_1),...,p^(a_n)) and diag(p^(b_1),...,p^(b_n)) are
determinant-one Smith diagonals for g and h, and m=a_j-a_i>0 is any
positive exponent difference for the first diagonal. No bound uniform
over all g is asserted.

Consequently, if e commutes with pi(C) but fails to commute with one
pi(h), its exact commutation stabilizer in A is C. This applies in
particular to a projection in any canonical actor model. For such a
projection, putting B={e}' cap M also gives

    ||E_B(pi(g))||_2^2
        <= 1-||[e,pi(h)]||_2^2/L_(g,h)^2 < 1             (SPL4)

for every g outside C. This supplies a definite contraction for each
fixed outside element; it does not provide a uniform contraction over
the entire complement, nor does it construct a leak.
