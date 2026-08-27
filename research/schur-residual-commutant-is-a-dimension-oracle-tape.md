---
rg: 2
id: schur-residual-commutant-is-a-dimension-oracle-tape
kind: claim
title: The residual Schur multiplicity commutant is exactly the matrix tape detected by Amitsur--Levitzki
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  schur-flip-cells-expose-residual-matrix-tape: that identifies the residual algebra as `M_L(C)` and computes the divisibility cost of new cells; this supplies a concrete endogenous instruction which must fail at that same residual dimension.
  two-generator-amitsur-levitzki-dimension-oracle: that is an abstract free-algebra statement; this places its letters in the commutant left by already paid Schur flip cells.
---

In the decomposition `(RMT1)`, two tape elements centralizing the old
cancellation algebra have the form

```text
I_(2^n) tensor X,              I_(2^n) tensor Y,
X,Y in M_L(C).                                                   (SAT1)
```

For the polynomials `(ALO1)`, their `L`th instruction therefore satisfies

```text
p_L(I tensor X,I tensor Y)=I_(2^n) tensor p_L(X,Y)=0.             (SAT2)
```

Thus arbitrary spectator amplification does not erase the dimension signal;
it moves the forced-zero instruction from `L` to a later finite address.  If a
single finitely compiled tape attempts `(ALO4)` inside the residual commutant,
every finite matrix microstate necessarily reaches a failed instruction.

This is exact algebraic detection only.  A useful group compiler must turn
that failure into more than `log_2L` independent Schur cells—or directly into
a marked-word collapse—with normalized-HS cost independent of `L` and of the
instruction runtime.

