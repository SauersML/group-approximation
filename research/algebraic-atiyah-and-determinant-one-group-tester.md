---
rg: 2
id: algebraic-atiyah-and-determinant-one-group-tester
kind: claim
title: One two-generator nonsofic group tests algebraic Strong Atiyah together with the determinant conjecture
distinct_from:
  two-generator-fp-torsion-free-master-tester: that lists algebraic, assembly and Whitehead equivalences for the same host; this adds the analytic pair of Strong Atiyah over the algebraic numbers and the determinant conjecture, which needed a new colimit permanence theorem.
  luck-determinant-fixed-two-generator-tester: that tests the determinant conjecture alone on an all-group host with torsion; this tests its conjunction with Strong Atiyah on a torsion-free host.
  universal-torsion-free-subgroup-colimit-class-tester: that is the abstract closure principle; this is its instance for one analytic class, whose permanence is proved separately.
  algebraic-atiyah-with-determinant-closed-under-colimits: that is the permanence theorem for the class; this is the resulting one-group equivalence and its dichotomy.
---

There is one two-generator finitely presented torsion-free group `E`, which
may be chosen nonsofic and non-MF, such that

```text
SA(E) and Det(E)   <=>   SA(G) and Det(G) for every torsion-free group G,
```

where `SA` is the Strong Atiyah Conjecture over `Qbar` and `Det` is Lueck's
determinant conjecture, as in
`algebraic-atiyah-with-determinant-closed-under-colimits`.  `E` may be taken
to be the witness of `two-generator-fp-torsion-free-master-tester`.

## Consequences

1. **Two properties of one group.**  Strong Atiyah over `Qbar` for every
   torsion-free group follows from `SA(E)` together with `Det(E)`.
2. **Dichotomy.**  If `SA(E)` holds, then either every torsion-free group
   satisfies `SA`, or `Det` fails for an explicit integral matrix over a
   finitely generated recursively presented torsion-free subgroup of `E`.
   Precisely: let `H` be torsion-free and `A in M_(m,n)(Qbar[H])` have
   algebraic integer coefficients in a Galois number field of degree `d`, and
   suppose `dim ker r_A` has fractional part `eta > 0`.  Choose `lambda` with
   `c lambda < 1` and `md log(kappa) / |log(c lambda)| < eta / 2`, with
   `kappa` and `c` from the colimit proof.  Then some stage `K_j <= E` of a
   recursively presented directed system with colimit `H` has
   `det_(N(K_j)) r_(rho(A_j)) < 1`, where `rho(A_j)` is the lifted matrix after
   restriction of scalars.
3. **Where such a failure would sit.**  The determinant conjecture holds for
   sofic groups (Lueck, arXiv:2102.04549v2, Remark 3.11), so the subgroup in
   the second branch is nonsofic.  By
   `universal-torsion-free-hosts-not-sofic-or-locally-indicable`, `E` lies
   outside every class for which Strong Atiyah or the determinant conjecture
   is proved by the methods recorded there.

## What it does not give

Nothing over `C`.  The determinant bound controls algebraic coefficients
only, and the known base change from `Qbar` to `C` (Jaikin-Zapirain, GAFA 29
(2019), Theorem 1.1, cited as such in arXiv:2201.03268, Remark 3.8) assumes
the group is sofic; see `strong-atiyah-base-change-algebraic-to-complex`.  It
proves neither `SA(E)` nor `Det(E)`.  The continuity argument is classical;
what is new is the permanence of the conjunction and its combination with the
torsion-free universal host.

**ESTABLISHED 2026-09-11** by [[algebraic-atiyah-determinant-tester-proof]].
