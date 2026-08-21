---
rg: 2
id: reverse-kleene-involutive-compiler-gives-non-mf
kind: claim
title: A reverse-Kleene involutive HS-collapse compiler yields a finitely presented non-MF group
distinct_from:
  kleene-halting-mark-collapse-diagonal: That compiler theorem uses the same fixed point to contradict hyperlinear canonical-trace microstates directly; this adds a fresh sign-twist HNN wrapper and concludes failure of operator-MF.
  dimension-matched-kleene-microstate-diagonal: That searches for a finite microstate and attacks its reported dimension; this reverse diagonal enumerates a van Kampen proof of triviality and needs no dimension detector.
  central-sign-corona-obstruction: That obtains the collapse mark from property-(T) commutant transport; this obtains it from self-referential computation and then uses `hs-collapse-sign-twist-non-mf`.
---

Assume a total computable compiler sends every Turing-machine index `e` to

```text
(Gamma_e=<S_e|R_e>, w_e, delta_e, alpha_e),
```

where `w_e` is an involution in `Gamma_e`, `delta_e>0`, and
`alpha_e<sqrt(2)`, with the two semantic clauses

```text
machine e halts
  => w_e!=1 in Gamma_e,                                      (RKM1)

machine e does not halt
  => Def_(R_e)(U)<delta_e implies
     ||w_e(U)-I||_2<=alpha_e                                 (RKM2)
```

for every finite-dimensional unitary tuple `U`.  The defect in `(RKM2)` is
normalized Hilbert--Schmidt defect.  The constants may depend computably on
`e`.

Then one can effectively construct a finitely presented group which is not
CDE/operator-MF.

## Fixed point

For each `e`, compute `(Gamma_e,w_e)` and run the standard recursively
enumerable word-problem procedure which lists finite van Kampen consequences
of `R_e`, halting exactly when it finds a proof

```text
w_e=1 in Gamma_e.                                            (RKM3)
```

Kleene's recursion theorem supplies an index `e_*` whose machine has exactly
that behavior for its own compiled pair `(Gamma_(e_*),w_(e_*))`.

If `e_*` halted, `(RKM3)` would prove `w_(e_*)=1`, whereas `(RKM1)` applied to
the same halting machine would give `w_(e_*)!=1`, a contradiction.  Hence
`e_*` does not halt.  Since its behavior is precisely the proof enumeration,
no proof of `w_(e_*)=1` exists; completeness of van Kampen enumeration gives

```text
w_(e_*)!=1 in Gamma_(e_*).                                   (RKM4)
```

Clause `(RKM2)` now applies to the same fixed index.  Thus the finite
presentation `Gamma_(e_*)` and involutive word `w_(e_*)` satisfy exactly the
hypotheses of `hs-collapse-sign-twist-non-mf`.

## Norm wrapper

Adjoin a fresh central involution `z` and stable letter `a`:

```text
H_* = < S_(e_*),z,a |
          R_(e_*),
          z^2=1,
          [z,s]=1                     (s in S_(e_*)),
          [z,a]=1,
          a w_(e_*) a^-1 = z w_(e_*) >.                      (RKM5)
```

The sign-twist theorem embeds `Gamma_(e_*) x <z>` in `H_*`, so `z!=1`, and
proves that every homomorphism from `H_*` to a norm matrix corona kills `z`.
Consequently `H_*` is finitely presented and non-MF.

This proof is computational/self-referential: the nontrivial source mark is
selected by the reverse Kleene fixed point, while the final operator-norm
obstruction is the sign-twist trace flip.  It uses neither the existing
property-(T) non-MF construction nor its asymptotic-commutant argument.

## Current instantiation status

The logical reduction above is complete.  It is **not yet an unconditional
second construction** in Cairn because the intended Fanizza instantiation
`fanizza-native-signal-groupification` is still open: that node supplies the
required HALT survival and NONHALT HS-collapse only once the nonlinear BCS
signal has been compiled into ordinary group-word relations with a
finite-matrix decoder modulus.  The present theorem removes the MF endpoint
from the list of missing steps; it does not silently assume that compiler.
