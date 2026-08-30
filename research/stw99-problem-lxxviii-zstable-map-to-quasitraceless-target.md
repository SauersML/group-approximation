---
rg: 2
id: stw99-problem-lxxviii-zstable-map-to-quasitraceless-target
kind: claim
title: Every unital map from a simple nuclear Z-stable algebra to a quasitraceless target is O-infinity-stable (STW Problem LXXVIII)
root: true
---

**Problem LXXVIII of Schafhauser--Tikuisis--White, _Nuclear C\*-algebras:
99 problems_, arXiv:2506.10902v2.**  Let `A` be unital, simple, separable,
nuclear, and `Z`-stable, and let `B` be unital with no normalized quasitraces.
Must every unital \*-homomorphism

```text
phi : A -> B
```

be `O_infinity`-stable?

This remains open.

Every counterexample now reduces to a finite-generator target extension:
`stw78-counterexamples-have-finite-obstruction-targets` gives

```text
B_0=C*(phi(A),b_1,...,b_m)
```

with `B_0` separable and still quasitraceless, while retaining a positive
finite-set central-isometry defect.  The key compactness theorem is that
absence of normalized 2-quasitraces is witnessed by a finitely generated
unital subalgebra.

## Attempts

An irreducible embedding into `B(H)` is not a counterexample merely because
its ordinary relative commutant is scalar.  The definition uses the sequence
relative commutant, and
`stw99-lxxviii-essential-representation-central-o2`
records that Voiculescu absorption puts a unital `O_2` there.

The direct negative route is instead
`stw99-lxxviii-finite-target-obstruction`: find a
finite unital quasitraceless `B` containing a unital copy of some domain `A`
as above.  No such inclusion is presently constructed.  Tensoring a known
finite non-stably-finite algebra by `Z` is not a repair: in the exact simple
traceless setting, `Z`-absorption forces pure infiniteness and destroys
finiteness.

Problem LXVI is linked directly to this negative route.
`stw99-lxvi-witness-refutes-lxxviii` proves that any LXVI witness cuts down
to a finite quasitraceless CAR-containing algebra, whose unital CAR inclusion
violates `O_infinity`-stability.  Hence a positive answer here would force a
negative answer to LXVI, while a positive LXVI construction would refute this
problem.

On the positive side, `O_infinity`-stability forces every nonzero element of
the image to be properly infinite.  Establishing that conclusion from the
absence of quasitraces is already a substantive missing comparison step; even
after it, the map-level upgrade is closely tied to Problem LXXVII.
