---
rg: 2
id: coinduction-preserves-but-cannot-create-algebraic-envelope
kind: claim
title: Coinduction preserves an algebraic envelope but the induction corner is only semifinite
distinct_from:
  algebraic-compact-action-envelope-for-non-ce-relation: that asks for the missing finite tracial algebraic envelope; this proves that the standard change-of-actor constructions cannot manufacture it from a nonalgebraic p.m.p. base.
  haar-algebraic-actions-have-permutation-koopman-spectrum: that obstructs measurable factors by Koopman spectrum; this computes the crossed-product inclusions and traces for induction and coinduction directly.
---

Let `H < Lambda` have infinite index, and let `H` act by continuous
automorphisms on a nontrivial compact second-countable abelian group `K_0`.
Put `B_0=L^infinity(K_0,m_0)`, where `m_0` is Haar measure.

The compact algebraic coinduction

```text
K = K_0^(Lambda/H)
```

with product Haar measure gives a trace-preserving inclusion

```text
B_0 rtimes H  ->  L^infinity(K) rtimes Lambda.          (CPC1)
```

Thus coinduction is useful only after the `H`-base is already algebraic.  It
does not turn an arbitrary p.m.p. `H`-space into a Haar algebraic one.

The superficially stronger corner construction belongs instead to the
measure-theoretic induced algebra

```text
B_ind = ell^infinity(Lambda/H) tensor B_0.
```

Its natural invariant trace uses counting measure on `Lambda/H` and is
semifinite.  If `p` is the characteristic projection of the base coset, then

```text
p (B_ind rtimes Lambda) p  =  B_0 rtimes H,             (CPC2)
```

but no `Lambda`-invariant probability measure can give every coset the same
positive mass when `[Lambda:H]=infinity`.

Nor can `(CPC2)` be copied into the probability algebra of compact
coinduction by freezing all off-base coordinates at the identity: that
"vacuum tail" has product-Haar measure zero.  Therefore standard
induction/coinduction and coset-corner manipulations do not import the known
non-CE relation factor into an algebraic probability crossed product.  A
successful change of actor still needs an algebraic envelope before
coinduction, or a genuinely non-coordinate/non-Cartan inclusion.
