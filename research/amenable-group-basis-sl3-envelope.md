---
rg: 2
id: amenable-group-basis-sl3-envelope
kind: claim
title: Embed the non-CE rigid factor in an amenable group-basis SL3 crossed product
distinct_from:
  algebraic-compact-action-envelope-for-non-ce-relation: that requires an abelian discrete kernel, equivalently a compact-abelian Haar base, and is subject to affine Fourier-moment tests; this permits a nonabelian amenable group kernel and uses its canonical group basis.
  non-ru-bcs-is-satisfiable-in-a-group-factor: that permits an arbitrary host group factor and asks only for one BCS model; this restricts the host to an amenable-by-SL3 semidirect product and asks to embed the fixed property-T relation factor.
---

Construct a countable amenable group `K`, an action

```text
SL_3(Z) -> Aut(K),
```

and a trace-preserving embedding of the fixed non-Connes-embeddable
property-`(T)` relation factor `N` into

```text
L(K) rtimes SL_3(Z) = L(K rtimes SL_3(Z)).              (AGB1)
```

Preferably `K` and its action are finitely generated/recursively presented
enough that the semidirect product has an effective presentation.

Unlike a compact-abelian Haar base, the hyperfinite algebra `L(K)` may be
noncommutative and can contain matrix blocks; the affine Fourier-binary test
does not apply to its noncommuting group basis.  The equality in `(AGB1)` is
nevertheless canonical, so any such embedding immediately makes
`K rtimes SL_3(Z)` non-hyperlinear.  Ordinary coinduction from the native
Haagerup actor cannot construct it; a direct `SL_3(Z)` group-basis action is
required.

## Attempts

- **Native Haagerup actor.**  Replacing the abelian base by `L(K)` does not
  help for the virtually-free source actor.  By
  `haagerup-actor-amenable-basis-rigidity-fence`, Popa's relative-H
  deformation intertwines any property-`(T)` subfactor into the amenable base,
  which is impossible.
- **Ordinary coinduction.**  The identity-coset coordinate in a coinduced
  amenable group basis generates the faithful source crossed product, not the
  singular Feldman--Moore quotient.  This is
  `amenable-basis-coinduction-cannot-create-envelope`; extra coordinates do
  not install the missing inclusion.
- **Why the direct `SL_3(Z)` branch remains live.**  An arbitrary semidirect
  product with amenable normal kernel and sofic quotient is *not* known to be
  sofic or hyperlinear; the invalid converse to the sofic-kernel/amenable-
  quotient theorem must not be used here.  Noncommutative `L(K)` also has
  matrix blocks and no affine Fourier-binary law.  What is missing is a direct
  `SL_3(Z)`-invariant regular group basis for an amenable factor whose crossed
  product contains `N`, not another change-of-actor construction.
