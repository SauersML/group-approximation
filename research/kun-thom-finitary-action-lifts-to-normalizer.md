---
rg: 2
id: kun-thom-finitary-action-lifts-to-normalizer
kind: claim
title: The explicit Kun--Thom action on the finitary symmetric factor has a trace-correct homomorphic lift to the normalizer of R in its ultrapower
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
distinct_from:
  hyperlinear-wreath-model: that asks directly for canonical microstates of the abelian-lamp wreath; this asks for a homomorphic normalizer lift of the larger finitary-symmetric action, which is sufficient but not known to follow from wreath hyperlinearity.
  invariant-cartan-completion: that tries to recover a normalized abelian lamp algebra from an arbitrary embedding; here the base is already the hyperfinite factor and the unknown is a nonabelian cocycle splitting in its ultrapower normalizer.
  kt-two-positive-compressors-generate-full-obstruction: that identifies why the two one-compressor permutation constructions cannot be pasted; this is the positive lifting statement in which the same incompatibility appears as a cocycle in `U(R' cap R^omega)`.
---

Let `Gamma < G` be the Kun--Thom pair, `X=G/Gamma`,
`Y=X x {0,1}`, and

```text
R = L(Sym_fin(Y)).
```

The permutation action of `G` on `Y` induces an action
`alpha:G->Aut(R)`.  There is a homomorphism

```text
u:G -> N_(R^omega)(R)
```

such that `Ad(u_g)|_R=alpha_g` and

```text
tau(x u_g)=0                    (x in R, g != 1).       (KFL1)
```

Equivalently, by `finitary-extension-ce-iff-action-lifts-to-normalizer`,
the explicit crossed product `R rtimes_alpha G` is Connes embeddable.
For every subgroup on which nonidentity elements move infinitely many
points of `Y`, the action is outer and `(KFL1)` is automatic; on that
subgroup the content is exactly that the pullback of

```text
1 -> U(R' cap R^omega) -> N_(R^omega)(R) -> Aut(R) -> 1
```

splits.  The full claim retains `(KFL1)` so it does not assume that every
actor element has infinite support.

This is OPEN.  Choosing individual lifts costs nothing by approximate
innerness of automorphisms of `R`; making them multiplicative is the entire
nonabelian cocycle problem.  The natural finite-quotient lift of the Kazhdan
subgroup is incompatible with the compressor relations, so a proof needs a
genuinely exotic simultaneous lift for the two named compressors.

