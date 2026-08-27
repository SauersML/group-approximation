---
rg: 2
id: sl2-homogeneous-action-is-not-treeable
kind: claim
title: The rank-one homogeneous-quotient orbit relation is not treeable
invalidates:
  - sl2-homogeneous-ce-via-global-treeing
distinct_from:
  non-ce-relation-is-not-treeable: that deduces non-treeability from non-Connes-embeddability; here Connes embeddability is open, and non-treeability is proved independently from a positive second L2-Betti number.
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that asks whether the relation algebra is Connes embeddable; a non-treeable relation may still have a Connes-embeddable algebra, so the present theorem does not decide it.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes finite equivariant refinements of one compact-orbit label; this excludes every measurable treeing of the entire essentially free orbit relation.
---

**THEOREM (established here; proof in
`sl2-homogeneous-nontreeability-proof`).**  Put

```text
A = SL_2(Z[1/2]),       L = SL_2(Q_2),
X = L/Lambda',
```

where `Lambda' < L` is a torsion-free cocompact lattice, and let `R_A` be
the orbit relation of the left `A`-action on `X`.  Then `R_A` is not
treeable.

Indeed, the action is essentially free, and

```text
beta_2^(2)(R_A) = beta_2^(2)(A) > 0.                    (HNT1)
```

The positivity follows because `A` is an S-arithmetic lattice in
`SL_2(R) x SL_2(Q_2)`: each rank-one factor has positive first L2-Betti
number, so the product has positive second L2-Betti number by the Kunneth
formula, and lattice proportionality transfers positivity to `A` (passing
between `SL_2` and `PSL_2` only changes the value by a finite factor).
Treeable p.m.p. relations have vanishing L2-Betti numbers in degrees at least
two, contradicting `(HNT1)`.

**Scope.**  This invalidates only the tempting proof that obtains Connes
embeddability of

```text
L^infinity(X) rtimes A
```

by exhibiting a global treeing and then applying
Brown--Dykema--Jung over the Cartan.  It does **not** refute Connes
embeddability.  The actual Bass--Serre decomposition is over the nonamenable
finite-index algebra `L^infinity(X) rtimes D`, and compatible non-Cartan
ultraproduct embeddings remain exactly the joint-spatialization problem of
`free-lattice-ce-is-joint-ultrapower-spatialization`.

DERIVATION
sl2-homogeneous-nontreeability-proof
