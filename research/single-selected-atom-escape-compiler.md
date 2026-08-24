---
rg: 2
id: single-selected-atom-escape-compiler
kind: claim
title: A one-piece HS escape cell yields a finite supercritical carrier contradiction
distinct_from:
  branching-plus-first-hit-exits-forces-hs-floor: That uses many pairwise orthogonal first-hit exits; this grows one reducing hull by adjoining only the maximal forbidden piece at each step.
  contractive-computation-ladder: That is an abstract scalar contraction estimate; this constructs the scalar recurrence from projection join and invariant hull operations.
---

**ESTABLISHED CONDITIONAL COMPILER.**  If
`single-selected-atom-hs-escape` is realized by a finite ordinary-group
extension, then its marked central involution `J` is nontrivial in an exact
finite-tracial representation but is trivial in every normalized-HS
approximate representation.  Hence the presented group is nonhyperlinear.

The initialization must use a proper canonical half of the marked sector,
not the whole `Q_-`.  Adjoin a seed Pauli pair `B,C`, commuting with the BCS
and selector tuple, with

```text
B^2=C^2=1,       [B,C]=J.                              (SEC1)
```

After fixed finite rounding put

```text
Q_0=Q_-(1+B)/2.                                        (SEC2)
```

Conjugation by `C` exchanges the two `B` halves of `Q_-`, so

```text
tau(Q_0)>=||rho(J)-1||_2^2/8-C_0 sqrt(E).              (SEC3)
```

Given `Q_n`, select `A_n` by `(MFA2)`, put
`D_n=U_(i_n)A_nU_(i_n)^*`, and let `Q_(n+1)` be the smallest reducing
subspace for the finite global shared-variable and selector tuple containing
`Q_n join D_n`.  All escape words preserve `Q_-`, so `Q_(n+1)<=Q_-`.
For projections,

```text
tau(Q_n join D_n)
 =tau(Q_n)+tau(A_n)-tau(Q_n meet D_n)
 >=tau(Q_n)+eta tau(A_n)-C sqrt(E),                    (SEC4)
```

because `tau(Q_n meet D_n)<=tau(Q_nD_n)`.  Therefore, with
`gamma=eta beta/(2M)>0`,

```text
tau(Q_(n+1))>=(1+gamma)tau(Q_n)-C' sqrt(E).             (SEC5)
```

Iterate only a fixed number `N`.  Since `tau(Q_N)<=1`, `(SEC3)--(SEC5)`
contradict arbitrarily small relator energy whenever `rho(J)` stays a fixed
positive distance from `1`.  In the exact infinite model use the same Pauli
construction for `(SEC1)`; all forbidden selected pieces vanish, so the
escape extension remains consistent and `J=-1` survives.

Starting with `Q_0=Q_-` would be invalid: a `J`-preserving unitary cannot
escape the whole marked sector, while a nonpreserving unitary would make the
next hull ineligible for the compressed BCS gap.  The seed split `(SEC1)` is
therefore load-bearing.

