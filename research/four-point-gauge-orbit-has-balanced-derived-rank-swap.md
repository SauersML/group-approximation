---
rg: 2
id: four-point-gauge-orbit-has-balanced-derived-rank-swap
kind: claim
title: Two complementary D8 pairs keep one Pauli rank across both reset signs on four gauge points
distinct_from:
  regular-gauge-orbit-contains-equal-scale-derived-d8-reset: that makes the reset translation one central commutator and identifies its negative spin sector; this adds the complementary `J s` commutator so the total active Pauli rank is constant in both selector sectors.
  weyl-derivative-reset-preserves-schur-spin-scale: that keeps the full derivative packet at baseline scale; this supplies an explicit ordinary-word replacement for one selector-dependent hyperbolic pair.
---

Let `J=-I`, let `s` be an involution with equal signs, and write

```text
E_+=(1+s)/2,
E_-=(1-s)/2.
```

On the four-dimensional gauge block
`(E_+ H tensor C^2) direct_sum (E_- H tensor C^2)`, define

```text
p_- = E_+ tensor I + E_- tensor X,
q_- = E_+ tensor I + E_- tensor Z,

p_+ = E_+ tensor X + E_- tensor I,
q_+ = E_+ tensor Z + E_- tensor I.                  (GRS1)
```

These are four involutions in a fixed finite signed-permutation group.  The
two pairs commute with each other, while

```text
[p_-,q_-]=s,
[p_+,q_+]=J s.                                      (GRS2)
```

Consequently:

- in the `s=+1` sector, `(p_+,q_+)` is one anticommuting Pauli pair and
  `(p_-,q_-)` is trivial;
- in the `s=-1` sector, `(p_-,q_-)` is one anticommuting Pauli pair and
  `(p_+,q_+)` is trivial.

Exactly one hyperbolic pair is therefore active in either selector sector.
The reset coefficient `s` and its complementary coefficient `Js` are both
literal commutators, but the spin dimension does not jump with the selector.
No tensor dimension is added beyond the four-point gauge orbit already used
to covariantize the marked exact representation.

Abstractly the generated packet has presentation

```text
J,s central involutions,
p_eps^2=q_eps^2=1,
[p_-,q_-]=s,
[p_+,q_+]=Js,
all cross commutators trivial.                       (GRS3)
```

It is a finite class-two `2`-group.  Thus `(GRS1)` is only the exact
completeness model; finite-dimensional soundness may exactify the ordinary
finite group `(GRS3)` directly.

This packet removes the last *one-pair* scale ambiguity in the derived reset.
For a rank-`N` Schur baseline it can replace one hyperbolic pair while a common
rank-`N-1` residual packet carries the remaining pairs.

`fanizza-schur-menu-has-common-codimension-one-residual` now supplies fixed
rank-fifteen hyperplanes for the universal arity-four menu and a compatible
reset direction.  What remains is the finite incidence implementing the
sectorwise symplectic congruences of those nondegenerate residual forms.
