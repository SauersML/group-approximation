---
rg: 2
id: fixed-separation-hamming-is-not-weak-soficity-proof
kind: route
title: Read the structure's target off the Lean, then separate the classes with the Kun--Thom wreath
target: fixed-separation-hamming-is-not-weak-soficity
requires: [weakly-sofic-not-sofic]
artifacts:
  - GroupApproximation/Sofic/SoficAmplification.lean
---

**The target class.**  Read directly from
`GroupApproximation/Sofic/SoficAmplification.lean` on 2026-08-17:
`WeakSoficModel G F δ ε` carries `carrier : FiniteModel`,
`map : G → Equiv.Perm carrier`, and both laws stated in
`hammingDistance carrier`, with `separated` requiring
`δ ≤ hammingDistance carrier (map g) (map h)`.  Compare `SoficModel` in
`GroupApproximation/Sofic/Sofic.lean`, identical except that the separation
bound is `1 - ε`.  So the target is `Equiv.Perm` with normalized Hamming
distance in both cases, and no other finite group or metric occurs.

**The equivalence with soficity.**  The same file proves
`isSofic_iff_weak (hδ0 : 0 < δ) (hδ1 : δ < 1) : IsSofic G ↔ IsSoficWeak G δ`,
via `soficModel_of_weak`: a positive separation that does not shrink
amplifies to `1 - ε` by passing to a tensor power whose exponent depends only
on `δ` and the target accuracy.  Hence `IsSoficWeak` decides exactly the
sofic class.

**Strictness.**  A finite symmetric group with normalized Hamming metric is a
finite group with a bi-invariant metric, so `IsSofic G` implies `G` is weakly
sofic in the Glebsky--Rivera sense.  `weakly-sofic-not-sofic` supplies the
Kun--Thom wreath `W = (⊕_(G/Γ) Z/2Z) ⋊ G`, which is weakly sofic and not
sofic.  Therefore `¬ IsSofic W`, hence `¬ IsSoficWeak W δ` for every
`δ ∈ (0,1)`, while `W` is weakly sofic.  The implication is strict, and the
name collision is between two genuinely different classes.

**Not a Lean error.**  Nothing above contradicts any theorem in the file; the
amplification results are correct for the fixed-separation convention they
state.  The claim is about which class the identifier names.
