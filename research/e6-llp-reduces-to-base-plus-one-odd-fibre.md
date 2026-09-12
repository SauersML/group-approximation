---
rg: 2
id: e6-llp-reduces-to-base-plus-one-odd-fibre
kind: claim
title: LLP of the degree-six Deligne cover is exactly base LLP plus one odd twisted fibre
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: that asks for LLP of the remaining odd fibre; this identifies that fibre as the only new LLP gate in the degree-six extension over the residually finite metaplectic base.
  maslov-mod3-gap-is-metaplectic-base-degree-six-gap: that is the Connes-embedding and projective-defect equivalence for E3 and E6; this is the full C-star LLP decomposition of E6.
  metaplectic-half-shift-preserves-twisted-fibre-llp: that pairs individual twisted fibres under a half shift; this combines that pairing with inversion and the six central Fourier summands.
---

**ESTABLISHED.**  Let `A_theta` be the full Maslov twisted group C-star
algebra of `Sp_4(Z)`.  The degree-six Deligne cover has

```text
C^*(E_6) = direct_sum_(j=0)^5 A_(j/6).
```

Then

```text
C^*(E_6) has LLP
 iff A_0 has LLP and A_(1/6) has LLP
 iff A_0 has LLP and A_(1/3) has LLP.                  (E6L1)
```

Thus the invisible central extension

```text
1 -> Z/3 -> E_6 -> E_2 -> 1
```

does not introduce six independent lifting problems.  Exact metaplectic
half-shift and opposite-algebra symmetry collapse them to the untwisted base
fibre and one odd fibre.  The latter is exactly the already isolated
`sp4-mod3-twisted-fibres-have-llp` gate.  Residual finiteness and property
`(T)` of `E_2` alone do not settle that remaining fibre.

The proof is `e6-llp-two-orbit-fibre-proof`.
