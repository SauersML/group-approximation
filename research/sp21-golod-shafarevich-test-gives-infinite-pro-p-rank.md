---
rg: 2
id: sp21-golod-shafarevich-test-gives-infinite-pro-p-rank
kind: claim
title: A finite-index subgroup of an Sp(n,1) lattice with mod-p H^2 below a quarter of (mod-p H^1)^2 has infinite-rank pro-p completion
distinct_from:
  sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel: that identifies finite rank with a finite pro-p congruence kernel; this is a homological certificate that forces infinite rank, and with that claim an infinite pro-p congruence kernel
  fpbs-power-p-deficiency-excludes-property-t: that excludes power p-deficiency for Kazhdan groups; this uses the Golod-Shafarevich condition, which Kazhdan groups can satisfy
artifacts:
  - research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md
---

**ESTABLISHED.** Let `Γ` be as in
`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`, and let `p` be a prime.
Suppose some finite-index `Δ <= Γ` has

```text
d = dim H^1(Δ;F_p) >= 2   and   dim H^2(Δ;F_p) < d^2 / 4.
```

Then the pro-p completion `Δ̂_p` has infinite rank.

**If moreover `Δ <= Γ(p)`,** that claim makes the pro-p congruence kernel of `Δ`
infinite. So `Γ` fails the congruence subgroup property, and the necessary
condition of the transvection mechanism in
`sp21-lattice-few-alternating-and-large-rank-quotients` holds.

This is the only certificate recorded for the infinite-rank side. It is
checkable from the mod-p homology of one finite cover. What a certificate needs
(sublinear mod-p homology growth along p-towers, forced by (T)) is recorded in
`sp21-lattice-pro-p-completions-have-finite-rank`. The route
`sp21-golod-shafarevich-test-proof` gives the proof.
