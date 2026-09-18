---
rg: 2
id: brick-diagonal-power-conjugacy-forces-zero-drift
kind: claim
title: If a brick diagonal sends b to a proper power b^m, every b-invariant measure has zero exponent drift
requires:
  - bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
distinct_from:
  renormalizable-thompson-elements-are-odometer-codes: item 3(b) there proves zero drift for odometers of a code, using the tower; this needs only the weaker diagonal identity delta_e(b) = b^m, which is exactly what the compiler step consumes.
  brin-thompson-proper-power-conjugates-have-zero-entropy: that bounds entropy of elements conjugate to proper powers; this is the drift (exponent-cocycle) analogue for diagonal power-conjugacy by a brick code.
---

**ESTABLISHED** through `brick-diagonal-power-conjugacy-zero-drift-proof`. Elementary lane proof
(bh-invent-08), not reviewed.

**Setting.** Let `b ∈ kV` and `δ_b(x) ∈ Z^k` be its exponent cocycle (on a table brick,
`(|v_j| - |u_j|)_j`), as in `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`. For a
`b`-invariant Borel probability measure `ν`, the drift is `D_ν(b) = ∫ δ_b dν`.

**Theorem.** If some `m`-ary brick code `e` (`m >= 2`) satisfies `δ_e(b) = b^m`, then `D_ν(b) = 0`
for every `b`-invariant probability measure `ν`.

**Corollaries.**
- **A test for the compiler.** An element with nonzero drift for SOME invariant measure never admits
  a diagonal power-conjugacy. By `brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups` it can
  never be the base of a compiled `BS(1,m)`, in any number of extra coordinates. For `b × id` on a
  larger `C^{k+l}`, invariant measures project to `b`-invariant ones.
- **Pointwise version.** If some coordinate of `δ_b` has constant nonzero sign everywhere, then `b`
  admits no brick-diagonal power-conjugacy.
- It recovers item 3(b) of `renormalizable-thompson-elements-are-odometer-codes`, since odometers
  satisfy `δ_e(T) = T^m`.

**Lesson for general BH.** Drift is the conserved quantity of the renormalization compiler. Each
diagonal identity `δ_e(b) = b^m` forces zero drift, while the conjugator the compiler creates always
carries positive drift in its fresh coordinate. The compiler's outputs therefore cannot be fed back in
as bases (`compiled-bs-stable-letters-are-never-rediagonalized`). Any hierarchy of power-conjugacies
in `nV` needs a drift-free source of conjugation.
