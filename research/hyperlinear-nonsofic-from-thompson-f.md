---
rg: 2
id: hyperlinear-nonsofic-from-thompson-f
kind: route
title: A hyperlinear nonsofic Thompson F answers Pestov Question 3.4, and the separation is a statement about two matrices
target: hyperlinear-nonsofic-group
requires: [thompson-f-is-hyperlinear, thompson-f-is-not-sofic]
---

If Thompson's `F` is hyperlinear and not sofic, it is a hyperlinear nonsofic group.

**Finitary form.** Write `R = {[ab^-1, a^-1ba], [ab^-1, a^-2ba^2]}` for the relators of `F`. By
`thompson-f-hyperlinear-iff-relator-system-hs-unstable` and `thompson-f-sofic-iff-relator-system-unstable`,
this route fires exactly when both of the following hold:
- **Unitary side.** Some unitary pairs `(U_n, W_n)` satisfy `R` up to `o(1)` in normalized
  Hilbert--Schmidt norm while `||U_n W_n - W_n U_n||_2` stays bounded below.
- **Permutation side.** Every permutation pair satisfying `R` up to `o(1)` in normalized Hamming
  distance almost commutes, uniformly in the size.

So Question 3.4 for `F` is the question whether the normalized-HS and Hamming stability of one
two-relator system can differ.

**Why this candidate is different.**
- **Torsion-free and a-T-menable.** `F` has the Haagerup property, as a subgroup of `V`, so no Kazhdan
  compression mechanism reaches it (`a-t-menable-groups-have-no-rigid-compression-defect`). Its
  nonsoficity would be a second mechanism, as for `hyperlinear-nonsofic-from-thompson-v`.
- **Easier than V on both sides.** Hyperlinearity of `V` gives the first premise, and nonsoficity of `F`
  gives nonsoficity of `V`. So this route is implied by neither `V` premise alone, and it is at least as
  accessible as the `V` route on the nonsofic side.
