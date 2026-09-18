---
rg: 2
id: upper-triangular-cloning-groups-contain-lamp-wreath-z2
kind: claim
title: "For every nonzero ring R, the Witzel–Zaremsky group T(B_*(R)) contains the wreath product (R,+) ≀ Z^2"
distinct_from:
  cloning-system-groups-on-finite-groups-embed-in-v: that is the universal embedding claim for all finite-group cloning systems; this is a subgroup computation for one non-local family, with no embedding input
  bit-register-cloning-group-has-doubly-exponential-period-growth: that is a period-growth obstruction for Sym({0,1}^n); T(B_*(F_q)) has torsion only inside B_∞(F_q), whose element orders are linear in matrix size, so period growth gives nothing here and the obstruction is a lamplighter over Z^2 instead
  wreath-z-by-z2-does-not-embed-in-thompson-v: that is Corwin's non-embedding theorem for Z ≀ Z^2; this node supplies copies of (R,+) ≀ Z^2 inside cloning groups
artifacts:
  - experiments/zaremsky-2-16-upper-triangular-2026-09-17/lamplighter_in_upper_triangular_cloning.py
  - experiments/zaremsky-2-16-upper-triangular-2026-09-17/output.txt
---

**ESTABLISHED (unreviewed).** Route `upper-triangular-cloning-lamp-wreath-proof`.

**Claim.** Let `R` be a ring with `1 ≠ 0`, and `T = T(B_*(R))` the Thompson-like group of the
Witzel–Zaremsky upper-triangular cloning system (arXiv:1405.5491, §7, Lemma 7.1). Then `T`
contains a subgroup isomorphic to the restricted wreath product `(R,+) ≀ Z^2`.

In particular:
- `F_p ≀ Z^2 ≤ T(B_*(F_q))` and `F_q ≀ Z^2 ≤ T(B_*(F_q))` for every prime power `q = p^e`;
- `Z ≀ Z^2 ≤ T(B_*(R))` whenever `Z → R` is injective (characteristic 0), for example
  `R = Z`, `Z[1/p]`, or a ring of `S`-integers.

**Where the copy lives.**
- *Lamps.* Take trees with a root caret, and the unipotent block matrices `[[I, X], [0, I]]`
  split across the root. Expansion keeps this block shape. On rows it extends by zero onto the
  last sub-leaf, and on columns it duplicates. The limit abelian group is
  `R[D ∩ (0,1/2]] ⊗ LC([1/2,1), R)`, where `D` is the set of dyadic rationals and `LC` means
  locally constant functions with dyadic breakpoints.
- *Top group.* `F_L × F_R ≤ F ≤ T` (elements whose trees both start with the root caret)
  normalizes this group and acts by moving points and pushing functions forward.
- *Choosing Z^2.* In the jump basis `{1} ∪ {1_[c,1)}` the right factor is a permutation module.
  Choose `g ∈ F_L` and `h ∈ F_R` with infinite orbits of `1/4` and `3/4`. Then the translates of
  one lamp `e_(1/4) ⊗ 1_[3/4,1)` are free.

**Consequences.**
- *Characteristic 0.* `T(B_*(R))` does not embed in `V`, by Corwin's theorem
  (`wreath-z-by-z2-does-not-embed-in-thompson-v`). See
  `char-zero-upper-triangular-cloning-groups-do-not-embed-in-v`.
- *Finite fields.*
  - If `T(B_*(F_q))` embeds in `V`, then `F_p ≀ Z^2 ≤ V`. That embedding is open, and it is the
    prerequisite of `finite-field-upper-triangular-cloning-not-in-v-via-lamplighter`.
  - If `T(B_*(F_q))` is locally coCF, then `F_p ≀ Z^2` is coCF. That contradicts the
    Holt–Rees–Röver–Thomas wreath-product conjecture: context only, not re-read at source.
- *For Problem 2.16.* `B_*(F_q)` is therefore not a candidate for a coCF group that does not embed
  in `V` unless `F_p ≀ Z^2` is coCF but not in `V`. So these systems add nothing beyond the
  lamplighter question itself.
