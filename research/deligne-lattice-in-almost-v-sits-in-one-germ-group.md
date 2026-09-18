---
rg: 2
id: deligne-lattice-in-almost-v-sits-in-one-germ-group
kind: claim
title: In any group of Cantor homeomorphisms with finite V-singular sets, a finite-index subgroup of the Deligne lattice embeds in one singular germ group, with its center singular
distinct_from:
  almost-v-fw-subgroups-act-through-finitely-many-germs: that gives one faithful germ group for Kazhdan lattices with trivial center; this handles the Deligne lattice, whose infinite center could have hidden in the V-local kernel, and shows it cannot.
  simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group: that is the same conclusion for simple Kazhdan inputs; the Deligne lattice is not simple and has infinite center.
  deligne-lattice-embeds-in-no-rover-nekrashevych-group: that excludes Rover--Nekrashevych hosts; this constrains every finite germ extension of V, including shell envelopes, without excluding them.
---

**ESTABLISHED** by `deligne-lattice-almost-v-germ-group-proof` (lane proof, not
independently reviewed; no novelty claimed).

Let `n >= 2`, let `p : G~ -> Sp_2n(R)` be the universal cover, let `Gamma~ = p^-1(Sp_2n(Z))`
(`deligne-universal-cover-lattice-is-non-rf-kazhdan`) and `Z = ker p ≅ Z`. Let `E <= H` be a
group containing `Gamma~` (notation of `kazhdan-subgroups-of-almost-v-have-no-central-v-elements`),
for instance a finite germ extension of `V`.

1. **The center is singular.** No nontrivial element of `Z` lies in `kVk^-1` for any
   `k in H`.
2. **One germ group.** There are a finite-index subgroup `Gamma_0 <= Gamma~` and a point
   `y` fixed by `Gamma_0` such that the germ map `Gamma_0 -> (E)_y` is injective. The point
   `y` lies in `sing(E)`, and the germ of every nontrivial element of `Z ∩ Gamma_0` at `y`
   has infinite order.
3. **Finite presentation.** If `E` is a finite germ extension of `V` certified finitely
   presented by Belk--Hyde--Matucci Theorem 2.1 at `n = 2`, then `(E)_y` is finitely
   presented.

**Reading for the test case.** Any almost-V host for `Gamma~` must carry a finite-index
subgroup of `Gamma~`, center included, faithfully in a single singular germ group. The
center cannot be absorbed into the V-local part, as a central element of `V` would be.
This is not an exclusion: shell envelopes of `Gamma~` satisfy all three items, and their
finite presentation stays open.
