---
rg: 2
id: thompson-v-is-not-mf
kind: claim
title: Thompson's group V is not MF
distinct_from:
  thompson-v-not-hyperlinear: that excludes approximate unitary models in the normalized Hilbert--Schmidt length; this excludes them in operator norm, which neither implies nor is implied by it for a general group.
  thompson-v-not-lef: that is the classical exclusion of exact local embeddings into finite groups; this excludes operator-norm asymptotic unitary representations, which LEF-failure does not control.
  leavitt-mf-quotients-see-thompson-vd-through-parity: that shows every MF quotient of the Leavitt unit group sees V at most through parity, which is a statement about the ambient's approximations; this is about V's own approximations, which need not extend to the ambient.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that excludes exact finite-dimensional unitary representations; this excludes approximate ones in operator norm.
  kazhdan-free-leavitt-collapse-typing-dichotomy: that shows any image-typed Kazhdan-free collapse produces a non-MF Kazhdan-blind group; this names the most economical such group, V itself.
---

**OPEN.** Thompson's group `V = G_(2,1)` does not embed in the operator-norm
ultraproduct of unitary groups `prod_omega U(n) / {(u_n) : ||u_n - 1||_op -> 0}`.

Because `V` is simple, the following are equivalent:
- `V` is not MF;
- `Rad_MF(V) != 1`;
- `Rad_MF(V) = V`.

**Kazhdan blindness.** `V` has the Haagerup property
(`thompson-v-has-haagerup-property`). So every Kazhdan subgroup of `V` is
finite, and every homomorphism from a Kazhdan group to `V` has finite image.
`V` is finitely presented (`thompson-v-finitely-presented-infinite-simple`),
so by compactness a proof of this claim can be taken to be a statement about
`V`'s own finite presentation. Every certificate group for this claim
surjects onto `V`, and so is not Kazhdan. This is the opposite of the
situation in `kazhdan-free-leavitt-collapse-typing-dichotomy` (b).

The Kazhdan compression engine is vacuous here:
`thompson-v-has-no-rigid-compression-defect` shows that every rigid pair
inside `V` is finite with trivial defect, in every ambient group.

**Consequences.**
- `property-t-free-leavitt-via-thompson-v-not-mf`: this claim closes the
  Kazhdan-free Leavitt goal, in the image-typed sense.
- It would give the first recorded non-MF group with the Haagerup property.
- It is implied by the non-MF-ness of any subgroup of `V`, for example
  Thompson's `F` or `T`. For `F` that is stronger than non-amenability of `F`,
  since amenable groups are MF.

## Attempts

None yet.
