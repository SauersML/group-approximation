---
rg: 2
id: self-similar-central-sign-cocycle
kind: claim
title: A nontrivial self-similar central cocycle reproduces the marked Clifford sign on both subtrees
distinct_from:
  untwisted-sign-replication-flips-minus: that proves the untwisted recursion impossible; this asks for the required projective replacement and its exact coherence equations.
  central-extension-twisted-sector-criterion: that analyzes one fixed central extension by cutting its negative sector; this requires the extension class to be compatible with binary wreath recursion at every depth.
  thompson-v-central-extensions-split: that excludes cocycles supported only on the bare prefix mixers; this asks for a class involving a nontrivial self-similar state kernel.
---

Construct a finitely generated self-similar group `G`, a central extension

```text
1 -> <J> -> Gtilde -> G -> 1,       J^2=1,
```

and a wreath recursion whose factor set `omega` satisfies the binary
self-similarity equation `omega ~= omega boxtimes omega` up to coboundary.
The recursion must have these concrete consequences.

1. A designated marked lift remains `-I` on the exact tracial model at every
   subtree depth; the cocycle supplies the phase forbidden by
   `untwisted-sign-replication-flips-minus`.
2. The two child copies contain a transported Pauli pair with the same central
   commutator `J`.
3. Sibling swaps intertwine the copies coherently, so the level-`n` CAR/Clifford
   algebra contains one genuinely new relative qubit.
4. All recursion and cocycle identities are consequences of a finite or
   recursively enumerable group presentation with polynomial derivation cost
   in the depth.

An identity `J=(J,J)` in an untwisted group is explicitly excluded.

## Attempts

- Search finite-state binary automata whose sections contain a Pauli pair,
  compute restriction on `H^2(G,C_2)`, and solve the fixed-class equation.
- The trivial class fails by `untwisted-sign-replication-flips-minus`. Reject
  any class which becomes a coboundary after one restriction, since its sign
  disappears below a finite level.
- Do not search `H^2(V,C_2)` for the missing multiplier.
  `thompson-v-central-extensions-split` proves that this group is zero and
  that the splitting is unique.  Prefix swaps may transport a kernel sign,
  but the cocycle itself must involve the state/Clifford kernel (or a relative
  extension containing it).
- **Central-product solution.**  `thompson-clifford-central-product-tape`
  identifies, rather than multiplies, the centers of the two child CAR
  kernels.  The route `self-similar-cocycle-from-thompson-clifford` verifies
  that this supplies the required fixed nontrivial class while leaving the
  Thompson prefix subgroup split.
