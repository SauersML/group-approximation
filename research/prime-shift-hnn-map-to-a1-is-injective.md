---
rg: 2
id: prime-shift-hnn-map-to-a1-is-injective
kind: claim
title: The surjection from the prime-shift HNN group Π_1 onto the permutation group A_1 is injective
distinct_from:
  prime-shift-hnn-groups-are-not-finitely-presented: that proves Π_1 is not finitely presented and derives what injectivity would imply; this is the open question whether Π_1 -> A_1 is injective.
  gl-n-q-lies-in-prime-shift-permutation-group: that constructs A_1 and the surjection from Π_1; this asks whether the surjection is an isomorphism.
  prime-shift-affine-group-a1-is-finitely-presented: that asks whether A_1 is finitely presented; a positive answer here refutes it.
---

**OPEN.** Notation as in `gl-n-q-lies-in-prime-shift-permutation-group` and
`prime-shift-hnn-groups-are-not-finitely-presented`:
- `σ` is the prime-shift permutation of `Q`;
- `A_1 = <x -> x+1, x -> 2x, x -> -x, σ> <= Sym(Q)`;
- `Π_1 = Aff(Q) *_(Q^x) (Q^x ⋊_σ <s>)`, which maps onto `A_1` by `s -> σ`.

Is the surjection `Π_1 -> A_1` injective?

**Source.** Root `gl-n-q-embeds-in-fp-simple-group`, Attempt 18: "The open question is whether `Π_1 -> A_1`
is injective."

**What either answer gives.** Both follow from `prime-shift-hnn-groups-are-not-finitely-presented`.
- **Injective.** Then `A_1 ≅ Π_1`, which is not finitely presented. `A_1` then contains no nontrivial finitary
  permutation, and `A_1^ab = Z/2 × Z^2`. This refutes `prime-shift-affine-group-a1-is-finitely-presented`, and
  with it the route `aff-q-bh-via-prime-shift-type-a-action`.
- **Not injective.** A hidden relation holds in `A_1`. That is necessary, but not sufficient, for `A_1` to be
  finitely presented or to contain `Alt_fin(Q)`.

## Attempts

None recorded as a separate node; see root Attempt 18 (lane gq-deep-typeA-2).
