---
rg: 2
id: leavitt-visible-states-are-factorwise-and-colimit-stable
kind: claim
title: States that could obstruct Leavitt-visible corners live on the visible factor, descend along field extensions, and are decided by one colimit ring per characteristic and arity
distinct_from:
  leavitt-unit-group-algebras-split-over-scalar-characters: that splits the group algebra over the scalar characters; this computes the states of the product and of the field colimit of the visible factors.
  twisted-leavitt-corner-fullness-equals-absence-of-k0-states: that is the equivalence between corner fullness and absence of states on one twisted factor; this assembles the visible factors over all finite fields of one characteristic.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

**ESTABLISHED.** Let `A_q = F_q[L_(F_q)(1,d)^x] = prod_chi A_chi` over the scalar characters, with
Leavitt-visible factor `A_iota(q)`.

1. **Factorwise.**
   - The states of `(K_0(A_q), [1])` are the convex combinations `sum_chi t_chi s_chi` of states
     `s_chi` of `(K_0(A_chi), [eps_chi])`, over the factors with `t_chi > 0`.
   - The augmentation gives a state carried by the trivial character, so `(K_0(A_q), [1])` always has a
     state.
   - An obstruction to a Leavitt-visible corner must therefore be a state on
     `(K_0(A_iota(q)), [eps_iota])` itself.
   - For `q = 2` the only factor is augmented, so `[1] <= 0` never holds there.
2. **Ascent.** `x -> x eps_iota(q^r)` is a unital ring homomorphism `A_iota(q) -> A_iota(q^r)` that
   carries `e_H` to `e_H`. Nonpositivity of the unit class ascends, and states descend.
3. **Colimit.** Fix `p` and `d`, and let `A_iota(infinity)` be the colimit of `A_iota(p^(k!))` along
   these maps. The following are equivalent:
   - `(K_0(A_iota(infinity)), [1])` admits no state;
   - the unit class is nonpositive in `K_0(A_iota(q))` for some finite field `F_q` of characteristic
     `p`;
   - for some finite field `F_q` of characteristic `p` and some admissible `m` prime to `p`, the cyclic
     corner of `leavitt-visible-cyclic-corner-is-full-on-some-host` is full.

So the colimit does not change the state question: the colimit factor has a state iff every finite
stage has one. A single state on it kills every linear cyclic corner in characteristic `p` and arity
`d`.

Proof: Section 8 of the census artifact (Theorem F).
