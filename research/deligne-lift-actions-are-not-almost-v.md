---
rg: 2
id: deligne-lift-actions-are-not-almost-v
kind: claim
title: The Lagrangian actions of Sp_2n(Z) and of Deligne's lattice are never almost-V, so Belk-Hyde-Matucci finiteness over V cannot certify a host containing them
distinct_from:
  almost-v-fw-subgroups-act-through-finitely-many-germs: that is the general germ reduction for FW subgroups of almost-V groups; this applies it to the specific Lagrangian actions and concludes that no identification makes them almost-V.
  deligne-lattice-in-almost-v-sits-in-one-germ-group: that constrains how Deligne's lattice can sit in an almost-V host (in one germ group, fixing a point); this shows the lift actions of deligne-extension-dies-on-lagrangian-cantor-covers are never of that kind.
  lagrangian-thompson-group-is-finitely-presented: that is the open finiteness question for the Lagrangian host; this rules out one standard way of proving it.
---

**ESTABLISHED** (lane proof, short, from landed nodes plus Borel density; not
reviewed).

## Statement

Let `Δ` be an infinite group with property FW, for example property (T). Suppose
`Δ` acts faithfully on a Cantor set `X` and **no finite-index subgroup of `Δ` fixes
a point of `X`**. Then for every homeomorphism `θ : X → C = {0,1}^N`, the group
`θΔθ^{-1}` is not contained in
`H = {g ∈ Homeo(C) : g is V-local outside a finite set}`.

In particular, no finite germ extension of `V` on `X` contains `Δ` in that action.
This covers every such extension in the sense of Belk–Hyde–Matucci, including `VA`
and all shell envelopes.

It applies to:
1. `PSp_{2n}(Z)` (`n ≥ 2`) acting on any Cantor space `Y` with an equivariant map
   `Y → Λ_n(R)`, such as the Maslov Cantorization `Y_Λ` of
   `lagrangian-thompson-group-contains-deligne-lattice`;
2. Deligne's lattice `Γ̃` acting on `Z_2 × Y` by any lift of the form in
   `deligne-extension-dies-on-lagrangian-cantor-covers` or
   `lagrangian-thompson-group-contains-deligne-lattice`.

## Proof

By item 2 of `almost-v-fw-subgroups-act-through-finitely-many-germs`, an infinite FW
subgroup of `H` has a finite-index subgroup fixing a nonempty finite set pointwise.
That contradicts the hypothesis. Both groups have property (T):
- `Sp_{2n}(Z)` for `n ≥ 2` (textbook);
- `Γ̃` by `deligne-universal-cover-lattice-is-non-rf-kazhdan`;
- and (T) passes to quotients such as `PSp_{2n}(Z)`.

Now check the fixed-point hypothesis.
1. **`PSp_{2n}(Z)` on `Y`.** Suppose a finite-index subgroup `Γ_0` fixes `y`. Then it
   fixes `f(y) ∈ Λ_n(R)`, so it lies in the stabilizer of a Lagrangian, which is a
   proper algebraic (parabolic) subgroup of `Sp_{2n}`. But `Γ_0` is Zariski dense by
   Borel density (textbook), a contradiction.
2. **`Γ̃` on `Z_2 × Y`.** A finite-index subgroup of `Γ̃` contains some `z^m` with
   `m ≥ 1`, where `z` generates `ker(Γ̃ → Sp_{2n}(Z))`. In these lifts `z^m` acts on
   the `Z_2` coordinate by a nonzero translation, so it has no fixed point. ∎

## Consequences

- Belk–Hyde–Matucci Theorem 2.1 with base `V` cannot prove finite presentation of
  `V_Λ`, `V_Λ^τ`, or any group of homeomorphisms of the same space containing these
  actions.
- The same applies to hosts with finite singular sets over any base in which (T)
  subgroups are finite. This is a hand remark: the germ reduction uses only that the
  base group has the Haagerup property.
- Groups of local similarities with a finite similarity structure (Hughes;
  Farley–Hughes) are Haagerup (Hughes 2009; textbook, not read at source). So they
  contain no copy of `Sp_{2n}(Z)` at all, in any action.
- So a finite presentation of a Lagrangian host needs a finiteness theorem for
  Cantor groups whose Kazhdan subgroups act without virtual fixed points. No such
  theorem is on main.

## Scope

This concerns these specific actions. It does not exclude `Γ̃` from finite germ
extensions of `V` through other actions: shell envelopes contain `Γ̃` with a
virtual fixed point and a faithful germ group
(`deligne-lattice-in-almost-v-sits-in-one-germ-group`).
