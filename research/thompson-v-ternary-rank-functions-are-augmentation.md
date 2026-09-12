---
rg: 2
id: thompson-v-ternary-rank-functions-are-augmentation
kind: claim
title: Every Sylvester rank function on the ternary group algebra of Thompson's V is the augmentation rank
refuted_by:
  - thompson-v-carries-ternary-nonaugmentation-rank-function
  - thompson-v-is-sofic
distinct_from:
  thompson-v-has-no-nontrivial-f2-rank-model: that is triviality of matricial characteristic-two rank models of V; this is the abstract Sylvester statement over F_3, which is the form the ternary counterexample chain consumes.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is the gate for the whole ternary unit group, which this implies through the signed Thompson group; the converse is not known, since a rank function on F_3[V] need not extend to the unit group.
artifacts:
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

**OPEN.** Every Sylvester matrix rank function on `F_3[V]` has `rk(1 - [g]) = 0` for all `g in V`, so it is
the augmentation rank.

**Why it matters.**
- **The signed group.** By `signed-thompson-z-moving-rank-functions-match-v-rank-functions`, this is exactly
  the statement that every Sylvester rank function on `F_3[E ⋊ V]` kills `1 - [z]`.
- **The unit group.** It implies `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` (route
  `ternary-units-kill-minus-one-via-thompson-v-augmentation`). With the state upgrade, that gives the ternary
  counterexample chain.
- **Soficity.** It makes `V` not sofic and not `F_3`-linear sofic, because a sofic approximation gives a
  detecting rank function. So it is at least as hard as the soficity problem for `V`.

## Attempts

- **Subgroup reduction** (w5-c3-signed-thompson, artifact Sections 1–4). The `E ⋊ V` route to the
  characteristic-three gate lands here: `E ⋊ V` embeds in `V` as the centralizer of the first-letter swap
  `σ_0`, which is the image of `z`, and restriction to the unsigned `V` goes back. Where it stops: no proof;
  any proof settles soficity of `V` negatively.
- **Verified laws are consequences, not obstructions.** The Haar law on the signed diagonal, the lifted-trace
  law on finite subgroups, uniform displacement and the trivial-plus-regular torsion law are theorems about
  every model. A contradiction drawn from them on `E ⋊ V` would be a proof of this claim. None is known.
- **Tools that may transfer from characteristic two** (my reading, not re-derived; for `w4-upg-audit`). The
  covariance obstruction (`thompson-v-cantor-system-has-no-covariant-rank-model`), uniform displacement and
  the torsion law appear to use only additivity on orthogonal idempotents, subadditivity and conjugation
  invariance, so they likely hold for abstract rank functions over `F_3`. The symmetric-group stage theorem is
  matricial.
- **What a proof needs.** Relations among infinite-order, depth-changing elements, or among two finite
  subgroups generating an infinite subgroup (`v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`,
  artifact Proposition 2.1: finite data never force triviality).

- **Audit for abstract rank functions** (w5-v-infinite-order, artifact
  `research/artifacts/thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`, Section 3.1).
  - **Holds abstractly:** the torsion law and uniform displacement. They use only unit invariance, subadditivity,
    additivity on orthogonal idempotents, Fourier inversion and group theory, so they hold for every Sylvester rank
    function on `F_3[V]` (the torsion law with `p = 5`).
  - **Holds but vacuous here:** the covariance theorem holds abstractly, but needs covariant cylinder idempotents
    in the target, so it says nothing on `F_3[V]` alone.
  - **[matricial]:** the covariance finite form, its truncation bound, and the symmetric-group stage theorem.
- **Reformulation** (`v-rank-torsion-constant-equals-global-fixed-rank`).
  - **Equivalence:** this claim is equivalent to `a_5(rk) = phi_V(rk) = 1` for every rank function on `F_3[V]`.
  - **What any other rank function looks like:** `phi_V < 1`, regular odd torsion on the part that is not fixed,
    and free wandering elements (`v-rank-models-act-freely-by-wandering-elements`).
  - **Matricial only:** the compression to a reduced model has no abstract version yet.
  - **Where it dies:** amenable configurations are inert (artifact Section 3.2).
