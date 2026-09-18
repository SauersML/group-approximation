---
rg: 2
id: twisted-brin-thompson-labels-are-rigid
kind: claim
title: In a twisted Brin–Thompson group SV_G whose actor has no finitary elements, branch labels form a well-defined cocycle, and conjugacy classes of G do not fuse in SV_G
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that decides when SV_G is finitely presented and simple; this is a structural invariant of its elements (the branch label at a point) and a consequence for conjugacy.
  odometer-2v-orbit-action-is-type-a: that builds the finitely presented simple group SV over 2V_tau; this constrains which elements of it can play the roles of Higman's generators.
  equicontinuous-bs-bases-force-conjugator-entropy: that bounds conjugator entropy on a compact space; combined with this node it forbids two consecutive Higman generators from both being pure labels in SV over 2V_tau when the base is an odometer.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority
claimed — the label cocycle is implicit in Belk–Zaremsky's calculus).

## Setting

`G` acts faithfully on an infinite set `S`, and **no nontrivial element of `G` moves only
finitely many points of `S`** (`G ∩ FSym(S) = 1`). `SV_G` acts on `X = ℭ^S`. Its elements
are the homeomorphisms given, on the bricks `B(φ_i)` of a finite partition, by branches
`h_(ψ_i) τ_(γ_i) h_(φ_i)^-1` with `γ_i ∈ G`, where `τ_γ(κ)(s) = κ(γ^-1 s)`. This is the
Belk–Zaremsky definition as quoted in `twisted-brin-thompson-fa-from-simplicity-by-tree-geometry-proof`.
A **constant configuration** is `κ_c(s) = c` for all `s`, with `c ∈ ℭ`. Every `τ_γ` fixes
every `κ_c`.

## Statement

1. **Labels.** For `h ∈ SV_G` and `z ∈ X`, the label `γ_i` of any branch of `h` whose
   domain brick contains `z` does not depend on the chosen description. Call it `ℓ_h(z)`.
   Then `ℓ_h : X → G` is locally constant, `ℓ_(τ_g) ≡ g`, and
   `ℓ_(h h')(z) = ℓ_h(h' z) ℓ_(h')(z)`.
2. **No fusion.** If `π, ρ ∈ G`, `w ∈ SV_G` and `w τ_π w^-1 = τ_ρ`, then
   `ρ = ℓ_w(κ) π ℓ_w(κ)^-1` for every constant configuration `κ`. So two elements of `G`
   conjugate in `SV_G` are conjugate in `G`.
3. **Retraction at constants.** For each constant configuration `κ`,
   `ℓ(κ) : Stab_(SV_G)(κ) → G` is a homomorphism, and it restricts to the identity on
   `G ≤ Stab_(SV_G)(κ)`.

## Proof

**Item 1.** Suppose two branches `h_ψ τ_γ h_φ^-1` and `h_(ψ') τ_(γ') h_(φ')^-1` agree on a
brick `B(χ)` containing `z`.
- Let `F` be the finite set
  `supp φ ∪ supp φ' ∪ supp χ ∪ γ^-1(supp ψ) ∪ γ'^-1(supp ψ')`.
- For `t` with `γ^-1 t ∉ F` and `γ'^-1 t ∉ F`, the two outputs at coordinate `t` are
  `κ(γ^-1 t)` and `κ(γ'^-1 t)`.
- If `γ^-1 t ≠ γ'^-1 t` for such a `t`, choose `κ ∈ B(χ)` with different values at these
  two free coordinates. The outputs then differ, which is a contradiction.
- So `γ^-1 t = γ'^-1 t` for all but finitely many `t`, that is, `γ'^-1 γ` moves only
  finitely many points. By hypothesis `γ = γ'`.

Locally constant: the label is constant on each domain brick. The cocycle: on a small
enough brick the composite of two branches is a branch. Its label is `γγ'`, because
conjugating a prefix change by `τ_γ` gives a prefix change on the permuted coordinates.
`ℓ_(τ_g) ≡ g` by definition.

**Item 2.** Apply item 1 at `κ` to both sides of `w τ_π = τ_ρ w`. We get
`ℓ_w(π κ) π = ρ ℓ_w(κ)`, and `π κ = κ`. Note that `w` need not fix `κ`.

**Item 3.** This is the cocycle identity at a common fixed point.

## Consequences in `SV` over `2V_tau`

Take `G = 2V_tau` acting on the orbit `S` of `odometer-2v-orbit-action-is-type-a`. `S` is
dense in `C × C`. A nontrivial element moves a nonempty open set, which meets `S` in
infinitely many points, so `G ∩ FSym(S) = 1`.
- **The baker map stays rigid.** The inverse baker `u` is not conjugate to `u^2` in
  `SV_(2V_tau)`. By item 2 they would be conjugate in `2V_tau`, hence in `Homeo(C × C)`,
  but `h(u) = log 2` is finite and positive and `h(u^2) = 2 log 2`. The same holds for every
  element of `2V_tau` of finite positive entropy on `C × C`.
- **Pure labels in Higman's cycle.** Let `γ_j` be the image of `g_j` under a homomorphism
  `H4 → SV_(2V_tau)`, and suppose `γ_(i+1) = τ_g` is a pure label. Then item 2, at a constant configuration, makes `g` conjugate to
  `g^2` in `2V_tau`, with conjugator `ℓ_(γ_i)(κ)`.
  - If moreover `g` is an equicontinuous map whose closure has a free `Z/2` quotient (as
    for `s = tau × id` and its conjugates), then `ℓ_(γ_i)(κ)` has entropy at least `log 2`
    on `C × C` (`equicontinuous-bs-bases-force-conjugator-entropy`).
  - So it is not conjugate to its square in `2V_tau`, and by item 2 `γ_i` is not a pure
    label either.

  Two consecutive generators can therefore never both be pure labels when the base is of
  odometer type.
- **Where a copy of `H4` must live.** Every generator is a base of the cycle. So any pure
  label among them must already be conjugate to its square inside `2V_tau`. All the new
  room of `SV_(2V_tau)` is in non-pure elements, whose labels vary between the bricks
  meeting a constant configuration and the bricks elsewhere. No such four-cycle is
  constructed here, and `higman-group-satisfies-boone-higman` stays OPEN.
