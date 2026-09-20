---
rg: 2
id: f-exotic-co-amenable-route-amenability-plus-not-bs-proof
kind: route
title: "Proof: an amenable co-amenable member gives A; conversely A makes every subgroup amenable and co-amenable"
target: f-exotic-co-amenable-route-is-amenability-plus-not-brin-sapir
requires:
  - thompson-f-interval-stabilizer-cosets-separate-only-if-amenable
---

Notation as in the target claim. There are two standard facts, each proved in one line here.

- **(a) Subgroups of amenable groups are amenable.** Let `m` be a left-invariant mean on `ℓ^∞(F)` and
  `K ≤ F`. Choose a set `T` of representatives of the right cosets `Kt`, and write `g = κ(g)·τ(g)` with
  `κ(g) ∈ K` and `τ(g) ∈ T`. For `f ∈ ℓ^∞(K)`, put `m_K(f) = m(f ∘ κ)`. For `k ∈ K`, `κ(kg) = kκ(g)`, so
  `m_K` is left `K`-invariant.
- **(b) Every subgroup of an amenable group is co-amenable.** Let `π : F → F/K` be the quotient map, and put
  `m'(φ) = m(φ ∘ π)` for `φ ∈ ℓ^∞(F/K)`. Since `π(hg) = h·π(g)`, `m'` is `F`-invariant.

**Item 1, `⇒`.** Assume `C(S) ∧ M(S)`. Choose `K ∈ S` with an invariant mean on `F/K`. Then `S ≠ ∅`, which
is `E(S)`. By `M(S)`, `K` is amenable, and item 3 of
`thompson-f-interval-stabilizer-cosets-separate-only-if-amenable` reads verbatim: "If `H ≤ F` is
amenable and `F/H` carries an invariant mean, then `F` is amenable." So `A` holds.

**Item 1, `⇐`.** Assume `A` and choose `K ∈ S`. By (b), `F/K` carries an invariant mean, so `C(S)`
holds. By (a), every member of `S` is amenable, so `M(S)` holds.

**Item 2.** First, `P2 ⇒ M(X)`: a member of `X` has no subgroup isomorphic to `F`. Conversely, assume
`M(X)`, and let `K ≤ F` have no subgroup isomorphic to `F`. Either `K` is elementary amenable, and hence
amenable, or `K ∈ X`, and then `K` is amenable by `M(X)`. So `P2` holds.

**Item 3.** By definition `P1 = C(X)`. By item 2, `P2 ⟺ M(X)`. By item 1 with `S = X`,
`P1 ∧ P2 ⟺ A ∧ E(X)`, and `E(X)` is `¬BS` by definition.

**Item 4.** Assume `A`. By (a), every subgroup of `F` is amenable, so `P2` holds. Item 3 then gives
`P1 ⟺ P1 ∧ P2 ⟺ A ∧ ¬BS ⟺ ¬BS`.

**Item 5.** If `BS` holds, then `X = ∅`. `C(∅)` is false, since it asserts the existence of a member.

**Item 6.** If `E(S)` is known, item 1 reads `C(S) ∧ M(S) ⟺ A`. If `E(S)` is not known, item 1 exhibits
the conjunction as `A ∧ E(S)`. If moreover `A ⇒ E(S)` is not known, then `A` does not yet imply the
route's conjunction, so the route is not known to be necessary for the target. Its prerequisite `C(S)`
can fail in a world where `A` holds, exactly when `E(S)` fails there. The examples: `{e}` is F-free, and
`F` belongs to the family of all subgroups, so in both cases `E(S)` is known.

**Combined statement.** Take any co-amenable-induction split with one kernel `K`, as in item 4 of
`f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic`. Unless `K` is Brin–Sapir exotic, it has
a conjunct equivalent to `A`, and a proof that `K` is exotic is a proof of `¬BS`. A family-quantified
split with `S ⊆ X` proves `E(S)`, and so `¬BS`, by item 1. For a family `S ⊄ X`, apply item 1 to
`S ∩ X` and to `S \ X` separately:
- A witness `K ∈ S \ X` for `C(S)` is not exotic, so `C(S) ∧ M(S)` reduces to a single-kernel datum at
  `K`. That datum collapses by items 2–3 of the sandwich claim: if `K` contains `F`, then `M(S)` gives
  `Amen(K)`, which is `⟺ A`; if `K` is elementary amenable, then `Coam(K) ⟺ A`.
- A witness in `S ∩ X` proves `¬BS`.

The collapse in the first bullet is a statement about the witness actually used. It does not claim that
`C(S)` alone is equivalent to `A`. ∎
