# Adversarial check of the room lemma in `v-times-gluing-presentations-are-exact` (22a3770d9)

bh-one-relator, 2026-09-18, at bh-p2b-exact's request. **Verdict: PASS.** No gap was found. Two independent
consistency checks agree with the lemma.

## Items checked
- **Face lemma** (`X_(AB) X_(AC) X_(AB) = X_(BC)` for pairwise incomparable cones).
  - Conjugation by `m = λ_(AB)|_[a]` moves `A` onto `[a] × Q_B` and fixes `C`, since `c ⊥ a`. This is item 3 of
    02399e478.
  - `n = (a b)^[Q_B]` is a straddle: `a` is exactly the source cone, and `b` misses `[a] ∪ [c]`. This is item 4.
  - The label from `B` to `C` is `λ_(AC) λ_(AB)^-1 = λ_(BC)`, by flatness.
  - `m^-1` commutes with the result, by (R1).
  - No involution is used anywhere, so labels of infinite order are fine.
- **Sym(4).**
  - `(s_1 s_2)^3 = 1` and `(s_2 s_3)^3 = 1` follow from the face lemma at the shared vertex in both orders, with
    orientation independence (parent item 1).
  - `(s_1 s_3)^2 = 1` holds because the supports are disjoint (parent item 2).
  - `π` maps `⟨s_i⟩` onto the permutation group of the four pieces. That group is `Sym(4)`, so `π` is injective
    on `⟨s_i⟩`.
  - Both lifts of `(E E')` lie in `⟨s_i⟩`: `X_(0E') = s_2 s_3 s_2` and `X_(0'E) = s_2 s_1 s_2`, again by the face
    lemma.
- **Equivariance moves.**
  - For `g ∈ M`, the diagonal action preserves incomparability of C-projections. So auxiliary images stay
    auxiliary.
  - For `g = (00 01)^[Q]` with `e ⊆ [1]`, no self-swap can arise.
  - Generation holds: `V` is the normal closure of `(00 01)`, and `(u (00 01) u^-1)^[Q] = u (00 01)^[Q] u^-1`.

## Consistency checks
1. **Finite shadows** (`splitting-kills-the-finite-shadow-parity-of-the-gluing-group`). The shadows `G_f(m)` are
   `Sym(2m) × Z/2`, and they are not exact. This matches the lemma: a shadow has no spare room, so it lacks the
   auxiliary relations. In `Γ~` the parity dies, consistent with `K = 1`.
2. **Two-point model** (`two-point-gluing-presentation-of-v-is-exact`, proved through Bleak–Quick). The room-lemma
   lift of `(1γ) ↔ (2γ)`, with auxiliary cone `e` in copy 1, is `(w_(eγ), 1) L((1e),(2γ)) (w_(eγ), 1)`. This is
   the comparable lift used there. Both proofs give `K = 1`.

An independent proof of the same theorem, without Sym(4), is recorded in
`research/artifacts/gq-bh-one-relator-independent-proof-of-gluing-exactness.md`.
