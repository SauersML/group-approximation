---
rg: 2
id: lifted-thompson-t-twist-cost-is-superlinear-proof
kind: route
title: "Rescale a linear-rate twist family to cocycles, take the ultralimit, and project onto invariant vectors to get a nonzero homomorphism of the perfect T-bar; lower semicontinuity handles the linear regime; conjugation by x ↦ 2x plus the eigenspace splitting of π(t_{1/2}) gives halving"
target: lifted-thompson-t-twist-cost-is-superlinear
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
  - lifted-thompson-t-relative-t-forces-dyadic-twist-gap
---

Notation as in the target. Imports:
- (P) `T̄` is perfect, so every homomorphism from `T̄` to an abelian group is `0`. This is item 2 of
  `lifted-thompson-t-perfect-centre-cubically-elliptic`.
- (A) Part (a) of `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`: `c(−θ) = c(θ)`,
  subadditivity, and lower semicontinuity of `c`.
- (U) Ultraproducts of unitary representations, as imported in
  `lifted-thompson-t-relative-t-forces-dyadic-twist-gap-proof`. For a nonprincipal ultrafilter `U`,
  bounded sequences modulo `U`-null ones form a Hilbert space `H_U`, and `π_U(g)[v_n] = [π_n(g)v_n]`
  is a unitary representation of the discrete group `T̄`.

## Item 1

Suppose `θ_n → 0`, `θ_n ≠ 0`, with `π_n`, `π_n(z) = e(θ_n)·I`, unit `ξ_n`, and
`δ_n = max_{s∈S} ‖π_n(s)ξ_n − ξ_n‖ ≤ K|θ_n|`. Take real representatives `θ_n ∈ (−1/2, 1/2]`.

**Step 1 (rescaled cocycles).** Put `b_n(g) = (π_n(g)ξ_n − ξ_n)/θ_n`. Each `b_n` is a 1-cocycle into
`π_n`: `b_n(gh) = b_n(g) + π_n(g)b_n(h)`. So `‖b_n(g)‖ ≤ |g|_S · max_s ‖b_n(s)‖ ≤ K|g|_S`, bounded
in `n` for each fixed `g`.

**Step 2 (ultralimit).** Put `ξ = [ξ_n]` and `b(g) = [b_n(g)]` in `H_U`. Then:
- `‖ξ‖ = 1`;
- `‖π_U(s)ξ − ξ‖ = lim_U δ_n ≤ lim_U K|θ_n| = 0`, so `ξ` is `π_U(T̄)`-invariant;
- `b` is a 1-cocycle into `π_U`, since the identity passes to the limit;
- `b(z) = [(e(θ_n) − 1)/θ_n · ξ_n] = 2πi · ξ`, since `(e(θ) − 1)/θ → 2πi` as `θ → 0`.

**Step 3 (invariant projection).** Let `P` be the orthogonal projection onto the
`π_U(T̄)`-invariant vectors. `P` commutes with `π_U`, and `π_U(g)` is the identity on its range. So
`Pb(gh) = Pb(g) + π_U(g)Pb(h) = Pb(g) + Pb(h)`, and `Pb` is a homomorphism of `T̄` into the
additive group of `P H_U`. By (P), `Pb = 0`. But `Pb(z) = 2πi · Pξ = 2πi · ξ ≠ 0`. This is a
contradiction.

**Equivalence with the ratio form.** If `c(θ_n) ≤ K'|θ_n|` along `θ_n → 0`, the definition of `c` as
an infimum gives `π_n, ξ_n` with defect `≤ (K' + 1)|θ_n|`. So item 1 in the sequence form gives
`c(θ)/‖θ‖ → ∞`. The converse is immediate. ∎

## Item 2

Let `K > σ`. Choose `θ_n → 0`, `θ_n ≠ 0`, with `c(θ_n) ≤ K‖θ_n‖`. By `c(−θ) = c(θ)` we may take
`θ_n ∈ (0, 1/2]`. Fix `x ∈ R/Z` and a representative `d ∈ [0, 1/2]` with `d = ‖x‖`, or
`d ∈ [−1/2, 0]` and argue symmetrically.
- Put `m_n = ⌊d/θ_n⌋ ≥ 0`. Then `0 ≤ d − m_nθ_n < θ_n → 0`, so `m_nθ_n → x` in `R/Z`.
- By subadditivity and `c(0) = 0`, `c(m_nθ_n) ≤ m_n c(θ_n) ≤ (d/θ_n) · Kθ_n = Kd`.
- By lower semicontinuity, `c(x) ≤ liminf_n c(m_nθ_n) ≤ K‖x‖`.

Letting `K ↓ σ` gives `c ≤ σ‖·‖`. ∎

## Item 3

**`Φ` is an endomorphism.** `T̄` is the group of homeomorphisms `g` of `R` with `g(x+1) = g(x)+1`
that are piecewise linear, with breakpoints in `Z[1/2]`, slopes in `2^Z`, and `g(Z[1/2]) = Z[1/2]`.
(These are exactly the lifts of elements of `T`.)
- For such `g`, `Φ(g)(x) = g(2x)/2` is a homeomorphism.
- `Φ(g)(x + 1/2) = g(2x + 1)/2 = Φ(g)(x) + 1/2`. So `Φ(g)` commutes with `t_{1/2}`, and hence
  with `z = t_{1/2}^2`.
- Its breakpoints are `b/2` for the breakpoints `b` of `g`, so they are dyadic. Its slopes are
  those of `g`, and it preserves `Z[1/2]`.

So `Φ(g) ∈ C_{T̄}(t_{1/2})`. `Φ` is a homomorphism, since it is conjugation in `Homeo(R)`, and it
is injective. `Φ(z)(x) = (2x + 1)/2 = t_{1/2}(x)`.

**Halving.** Fix `θ` with a real representative, and let `π` have `π(z) = e(θ)·I` and a unit `ξ`
with `max_s ‖π(s)ξ − ξ‖ ≤ δ`.
- Put `ρ = π ∘ Φ` and `W = π(t_{1/2})`. Then `W` commutes with `ρ(T̄)` and `W^2 = e(θ)·I`.
- So `H = E_+ ⊕ E_−`, where `E_±` is the eigenspace `W = ±e(θ/2)`. Both are `ρ`-invariant, and
  `ρ(z) = W` acts on them by `e(θ/2)` and `e((θ+1)/2)`.
- `‖ρ(s)ξ − ξ‖ = ‖π(Φ(s))ξ − ξ‖ ≤ Mδ`, since `Φ(s)` is an `S`-word of length at most `M`.
- The projections onto `E_±` commute with `ρ`, so each component `ξ_±` has
  `‖ρ(s)ξ_± − ξ_±‖ ≤ Mδ`. One of them has `‖ξ_±‖^2 ≥ 1/2`, and normalising it gives defect at most
  `√2Mδ` in the class of `c(θ/2)` or of `c((θ+1)/2)`.

Taking the infimum over `(π, ξ)` gives `min(c(θ/2), c((θ+1)/2)) ≤ √2 M c(θ)`. The branch can depend
on `(π, ξ)`. Since there are only two branches, a minimising sequence has a subsequence with a
constant branch, so the inequality holds. ∎
