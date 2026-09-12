# Chapman--Peled arXiv:2509.21566v2 — statements read from the PDF (2026-09-11)

Source: M. Chapman and Y. Peled, *Cocycle stability in permutations of random
simplicial complexes*, arXiv:2509.21566v2 (4 Dec 2025). Read page by page from
the arXiv PDF on 2026-09-11. Page numbers are the paper's own.

## Exact hypothesis of the main theorem (p. 2)

> **Theorem 1.1.** Let `0 < η < 1/2`, `p = n^(-1+η)` and `Y ~ Y(n,p)`. Then,
> if a.a.s. `h_1(Y, Sym) = ω(n^(-3) p^(-1))`, then the fundamental group of such
> a complex is a.a.s. a non-sofic hyperbolic group.

So the assumption is that the cocycle Cheeger constant beats the inverse
triangle count `n^(-3)p^(-1) = n^(-2-η)`. The abstract's phrase "linear cocycle
stability rate" means only that the rate is linear, `h_1 > 0`. The theorem needs
no constant lower bound.

Remark 1.2 (p. 3): "The permutation analogue of Dogon's result, where a
stability rate which is worse than linear occurs with positive probability,
remains open."

Theorem 1.3 (p. 3): for `p = n^(-1/2+η)`, a.a.s. `h_1(Y,Sym) >= η/42`.
Theorem 1.4 (p. 3): for `p = n^(-1-η)`, `0<η<2`, a.a.s. `η/2 <= h_1 <= 9η/4+3`.
Remark 1.5: a bounded-below cocycle Cheeger constant is not a monotone property.

## Definitions (pp. 6--9)

* 1-cochains are antisymmetric edge labels in `Γ`; `δα(xyz)=α(xy)α(yz)α(zx)`.
* `d(α,β) = E_(x~μ_1) d(α(x),β(x))`; `||δα|| = E_(x~μ_2)||δα(x)||`; measures are
  descending from `μ_2` (Definition 2.2). In the random-complex setting `μ_2` is
  uniform on triangles.
* `h_1(X,Γ) = inf ||δα|| / d(α, Z^1(X,Γ))` (2.8). With permutation coefficients,
  `d_h(σ,τ) = 1 - |{i in [n] : σ(i)=τ(i)}|/N` for `σ in Sym(n)`, `τ in Sym(N)`,
  `N >= n` (2.10). Cocycles of every size are allowed, so the notion is *flexible*.
* Fact 2.4 (Theorem 1.3 of CL23a): a `ρ`-cocycle stable complex has a
  `|Y(1)|·ρ`-homomorphism stable fundamental group. Footnote 8: homomorphism
  stability "is usually referred to as pointwise flexible group stability in
  permutations".
* Proposition 2.8 (Glebsky--Rivera; also AP15): a `ρ`-homomorphism stable
  sofic presented group is residually finite, for any rate `ρ`.

Because the stability is flexible, Becker--Lubotzky's theorem (strict
stability of infinite sofic Kazhdan groups fails) does not apply. That is why the
proof below adds a triangle instead of invoking Becker--Lubotzky.

## Tools used in the proof (pp. 10--13)

* **Lemma 2.9.** `α in C^1(Y,Sym(n))`, `β in C^1(Y,Sym(N))`, `N >= n`; `A` = the
  covering of `G(Y)` from `α x β` with uniformly lifted `μ_1, μ_0`; `D` = the
  diagonal `{(y,i,i)}`; `f = 1_D`. Then `d_h(α,β) >= ||δf|| / (2 μ_0(D))`.
* **Fact 2.12** (Oppenheim trickling down): a pure connected λ-local spectral
  expander with `λ < 1/2` is a `λ/(1-λ)`-spectral expander.
* **Proposition 2.13:** a λ-spectral expander has `h_0(X,F_2) >= 1-λ`.
* **Corollary 2.14:** if `X` is a λ-local spectral expander, `λ<1/2`, every
  connected covering `Y` of `X` has `h_0(Y,F_2) >= (1-2λ)/(1-λ)`.

## Mid-range properties (p. 21)

Algorithm 1: sample `Y ~ Y(n,p)`, choose a uniformly random triangle
`Δ` not in `Y(2)`, add it to get `Z`.

> **Corollary 4.6.** Let `0 < η < 1/2` and `λ > 0`. If `p = n^(-1+η)`, then a.a.s.
> over sampled pairs `Y, Z` according to Algorithm 1,
> (1) the triangle `Δ in Z(2) \ Y(2)` is not trivial in `π_1(Y,*)`;
> (2) the fundamental groups `π_1(Y,*)` and `π_1(Z,*)` are hyperbolic;
> (3) the complexes `Y` and `Z` are λ-local spectral expanders.

Inputs: BHK11 Lemmas 3.10, 3.12 (Fact 4.2), BHK11 Theorem 1.5 (Fact 4.3), HKP21
Theorem 1.1 (Fact 4.5).

## The proof of Theorem 1.1 (pp. 22--23)

1. The a.a.s. lower bound transfers from `Y` to `Z` through the total variation
   distance between `Bin(C(n,3),p)` and its shift by one.
2. By Fact 2.4 both groups are homomorphism stable. Under the contrary assumption
   "every hyperbolic group is sofic", Proposition 2.8 makes them residually finite.
3. Residual finiteness plus Corollary 4.6(1) gives `α: π_1(Y,*) -> Sym(n)` with
   `d_h(α(Δ),Id)=1`, extended to a 1-cocycle of `Y` by `α=Id` on a spanning tree.
   As a cochain of `Z`, `||δα|| = 1/|Z(2)|`.
4. Let `β` be a 1-cocycle of `Z`. **Claim 4.7:** every component `C` of `A` has
   `μ_0(C ∩ D)/μ_0(C) <= 1/2`, via the injection
   `(y,i,i) -> (y, α(σΔσ̄)i, β(σΔσ̄)i) = (y,j,i)`, `j != i`, where `σ` is a tree
   path to the first vertex of `Δ`, `α(σΔσ̄)=α(Δ)` has no fixed point, and
   `β(σΔσ̄)=Id`.
5. Corollary 2.14 on each component gives `||δf|| >= μ_0(D)(1-2λ)/(1-λ)`, so
   `d_h(α,β) >= (1-2λ)/(2-2λ)`. Hence `h_1(Z,Sym) = O(n^(-3) p^(-1))`, contradicting step 1.

## What this repository extracts (2026-09-11, `hyperbolic-sofic` lane)

Steps 3--5 never use soficity. They use one finite quotient of `π_1(Y)` in which
the perimeter of `Δ` survives, plus λ-local spectral expansion of `Y`. So they give
an unconditional, deterministic cap on the Cheeger constant of `Z`, recorded as
`finite-quotient-caps-cocycle-cheeger-constant`. Two bookkeeping points the
paper glosses:

* **Measure change.** `d` on `Z` uses the descendant `μ_1^Z`. Off the three
  edges of `Δ`, `μ_1^Z = (|Y(2)|/|Z(2)|) μ_1^Y`; on them the degree grows by
  one. So `μ_1^Z >= (|Y(2)|/|Z(2)|) μ_1^Y` pointwise, and the cap becomes
  `h_1(Z,Sym) <= (2-2λ)/((1-2λ)|Y(2)|)`.
* **Small targets.** For a cocycle `β` on `N < n` points, padding by fixed
  points gives a cocycle on `n` points that agrees with `α` at least as often, so
  the lower bound on `d_h(α,β)` covers every size.
