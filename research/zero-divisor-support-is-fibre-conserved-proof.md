---
rg: 2
id: zero-divisor-support-is-fibre-conserved-proof
kind: route
title: Proof that minimal zero-divisor support is conserved on fibres and concentrates in the rational derived core, and that the finite-index step of amenable cd-2 descent preserves counterexamples, multiplies chi and raises only support
target: zero-divisor-support-is-fibre-conserved
requires:
  - amenable-finite-cd-domain-groups-are-virtually-solvable
  - amenable-cd-two-kropholler-iff-locally-indicable
  - rf-weak-bass-defect-is-degree-two-approximation-defect
---

Notation is that of the claim. `|x|` means `|supp x|`. A nonzero `x` with `|x| = 1` is a unit, so
every zero-divisor pair has `|a|, |b| >= 2`, and `μ >= 4`.

**Translation.** If `ab = 0`, then `(u a v)(v^{-1} b w) = 0` for all group elements `u, v, w`,
with the same support sizes. Given `α ∈ supp a` and `β ∈ supp b`, take `u = α^{-1}`, `v = 1` and
`w = β^{-1}`. This gives a normalized pair. **Monotonicity.** If `H ≤ G`, then
`Q[H] ⊂ Q[G]`, so `μ(H) >= μ(G)`.

## Item 1

Fix `t ∈ H` with `φ(t) = 1`, and let `σ(x) = t x t^{-1}`, an automorphism of `Q[L]` that
preserves support size. Every `a ∈ Q[H]` is uniquely `Σ_i a_i t^i` with `a_i ∈ Q[L]`, and
`|a| = Σ_i |a_i|`. Let `ab = 0` with `a, b ≠ 0`. Let `q` and `s` be the top indices of `a` and `b`.
The coefficient of `t^{q+s}` in `ab` is `a_q σ^q(b_s)`, because `a_i t^i b_j t^j = a_i σ^i(b_j) t^{i+j}`.
So `a_q · σ^q(b_s) = 0`, with both factors nonzero in `Q[L]`. Also
`|a_q| + |σ^q(b_s)| <= |a| + |b|`, with equality iff `a = a_q t^q` and `b = b_s t^s`.

(a) Applied to a minimal pair of `H`, this gives `μ(L) <= μ(H)`. Monotonicity gives the reverse.

(b) For a minimal pair, strict inequality would contradict (a). So `a = a_q t^q` and
`b = b_s t^s`. If the pair is normalized, `1 ∈ supp a ⊂ L t^q` forces `q = 0`, and likewise
`s = 0`. So `a, b ∈ Q[L]`.

(c) Normalized minimal pairs exist, by translation of any minimal pair (if `μ(H) = ∞` there is
nothing to prove). Fix one, `(a, b)`. By transfinite induction, `(a, b)` lies in `Q[H^{(α)}_Q]` and
is minimal there. At `α = 0` this holds. If it holds at `α`, then
`μ(H^{(α)}_Q) = μ(H)`, by monotonicity together with the pair itself. Let
`0 ≠ φ ∈ Hom(H^{(α)}_Q, Z)`. Then `φ/n` is onto `Z` for `n` the generator of the image, and it
has the same kernel as `φ`. By (b), `(a, b)` lies in `Q[ker φ]`. So it lies in
`Q[H^{(α+1)}_Q]`, where it is again minimal by monotonicity. At limit ordinals, take
intersections: the supports are finite sets lying in every earlier term. So `(a, b)` lies in
`Q[H^{(∞)}_Q]`, and `J = ⟨supp a ∪ supp b⟩ ≤ H^{(∞)}_Q`. Monotonicity squeezes
`μ(J)` and `μ(H^{(∞)}_Q)` to `μ(H)`. Finally let `φ : J → Z` be nonzero, normalized to be onto.
The pair is normalized and minimal in `J`, so by (b) its supports lie in `ker φ`. They generate
`J`, so `J ≤ ker φ`, a contradiction. Hence `Hom(J, Z) = 0`, and `b_1(J) = 0`, since `J` is
finitely generated.

## Item 2

(a) Torsion-freeness, amenability and `cd <= 2` pass to subgroups. If `J'` were elementary
amenable, then its normal core `N` in `J` would be too, and `J`, an extension of `N` by the
finite group `J/N`, would be elementary amenable. So `J'` is a counterexample. *The
equivalence with zero divisors:* a torsion-free elementary amenable group has a domain as
rational group algebra (Kropholler–Linnell–Moody). Conversely, if `Q[J']` is a domain, then
`J'` is virtually solvable by `amenable-finite-cd-domain-groups-are-virtually-solvable`,
hence elementary amenable. So `Q[J']` is not a domain, and `μ(J') < ∞`. Monotonicity gives
`μ(J') >= μ(J)`.

(b) This is `rf-weak-bass-defect-is-degree-two-approximation-defect`, item 3, with
`K = J`, which needs `cd_Z J <= 2` and `b_2(J) < ∞`. It gives `b_2(J') < ∞` and
`χ(J') = k χ(J)`, and `χ(J) = 1 − 0 + b_2(J)`.

(c) Let `n` generators present `J`, and let `P` be the relation module. Since `cd_Q J <= 2`,
Schanuel's lemma makes `P` projective in
`0 → P → Q[J]^n → Q[J] → Q → 0`. Restricted to `J'`, this becomes a projective resolution
`0 → P' → Q[J']^{kn} → Q[J']^k → Q → 0`. Let `Λ = Q[J'/L]` and apply `Λ ⊗_{Q[J']} −` to the
truncated resolution. By Shapiro's lemma, the resulting complex
`Λ ⊗ P' → Λ^{kn} → Λ^k` has homology `H_2(L; Q)`, `H_1(L; Q)` and `H_0(L; Q) = Q` (the last is
`Λ`-torsion). The module `Λ ⊗ P'` is projective over the PID `Λ`, hence free (Kaplansky). Its
rank is `r = dim_Q(Q ⊗_Λ Λ ⊗ P') = dim_Q(Q ⊗_{Q[J']} P')`. That is finite, because the complex
`Q ⊗ P' → Q^{kn} → Q^k` computes `H_*(J'; Q)`, whose `b_2(J')` and `b_1(J')` are finite. Now
`H_2(L; Q) = ker(Λ^r → Λ^{kn})` is a submodule of a free module over a PID, so it is free, of
some rank `ρ_2 <= r`. `H_1(L; Q)` is finitely generated. Ranks over `Q(t)` are additive, so
`r − kn + k = ρ_2 − ρ_1 + 0`. The same complex base-changed along `t ↦ 1` gives
`r − kn + k = χ(J')`. So `ρ_2 − ρ_1 = χ(J') = kχ(J) >= k` by (b).

(d) Take `J_1 ≤ L` as in a descent step. It is nontrivial and torsion-free. If `cd J_1 <= 1`,
then `J_1` is free by Stallings–Swan, and being finitely generated and nontrivial it has
`b_1 >= 1`, a contradiction. So `cd J_1 = 2`, and `χ(J_1) = 1 + b_2(J_1)`. Monotonicity and
item 1(a) give `μ(J_1) >= μ(L) = μ(J') >= μ(J)`. The canonical choice, `J_1` generated by a
normalized minimal pair of `L` (item 1(c)), has `μ(J_1) = μ(J')`.

## Item 3

The first two bullets are monotonicity, together with item 1(a) for the fibre part. The third
is item 2(d). The finite-index step: let `J = ⟨supp a ∪ supp b⟩` for a normalized minimal pair,
and let `J' ⊲ J` be proper of index `k`. If `(a, b)` lay in `Q[J']`, the supports would generate
a subgroup of `J'`. Writing `a = Σ_c a_c c` over coset representatives `c` of `J/J'`, with
`a_c ∈ Q[J']`, turns right multiplication by `a` on `Q[J] = ⊕_c Q[J'] c` into a `k × k` matrix
`A` over `Q[J']`, and similarly `b` gives `B`, with `AB = 0`. In `M_2(Q[L])`, the matrices
`e_{11} x` and `e_{22} y` multiply to zero for any nonzero `x, y`. So a leading-coefficient
argument on `A, B` yields matrices with product zero, and no element pair.

## Item 4

`D_∞ = ⟨r, s | s^2, srs = r^{-1}⟩` has index-2 subgroup `⟨r⟩ ≅ Z`, and `Q[Z] = Q[r^{±1}]` is a
domain. So `μ(Z) = ∞`, while `(1 − s)(1 + s) = 0` gives `μ(D_∞) = 4`, the lower bound.

`HW` is the torsion-free Bieberbach group of dimension 3 with holonomy `(Z/2)^2`. It has
`H_1(HW; Z) = (Z/4)^2`, so `b_1 = 0`, and it is not locally indicable. It is elementary
amenable and torsion-free, so `Q[HW]` is a domain (Kropholler–Linnell–Moody). Its finitely
generated subgroups are torsion-free and virtually abelian, so each contains a finite-index
`Z^m`, which maps onto `Z` when `m >= 1`. Hence it has no type (I) subgroup. The descent
`HW ⇝` (`Z^3 ↠ Z`, kernel `Z^2`) meets a locally indicable fibre, which has no nontrivial
finitely generated subgroup with `b_1 = 0`.
