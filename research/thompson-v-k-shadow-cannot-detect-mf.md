---
rg: 2
id: thompson-v-k-shadow-cannot-detect-mf
kind: claim
title: The K-theoretic, tracial and rational-cohomological shadow of an MF model of Thompson's V is realizable, so no argument through it proves V non-MF
distinct_from:
  thompson-v-is-not-mf: that is the open non-MF statement; this proves that every obstruction factoring through ordered K_0, traces, finite-subgroup multiplicities or rational cohomology of V and its torsion centralizers is vacuous for it.
  dadarlat-matricial-stability-obstruction: that is an obstruction to matricial stability from nonzero even rational cohomology; this shows its input, and the delocalized input, vanish for V and that the K_0 shadow of MF is realizable.
  lueck-surjective-assembly-traces-lie-in-lambda-g: that bounds trace values under surjective assembly; this uses the bound (rationality) to build an integer-valued positive K_0 shadow with nonzero sign class.
---

**ESTABLISHED** by `thompson-v-k-shadow-cannot-detect-mf-proof`. Class-killing
obstruction for `thompson-v-is-not-mf`.

**Notation.** `V = G_(2,1)` acts on the Cantor set `{0,1}^N`. Let `s ∈ V` be the
involution `0w ↔ 1w`, and let `p_s = (1 - s)/2 ∈ C*(V)`, a projection. For a
sequence `k = (k_n)` of positive integers put `Q_k = ∏ M_(k_n) / ⊕ M_(k_n)`.
A projection `P` in `M_m(Q_k)` lifts to projections `P_n ∈ M_m(M_(k_n))`.
Their ranks are eventually independent of the lift, which defines the rank
class `r(P) ∈ ∏Z/⊕Z`. Let `ε` be the trivial character and `τ = τ_reg`, both
on `C*(V)`.

**(i) Reduction to one class.** `V` is MF (as defined in `thompson-v-is-not-mf`)
if and only if there are a sequence `k` and a unital *-homomorphism
`Ψ : C*(V) → Q_k` with `r(Ψ(p_s)) ≠ 0`. Equivalently: `V` is not MF iff every
operator-norm asymptotic representation `ψ_n : V → U(k_n)` has
`ψ_n(s) → 1` in norm. In rank terms, the spectral projection of `ψ_n(s)` on
`{Re z < 0}` is eventually `0`.

**(ii) The K_0 shadow is realizable.** There are integer sequences
`a_n ≥ 0` and `b_n ≥ 2`, with `k_n = a_n + b_n` and `n!` dividing `b_n`, such that
`θ_n = a_n ε_* + b_n τ_*` defines a group homomorphism
`θ : K_0(C*(V)) → ∏Z/⊕Z` with:
- (S1) `θ` is positive: `θ[P]` is represented by a sequence of nonnegative
  integers for every projection `P ∈ M_m(C*(V))`;
- (S2) `θ[1] = [(k_n)]`;
- (S3) `|θ_n(x)| ≤ C_x k_n` for every `x`;
- (S4) `θ_n(x)/k_n → (1-t) ε_*(x) + t τ_*(x)` for every `x`, where
  `t ∈ [0,1]` can be prescribed in advance;
- (S5) `θ[p_s] = [(b_n/2)] ≠ 0`.

Every rank shadow `r ∘ Ψ_*` of a unital `Ψ : C*(V) → Q_k` satisfies
(S1)--(S3), and satisfies (S4) along some ultrafilter for some `t`, by
`thompson-v-character-simplex`. So those properties, together with every
bounded trace on `C*(V)`, are consistent with (S5). By (i), (S5) is exactly
the MF condition read on K_0.

**(ii-a) Finite-subgroup packets.** For a finite `H ≤ V` and `n ≥ |H|` (so `|H|`
divides `b_n`), `θ_n` restricted to `K_0(C*(H)) = R(H)` is the representation
`ρ_H = a_n 1_H ⊕ (b_n/|H|) reg_H`. This system is exactly compatible with
restriction and conjugation. On `⟨s⟩` the sign representation has
multiplicity `b_n/2`.

**(iii) Rational cohomology gives no input.** `H^(2k)(V; Q) = 0` and
`H^(2k)(C_V(g); Q) = 0` for every torsion `g` and every `k ≥ 1`. So
`dadarlat-matricial-stability-obstruction` (Theorems 1.1 and 1.2) has no input
for `V`, and neither does any refinement indexed by torsion conjugacy classes.

## Death step and what survives

Take an argument that assumes an MF model `ψ` exists and derives a
contradiction using only:
- `Ψ_*` on ordered `K_0` with its unit;
- the limit trace, which lies in the character simplex;
- finite-subgroup multiplicities;
- positive-degree rational (co)homology of `V` or of its torsion centralizers.

Such an argument must conclude `r(Ψ(p_s)) = 0`. It dies at that step, because
`θ` has all the listed properties and `θ[p_s] ≠ 0`. `K_1` adds nothing, since
`K_1(Q_k) = 0` (six-term sequence of `⊕M ↪ ∏M ↠ Q_k`, not re-derived here).

What survives is information that is not homotopy invariant: operator-norm
defects of the infinite-order relators, and how local near-representations
glue. That is the relator-defect lane. `θ` is not claimed to come from any
`Ψ`.
