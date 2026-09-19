---
rg: 2
id: amenable-cd-two-pro-p-completions-not-golod-shafarevich
kind: claim
title: In a finitely generated amenable group of cd 2 the mod-p Euler characteristic is exactly multiplicative, so Golod-Shafarevich non-amenability caps b_1(N;F_p) by 2 + 2 sqrt([K:N] chi_Q(K)) for every finite-index N; if chi_Q = 0 every pro-p completion is p-adic analytic of dimension at most 2
distinct_from:
  rf-weak-bass-defect-is-degree-two-approximation-defect: that proves rational multiplicativity of chi_Q and identifies the defect with the growth of b_2 along residual chains; this proves the same identity over F_p for all finite-index subgroups (no residual finiteness), and feeds it into the Golod-Shafarevich inequality to bound b_1(N;F_p) and b_1(N;Q) by O(sqrt [K:N]) uniformly over all finite-index subgroups
  amenable-cd-two-bass-defect-equals-euler-characteristic: that identifies the Bass defect of the relation module with chi_Q(K); this constrains the mod-p and rational homology of every finite-index subgroup of a group with chi_Q(K) > 0, and pins down the pro-p completions when chi_Q(K) = 0
---

**ESTABLISHED** (proposed; referee pending) through
`amenable-cd-two-pro-p-completions-not-golod-shafarevich-proof`, from
`rf-weak-bass-defect-is-degree-two-approximation-defect` (item 1, finite-quotient Swan). Recalled
imports: Bass (1963, big projective `Z[F]`-modules are free); Swan (1960); injectivity of the
decomposition map for projective modules over `Z_p[F]` (Serre, *Linear representations*, §16.1,
Cor. 2 of Thm. 34); injectivity of `H^2(Γ_p̂; F_p) → H^2(Γ; F_p)` for pro-p completions;
Golod–Shafarevich–Vinberg in Ershov's formulation, and Ershov–Jaikin-Zapirain (Proc. LMS 102
(2011), Thm. 1.1): an abstract group whose pro-p completion is Golod–Shafarevich has an infinite
quotient with property (T), so it is not amenable; Lubotzky–Mann (pro-p groups of finite rank are
p-adic analytic).

**Setting.** `K` is a finitely generated amenable group with `cd_Z K <= 2` and `b_2(K) < ∞`, and
`χ = χ_Q(K) = 1 − b_1(K) + b_2(K)`. For a subgroup `N` of finite index and a field `k`, write
`b_i(N; k) = dim_k H_i(N; k)`. `N_p̂` is the pro-p completion, `d(G) = dim H^1(G; F_p)` and
`r(G) = dim H^2(G; F_p)` for a pro-p group `G`. No residual finiteness and no torsion-freeness
beyond `cd < ∞` is assumed.

1. **Exact Euler characteristics in every characteristic.** For every subgroup `N` of finite
   index, every prime `p` and `k ∈ {Q, F_p}`, `b_2(N; k) < ∞` and

   > `1 − b_1(N; k) + b_2(N; k) = [K:N] · χ`.

   In particular `H_2(N; Z) ≅ Z^{b_2(N;Q)}` is free, and the `p`-rank of the torsion of
   `H_1(N; Z)` equals `b_2(N; F_p) − b_2(N; Q)`.
2. **Golod–Shafarevich bound.** For every finite-index `N` and prime `p`, with `d = b_1(N; F_p)`:

   > `d <= 1`, or `(d − 2)² <= 4 [K:N] χ`; in all cases `b_1(N; Q) <= b_1(N; F_p) <= 2 + 2 √([K:N] χ)`.

   The pro-p completion `G = N_p̂` has `d(G) = d` and `r(G) <= d − 1 + [K:N] χ`, and
   `d(G)² <= 4 r(G)` unless `d(G) <= 1`. In particular `χ >= 0`, i.e. `b_1(K) <= 1 + b_2(K)`,
   for every finitely generated amenable `K` of cd 2 with `b_2(K) < ∞`. Previously
   (item 4 of `rf-weak-bass-defect-is-degree-two-approximation-defect`) this was known only for
   residually finite `K`. So `D(P) = χ >= 0` for the relation module of every such `K`.
3. **The case `χ = 0`** (which holds for every known example, and for all `K` if Kropholler's
   question has a positive answer in dimension 2). Then `b_1(N; F_p) <= 2` for every
   finite-index `N` and every `p`, and if `b_1(N; F_p) = 2` then `r(N_p̂) = 1`. Every pro-p
   completion of every finite-index subgroup of `K` is a p-adic analytic group of dimension at
   most 2.
4. **Counterexamples.** A counterexample `K` to Kropholler's question in dimension 2 with finite
   abelianization (these exist if any counterexample does, by
   `amenable-cd-two-kropholler-iff-locally-indicable`) has `χ = 1 + b_2(K) >= 1`, and for every
   finite-index `N` and prime `p`:
   - `b_1(N; F_p) <= 2 + 2 √((1 + b_2(K)) [K:N])`. In particular `d(K_p̂) <= 2 + 2√(1 + b_2(K))`;
   - `b_2(N; Q) = (1 + b_2(K)) [K:N] − 1 + O(√[K:N])`, with an explicit constant, for every
     finite-index `N`, not only along residual chains. So the slope-`(1 + b_2(K))` growth of
     `b_2` required by item 5 of `rf-weak-bass-defect-is-degree-two-approximation-defect` holds
     with a square-root error term, and the rational homology of every finite cover of a
     counterexample is dominated by `H_2`, as for a finite group.

**Calibrations.** `Z²` (`d = 2`, `r = 1`), the Klein bottle group (`p = 2`: `d = 2`, `r = 1`) and
`BS(1,m)` (`d = 2` iff `p | m − 1`, else `d = 1`; all finite-index subgroups are of the same form)
have `χ = 0` and meet item 3 with equality at `d = 2`, `r = 1`; their pro-p completions are
`Z_p²`, `Z_p ⋊ Z_p` or `Z_p`. Non-amenable controls: the free group `F_2` (`cd 1`, `χ = −1`,
`d = 2`, `r = 0`) and surface groups of genus `g >= 2` (`d = 2g`, `r = 1`) satisfy item 1 but
violate the inequality of item 2, as they must, since their pro-p completions are
Golod–Shafarevich. The torsion hypothesis cannot be dropped from item 1: `D_∞` has
`hd_Q = 1`, `χ_Q = 1`, but its index-2 subgroup `Z` has `χ_Q = 0`.

**What this changes.** The mod-p and rational first Betti numbers of all finite-index subgroups of
an amenable cd-2 group grow at most like the square root of the index, uniformly and without
residual finiteness. This is stronger than rank-gradient zero (Abért–Jaikin–Nikolov) and than
Lück–Osin, and it comes from the exact Euler identity of item 1, which uses projectivity of the
relation module. In the expected world (`χ = 0`) the finite-index subgroups have at most two
independent `Z/p` quotients and the pro-p completions are those of `Z²`, `Z_p ⋊ Z_p` or `Z_p`
(up to finite groups).
A counterexample would have finite covers whose rational homology looks like that of a finite
group: `b_1 = O(√index)` and `b_2 ~ (1 + b_2(K)) · index`. The Golod–Shafarevich method cannot
refute this. It bounds generators by relations, and a counterexample has many relations and few
generators. This is the exact point where the pro-p route stops (proof, §4).
