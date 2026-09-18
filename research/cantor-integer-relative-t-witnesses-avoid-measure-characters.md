---
rg: 2
id: cantor-integer-relative-t-witnesses-avoid-measure-characters
kind: claim
title: Almost-invariant measures on the dual of C(C,Z) are asymptotically null on measure characters, on characters supported in a proper clopen and on fixed sets, while Haar measure survives
distinct_from:
  cantor-integer-maps-by-v-are-not-a-t-menable: that asserts non-a-T-menability of C(C,Z) ⋊ V; this only constrains where measures witnessing the failure of relative (T) for (C(C,Z) ⋊ V, C(C,Z)) can live, and decides neither direction.
  cantor-integer-maps-by-v-have-haagerup-property: that is the affirmative case of Brothier's Problem B; this is a screen on total-variation almost-invariant measures on the dual group, which the affirmative case does not need.
  thompson-v-amenable-actions-are-free-off-fixed-points: that is about invariant means on all subsets of a discrete V-set; this runs the halving and IRS arguments for finitely additive limits of countably additive measures on the Borel sets of the dual compact group, and adds the measure-character section, which has no analogue there.
---

**ESTABLISHED.**

**Setting.**
- `A = C(C,Z)`, with `V` acting by `(g·f)(x) = f(g^-1 x)`.
- `Â = Hom(A, T)` is a compact group: the finitely additive `R/Z`-valued measures on clopen sets. `V` acts by
  `(g·χ)(f) = χ(f∘g)`.
- A sequence `μ_k` of Borel probability measures on `Â ∖ {0}` is *almost invariant* if
  `‖g_*μ_k − μ_k‖_TV → 0` for every `g ∈ V`. Convergence to `δ_0` is **not** assumed.
- **Measure characters.** For a finite real Borel measure `σ` on `C`, put `χ_σ(f) = ∫ f dσ mod 1`.
  Let `M = {χ_σ} ∖ {0}`.
- **Vanishing sets.** For a nonempty clopen `U`, `N_U = {χ ≠ 0 : χ vanishes on C(U,Z)}`.
- `Fix(g) = {χ : g·χ = χ}`.

**Statement.** Let `μ_k` be almost invariant on `Â ∖ {0}`.
1. **Section principle.** Let `E ⊆ Â ∖ {0}` be a `V`-invariant Borel set carrying a Borel map
   `χ ↦ λ_χ` into finitely additive probabilities on the clopen algebra, with `λ_(gχ) = g_*λ_χ`. Then
   `μ_k(E) → 0`.
2. **Measure characters.** `M` is Borel and `μ_k(M) → 0`. So every character of the form
   `f ↦ ∫ f dσ mod 1` is excluded in the limit. This includes:
   - point-evaluation and finitely or countably atomic characters (all of artifact §3(g), without a bound on
     the number of atoms);
   - Lebesgue densities, including the high-frequency family `2^F·λ` with `F ∈ C(C,Z)`;
   - Bernoulli and every other non-atomic finite measure.
3. **Characters supported in a proper clopen.** `μ_k(N_U) → 0` for every nonempty clopen `U`.
4. **Essential freeness.** `μ_k(Fix g) → 0` for every `g ≠ e`. For each finite `P ⊆ V ∖ {e}`, the set
   of characters whose stabilizer meets `P` is asymptotically null.
5. **Countable orbits.** If `E` is a countable `V`-invariant set whose stabilizers each fix a finitely
   additive probability on clopen sets (for example amenable stabilizers), then `μ_k(E) → 0`.
6. **Sharpness.** Haar measure `m_Â` is a `V`-invariant probability on `Â ∖ {0}`. It gives mass `0` to `M`,
   to every `N_U` and to every `Fix(g)` with `g ≠ e`. So the constant sequence `μ_k = m_Â` survives items
   1–5. No argument that ignores `μ_k → δ_0` can prove relative (T) for `(C(C,Z) ⋊ V, C(C,Z))`.

**Consequence (decomposition of the relative-(T) route).** By the criterion of artifact §3(f), `(G, A)` fails
relative (T) iff some almost-invariant `μ_k → δ_0` exists. Restricting to the complement of `M` and renormalizing
keeps both properties, since `μ_k(M) → 0`. The same holds for any fixed finite union of sets `N_U` and `Fix(g)`.
So relative (T) for `(G, A)` holds iff there is no such
sequence on the **wild** part. Relative (T) would give `brin-thompson-2v-is-not-a-t-menable`. The wild part
consists of:
- characters that are not reductions mod 1 of finite real measures;
- that are asymptotically not supported inside any fixed proper clopen set;
- with asymptotically essentially free orbits.

Haar-typical characters are exactly of this kind. Any proof must use smallness near `0` on the finitely many
test cones. Any disproof must build non-invariant, near-zero, wild, essentially free random characters.
Gaussian white noise mod 1 is the obvious wild candidate, and it dies for a different reason: Kakutani
singularity, recorded on `cantor-integer-maps-by-v-are-not-a-t-menable`.

Proof: `cantor-integer-witnesses-avoid-measure-characters-proof`.
