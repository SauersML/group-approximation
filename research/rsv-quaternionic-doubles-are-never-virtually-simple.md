---
rg: 2
id: rsv-quaternionic-doubles-are-never-virtually-simple
kind: claim
title: The non-residually-finite doubled lattices of Rungtanapirom–Stix–Vdovina in products of trees are never virtually simple, so they give no f.p. simple group of cd > 2
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-cd3-sources.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed). It uses only the exact sequence that
Rungtanapirom–Stix–Vdovina (RSV) state, as recorded in the artifact. No priority claimed.

**Setting.** Let `Γ` act simply transitively on the vertices of a product `Z = T_1 × ... × T_d` of
trees of valency `>= 2`. Let `Γ_0` be its type-preserving subgroup, `Y = Γ_0\Z`, and
`D(X) = (Γ/Γ_0)\(Y ⊠_{□^d} Y)` the doubling of `X = Γ\Z` (RSV §5). For RSV's quaternionic `Γ_S`
with `#S_0 >= 2`, `π_1(D(X_S))` is a torsion-free lattice in a product of `#S_0` trees that is not
residually finite (RSV Theorem l.2925). RSV (l.754) ask whether these lattices are virtually simple.

**Claim.** No finite-index subgroup of `π_1(D(X))` is simple. More strongly, every finite-index
subgroup has a nontrivial normal subgroup of infinite index, so none is just-infinite.

**Proof.**
1. **The kernel.** `Z ⊠_{□^d} Z = ∏_i (T_i ⊠_{□^1} T_i)` is a connected unramified cover of
   `D(X)` with covering group `Γ ×_{Γ/Γ_0} Γ` (RSV Corollary `cor:pi1ofdouble`, l.2741–2751). It is
   not the universal cover, which is the product of the trees covering the graphs
   `T_i ⊠_{□^1} T_i`. This gives RSV's exact sequence
   `1 → N → π_1(D(X)) → Γ ×_{Γ/Γ_0} Γ → 1` with `N = ∏_i π_1(T_i ⊠_{□^1} T_i)`.
2. **`N` is nontrivial.** `T ⊠_{□^1} T` is the graph on `T_+ × T_+ ⊔ T_- × T_-` whose edges are
   pairs of edges of `T`. Take `x ∈ T_+` with neighbours `a ≠ b`, and `c ∈ T_-` with neighbours
   `y ≠ y'`. Then `(x,y) – (a,c) – (x,y') – (b,c) – (x,y)` is an embedded 4-cycle. A graph with a
   cycle has nontrivial free fundamental group, so each factor of `N` is a nontrivial free group.
3. **Infinite index.** The quotient `Γ ×_{Γ/Γ_0} Γ` contains `Γ_0 × Γ_0`, which is infinite.
4. **Every finite-index subgroup.** For `Δ ≤ π_1(D(X))` of finite index, `N ∩ Δ` has finite index in
   the infinite group `N`, so it is nontrivial. It is normal in `Δ`, with `[Δ : N ∩ Δ] = ∞`. So `Δ`
   is neither simple nor just-infinite.

**Consequence.** The route "finite residual of an RSV double, via the Bader–Shalom normal subgroup
theorem" to an f.p. simple group of finite cd `> 2` (Kourovka 21.46) is closed. Bader–Shalom's
hypotheses must fail for these lattices, since they would force just-infiniteness. The live
candidate is `amir-lazarovich-lattice-torsion-is-square-diagonals`.

## Referee (bh-ref-misc, 2026-09-18): PASS

Internal referee lane, not an external review. Checked against the TeX e-print of
arXiv:1808.03290 read on MSI (`/scratch.global/sauer354/bhfe/rsv/main.tex`).
- **The question.** l.754 reads "It is tempting to ask if these non-residually finite lattices are also
  virtually simple". "These" are the doubles `π_1(D(X_S))` of Theorem `thm:non residually finite doubles`
  (l.2922–2925, `#S_0 >= 2`).
- **Inputs.** Checked at source:
  - the definition of `D(X)` (l.2635–2640);
  - the vertex set `𝔤_+ × 𝔤_+ ⊔ 𝔤_- × 𝔤_-` of `𝔤 ⊠_{□^1} 𝔤` (l.2651);
  - connectedness (Lemma `lem:doubletreeconnected`, l.2645);
  - the exact sequence (Corollary `cor:pi1ofdouble`, l.2741–2746), stated for every `Γ` acting simply
    transitively on the vertices of `Z`. The arithmetic case is the proposition at l.2870–2873.
- **Steps 2–4.** Each of the four edges of the 4-cycle is a pair of edges of `T` with matching
  orientation. The four vertices are distinct because `a ≠ b` and `y ≠ y'`. So each factor of `N` is a
  nontrivial, hence infinite, free group. Steps 3 and 4 are correct as written.

**Correction made in this pass.** Step 1 used to say that `Z ⊠ Z` is the universal cover of `D(X)`, and
that `Γ ×_{Γ/Γ_0} Γ` acts on `Y ⊠ Y`. Both were wrong as stated: step 2 shows `Z ⊠ Z` is not simply
connected, and the group acting on `Y ⊠ Y` is `Γ/Γ_0`. Step 1 now follows RSV's own proof of
`cor:pi1ofdouble`. The argument is unchanged.

**Remark.** The answer is immediate from RSV's own Corollary `cor:pi1ofdouble`, which they do not relate
to the question at l.754. Priority was not searched beyond the paper.
