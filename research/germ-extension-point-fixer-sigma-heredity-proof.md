---
rg: 2
id: germ-extension-point-fixer-sigma-heredity-proof
kind: route
title: Split each character by its restriction to the base; the base-trivial Morse theorem with fixed singular points allowed, and the Meinert step on point-fixers
target: germ-extension-point-fixer-sigma-heredity
requires:
  - germ-extension-base-trivial-characters-lie-in-sigma
  - germ-extension-base-nontrivial-characters-via-point-fixers
  - germ-complex-and-bux-gonzalez-morse-inputs
---

Notation and hypotheses (H1)–(H4) are those of the claim. The base-trivial theorem is
`germ-extension-base-trivial-characters-lie-in-sigma`, with hypotheses 1–4 and proof steps 0–6 in its proof route. The
base-nontrivial theorem is `germ-extension-base-nontrivial-characters-via-point-fixers`. Item (Fin) is from
`germ-complex-and-bux-gonzalez-morse-inputs`.

## Lemma W (the base-trivial theorem with fixed singular points)

**Statement.** The base-trivial theorem remains true when its hypothesis 4 is replaced by:

- (4') every `B`-orbit in `sing(G)` is either infinite or a whole `G`-orbit.

**Proof.** Hypothesis 4 enters the proof route in one place only: Step 5, "`V↑` is infinite. By hypothesis 4 the orbit
`Ω_−` of (P3) is infinite." We check that (4') still makes `Ω_−` infinite. Everything else is unchanged.

1. In Step 3, `Ω_−` is a `B`-orbit contained in a `G`-orbit `O_1` with `|A_{O_1}| >= 2`. The constant `κ_{O_1}` is
   chosen so that `ν` takes both signs on `O_1`, and `Ω_−` is a `B`-orbit in `O_1` where `ν < 0`.
2. `ν` is constant on `B`-orbits (Step 3, "Constant on `B`-orbits"). It takes two different values on `O_1`, so `O_1`
   is not a single `B`-orbit. Hence `Ω_− != O_1`.
3. By (4'), `Ω_−` is infinite.

The rest of Step 5 goes through as before. `A_p != ∅` uses only (P2). The count of `V↑` uses only that `Ω_−` is
infinite and that `γ` has finitely many hidden or nontrivial coordinates. ∎

**Where (4') has content.** Let `p` be a `G`-fixed singular point. Its orbit `{p}` is a single `B`-orbit, so
`A_{{p}} = {0}`, and Step 3 takes `ν(p) > 0`. The hidden coordinate `p` still has an ascending germ: the trivial germ,
with `τ = ν(p) > 0`.

## The theorem

Fix `m >= 1`, assume `Φ_m(B,P)`, and let `M ⊆ P` be finite.

**Type `F_m`.**

- (H2) gives finitely many `B_M`-orbits on `sing(G_M)^m`, by projecting onto the first `m` coordinates.
- For `M' ⊆ sing(G_M)`, `Fix_{B_M}(M') = B_{M ∪ M'}`. Here `M ∪ M' ⊆ P` by (H1), so `Φ_m(B,P)` gives type `F_m`.
- (H3) gives finite germ index.
- So (Fin), applied to `G_M ⊇ B_M` with `n = m`, gives that `G_M` has type `F_m`.

**Characters.** Let `χ in Hom(G,R)` with `χ|_{G_M} != 0`, and put `ψ = χ|_B`.

*Case (a): `ψ != 0`.* Apply the base-nontrivial theorem to `G_M ⊇ B_M`.

- Its hypothesis 1 is (H2) projected to `m`-tuples. Its hypothesis 2 was shown above. Its hypothesis 3 is (H3).
- Let `M' ⊆ sing(G_M)` with `|M'| <= m`. Then `χ|_{Fix_{B_M}(M')} = ψ|_{B_{M ∪ M'}}`.
  - This is nonzero, because `B` localizes over `P` and `M ∪ M' ⊆ P`.
  - `Φ_m(B,P)` then puts it in `Σ^m(B_{M ∪ M'})`.

So `[χ|_{G_M}] in Σ^m(G_M)`.

*Case (b): `ψ = 0`.* Then `χ|_{G_M}` is a nonzero character of `G_M` vanishing on `B_M`. Apply Lemma W to
`G_M ⊇ B_M`.

- Hypothesis 1 is (H2). Hypothesis 3 is (H3). Hypothesis (4') is (H4).
- Hypothesis 2 asks that `Fix_{B_M}(M') = B_{M ∪ M'}` have type `F_m` for `|M'| <= m+1`. This holds by `Φ_m(B,P)`.

So `[χ|_{G_M}] in Σ^m(G_M)`.

The two cases give `Φ_m(G,P)`. Localization of `G` is not needed for this step. It is needed so that the conclusion
covers every nonzero `χ in Hom(G,R)` at every `M`, and so that the next level of a tower can use case (a). ∎

## The corollary

Induct on `i`. `Φ_m(B_0,P)` holds for every `m`, and the theorem gives `Φ_m(B_i,P) ⟹ Φ_m(B_{i+1},P)`. Take `M = ∅` in
`Φ_m(B_n,P)` for all `m`.

- `B_n` has type `F_m` for every `m`.
- Every nonzero `χ in Hom(B_n,R)` has `[χ] in Σ^m(B_n)`, because `χ|_{B_n} = χ != 0`.

So `Σ^∞(B_n) = S(B_n)`. ∎

## Calibration

- **Thompson's `F` over `F'`** (the calibration of the base-trivial theorem). `sing(F) = {0,1}`, both points fixed.
  (H4) holds, but (H3) fails: `(F)_0 = Z` and `(F')_0 = 1`. The conclusion `Σ^1(F) = S(F)` is false. So (H3) is what
  excludes this example; (H4) alone does not.
- **Trivial extension `G = B`.** (H1)–(H4) hold vacuously and the theorem says `Φ_m(B,P) ⟹ Φ_m(B,P)`.
