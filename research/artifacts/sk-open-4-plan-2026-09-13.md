# sk-open-4 plan: what G_X sees of the dynamics of X

Lens: the dictionary between an infinite minimal subshift (X,T) and G_X = EL_3(R_X), where R_X = LC(X,F_2) ⋊_T Z.
Each row below will be proved, cited, or firewalled.

## Target rows
- **(K) Algebraic K-theory.** For every infinite minimal Cantor system and every prime power q, split for n ≥ 0:
  `K_n(LC(X,F_q) ⋊_T Z) ≅ (K^0(X,T) ⊗ K_n(F_q)) ⊕ K_{n-1}(F_q)`.
  Over F_2 this gives K_1 = Z[u], K_2 = 0, K_3 ≅ K^0(X,T)/3, K_4 ≅ Z/3, and in general
  K_{2i+1} ≅ K^0(X,T)/(2^{i+1}-1) and K_{2i} ≅ Z/(2^i-1).
  It extends `subshift-crossed-product-k0-is-coinvariant-group` through the same ABC fibration plus Quillen's K_*(F_q).
- **(St) Groups.**
  - The winding class: diag(u,1,1) ∈ GL_3(R_X) is not in E(R_X), and the unit of γ ∈ [[T]] has K_1 class equal to its index.
  - The stable elementary group E(R_X) = St(R_X) is centrally closed, and H_3(E(R_X);Z) ≅ K^0(X,T)/3.
  - Finite rank: EL_n(R_X) ≅ St_n(R_X) with trivial Schur multiplier. This is conditional on a stable-range bound (open claim).
- **(E) Spectrum and factors.** For p ≥ 2, the following are equivalent:
  - e^{2πi/p} is a continuous eigenvalue;
  - [1] ∈ pK^0(X,T);
  - M_p(F_2) embeds unitally in R_X;
  - R_X ≅ M_p(S).
  Then G_X ≅ EL_{3p}(R_{(U,T^p)}) and SL_{3p}(F_2[t^{±1}]) ≤ G_X. A factor map X → Y gives a unital embedding R_Y ⊆ R_X, so G_Y ≤ G_X.
- **(M) Invariant measures.**
  - Each invariant probability μ gives a conjugation-invariant length function ℓ_μ(g) = rk_μ(g − I) on G_X, with ℓ_μ(g) > 0 for g ≠ 1.
  - It is the normalized-rank limit of the note's finite models along periodic words whose empirical measures tend to μ, and every μ arises this way.
  - μ ↦ ℓ_μ is affine and injective: ℓ_μ(e_12(e_U)) = μ(U).
- **(F) Firewalls.** K-theory and stable homology depend only on the abstract group K^0(X,T). So they cannot see the order, entropy or complexity. Literature check, stated with its bounds: entropy within strong orbit equivalence classes.

## Why this matters for the note
The theorem accepts any minimal subshift. The dictionary says what of X survives in the ring and the group:
- the dimension group, which appears mod 3 in K_3;
- rational spectrum, as matrix-ring structure;
- invariant measures, as rank length functions.
At most one sentence reaches the note, and only if it earns its length.

## Not duplicated
- sk-rigidity-ring and sk-rigidity-intrinsic own "G_X ≅ G_Y ⇒ ?" (reconstruction, order on K_0, SOE). Row (K) hands them computed invariants; I do not attempt reconstruction.
- Owned elsewhere:
  - sk-lef-growth: recurrence and LEF growth;
  - sk-characters: characters;
  - sk-subgroups: [[T]] and finite subgroups;
  - sk-word-problem: language and word problem;
  - sk-stable-rank-a/b: sr(R_X), which the finite-n part of (St) depends on.
- Normal subgroups ↔ subsystems for non-minimal X is already on main, and I only cite it:
  - non-MF tex thm:core-mf-radical;
  - `pestov91-cycle-core-exact-mf-reflection-2026-09-13.md`, `pestov91-directed-seams-and-normal-lattices-2026-09-13.md`, `pestov91-seam-normal-lattice-2026-09-13.md`.

## Deliverables
- Cairn claims with proof routes for (K) and (E), and a claim for (M).
- An open claim with Attempts for finite-n (St).
- Artifact parts.
- `sk-open-4-proposal-2026-09-13.md`.
