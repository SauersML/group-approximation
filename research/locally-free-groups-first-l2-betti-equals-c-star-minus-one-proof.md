---
rg: 2
id: locally-free-groups-first-l2-betti-equals-c-star-minus-one-proof
kind: route
title: Exhaust by minimal-rank subgroups, use compressed implies L2-independent, and pass to the colimit without losing dimension
target: locally-free-groups-first-l2-betti-equals-c-star-minus-one
requires:
  - compressed-subgroups-of-free-groups-are-l2-independent
  - linnell-dimension-equals-skew-field-rank
  - lueck-dimension-additivity-cofinality-and-induction
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Direct proof. The full text is §§2–4 of the artifact. Write `N = N(Γ)`.

1. **Compressed exhaustion.** Enumerate `Γ = {g_1, g_2, …}` and let
   `T_0 = {g}` with `g ≠ 1`. Choose a finitely generated `Δ_n ⊇ T_n` of rank
   `r_n = c_{T_n}`, with generating set `S_n`, and put
   `T_{n+1} = T_n ∪ S_n ∪ {g_{n+1}}`.
   - Then `Δ_n ≤ Δ_{n+1}`, `⋃ Δ_n = Γ`, `r_n ≥ 1` (torsion-free), and
     `sup r_n = c*`.
   - Any finitely generated `L` with `Δ_n ≤ L ≤ Δ_m` contains `T_n`, so
     `rk L ≥ r_n`. So `Δ_n` is compressed in `Δ_m`, and by
     `compressed-subgroups-of-free-groups-are-l2-independent` it is
     `L²`-independent there.
2. **Homology as a restricted matrix map.** For `H ≤ F ≤ Γ` free on
   `h_1..h_p` and `f_1..f_q`, and a right `CΓ`-module `V`:
   - `H_1(H; V) = ker(V^p → V)`, from the free resolution by the augmentation
     ideal (Brown I.4.4).
   - The inclusion-induced map is the restriction of `θ_V : v ↦ vA`, where
     `A ∈ M_{p×q}(Z[F])` is the Fox matrix of `h_i − 1 = Σ_j a_ij (f_j − 1)`.
   - `ker φ = ker θ_V`, and `coker θ_V = V ⊗_{CF} M` with
     `M = CF^q / CF^p A`.
3. **No kernel dimension.** Assume `H` is `L²`-independent in `F`.
   - Then `v ↦ vA` is injective over the division closure `D_Q(F)` of `Q[F]`.
     By `linnell-dimension-equals-skew-field-rank`, the Linnell skew field
     `D(F)` contains `D_Q(F)`.
   - Gaussian elimination over `D_Q(F)` (`PAQ = [I_p | 0]`) keeps the map
     injective over `D(F)`. So `dim_{D(F)} D(F) ⊗ M = q − p`.
   - The same node gives `dim_{N(F)} N(F) ⊗ M = q − p`. Induction
     (`lueck-dimension-additivity-cofinality-and-induction`) gives
     `dim_N N ⊗_{CF} M = q − p`.
   - Additivity on `0 → ker θ → N^p → N^q → N ⊗ M → 0` gives
     `dim_N ker φ = 0`.
4. **Stage dimensions.** For `H` free of rank `p ≥ 1`,
   `dim_N H_1(H; N) = p − 1`. This follows from additivity on
   `0 → H_1 → N^p → N → H_0 → 0`, together with induction and
   `dim_{D(H)} D(H) ⊗_{CH} C = 0`, since `h_1 − 1` is invertible in `D(H)`.
5. **Colimit.** Imported (verbatim from Fisher–Lodha arXiv:2608.25988v1, Lemma
   `lem:direct-union-homology`, TeX source read September 17, 2026): "Suppose
   $G_0\leqslant G_1\leqslant \ldots $ are groups, let $G=\bigcup_{i\in
   \N}G_i$, and let $M$ be a fixed right $\C[G]$-module. Then
   $\homol_n(G;M)=\varinjlim_{i\in\N} \homol_n(G_i;M)$". The paper
   attributes it to Brown, *Cohomology of Groups*, Exercise V.5.3(a).
   - With `ψ_n : H_1(Δ_n; N) → H_1(Γ; N)`, `ker ψ_n = ⋃_m ker φ_{n,m}` has
     dimension 0 by step 3 and cofinality.
   - So `dim im ψ_n = r_n − 1` by step 4.
   - `H_1(Γ; N)` is the increasing union of the `im ψ_n`, so cofinality gives
     `beta_1^(2)(Γ) = sup (r_n − 1) = c* − 1`.

Trust surface: the three required nodes, the verbatim colimit lemma above
(standard), and Fox calculus (`I_{Z[F]}` is free on the `f_j − 1`).
