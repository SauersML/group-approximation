---
rg: 2
id: sp21-gs-certificate-shape-at-uniform-levels-proof
kind: route
title: Universal coefficients, the presentation complex, Lazard's exterior algebra on congruence characters, and splitting of pulled-back central extensions
target: sp21-gs-certificate-shape-at-uniform-levels
requires: []
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**Imported inputs.**
- **(T)** Finite-index subgroups of `Γ` have finite abelianization.
- **(Lz)** Lazard, *Groupes analytiques p-adiques* (1965), V.2.2.7. For `p` odd and
  `U` uniform, cup product gives `H^*(U;F_p) ≅ Λ^* H^1(U;F_p)`. Imported, not
  re-read; used only in (iii).
- **(Coh)** Continuous `H^2(U;F_p)` is the colimit of `H^2(U/W;F_p)` over open
  normal `W`, and inflation is multiplicative.

**(i)** By (T), `H_1(Δ;Z)` is finite, so `b_1 = 0`. The universal coefficient
theorem gives:
- `H^1(Δ;F_p) = Hom(H_1(Δ;Z), F_p)`, of dimension `d_p(H_1)`;
- `H^2(Δ;F_p) ≅ Hom(H_2(Δ;Z), F_p) ⊕ Ext(H_1(Δ;Z), F_p)`, of dimension
  `b_2 + d_p(tors H_2) + d`.

The certificate therefore needs `d²/4 - d > 0`, i.e. `d >= 5`.

**(ii)**
- Let `K` be the presentation complex of `⟨X|R⟩`. It is the 2-skeleton of a
  `K(Δ,1)`, and relative cells have dimension `>= 3`. So `H^2(Δ;F_p) -> H^2(K;F_p)`
  is injective.
- `χ(K) = 1 - |X| + |R|`, and `H^1(K;F_p) = H^1(Δ;F_p)`. So
  `dim H^2(K;F_p) = |R| - |X| + d`.

**(iii)**
- Inflation `H^1(U;F_p) -> H^1(Δ;F_p)` is injective, because `Δ` is dense in `U`.
  Its image is `V`, of dimension `d(U) = D`.
- The composite `Λ²H^1(U) --(Lz)≅--> H^2(U) --inf--> H^2(Δ)` sends `α∧β` to
  `inf α ∪ inf β`. Its rank is `C(D,2) - t`, so `r >= C(D,2) - t`.
- Substituting `d = D + e` into `r < d²/4` gives `C(D,2) - t < (D+e)²/4`. When
  `t = 0`, this is `2D(D-1) < d²`.

**(iv)**
1. Let `0 != c ∈ H^2(U;F_p)` with `inf_Δ(c) = 0`. By (Coh),
   `c = inf(c̄)` for some `c̄ ∈ H^2(U/W;F_p)` with `W` open normal, and `c̄ != 0`.
2. Let `1 -> F_p -> E -> U/W -> 1` be the extension with class `c̄`. Its pullback
   to `Δ` has class `inf_Δ(c) = 0`, so `Δ -> U/W` lifts to `s: Δ -> E`.
3. **`s` is onto.** The image `H = s(Δ)` maps onto `U/W`. If `H != E`, then
   `H ∩ F_p = 1`, so `H` is a section and `c̄ = 0`.
4. **`s` is not congruence.** If `s` extended continuously to `U`, the pullback of
   `c̄` to `U` would split, giving `c = 0`.

So `E` is a finite p-quotient of `Δ` that does not factor through `U`. ∎
