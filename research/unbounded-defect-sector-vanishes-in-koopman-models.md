---
rg: 2
id: unbounded-defect-sector-vanishes-in-koopman-models
kind: claim
title: In every sofic model of the hyperbolic Leavitt cover each finite-dimensional kernel type has block-algebra multiplicity at most its dimension, so the unbounded-multiplicity sector is zero and the defect projection Q = P - P' vanishes
distinct_from:
  jones-index-blind-on-unbounded-defect-sector: that shows the Jones-type index on H_inf is the defect indicator, equal to 1 iff P' = P; this shows H_inf = 0 and P' = P in every sofic model, so the indicator is always 1 and the sector it was read on is empty.
  bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect: that proves Kazhdan-projection sizes blind on the bounded-multiplicity sector H_b; this proves the bounded-multiplicity hypothesis always holds, so H_b is the whole finite-dimensional isotypic part H minus H_wm.
  kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure: that forces W_rho(g) scalar on A-submodules of bounded multiplicity and records l^2(G/N) with A = C as sharp; this shows that when A is the kernel's invariant algebra in a measure-preserving model, every W_rho has multiplicity at most dim rho, so the hypothesis is automatic.
  component-space-sizes-miss-leavitt-cover-defect: that treats sizes read through component spaces of the trivial type; this bounds the multiplicity of every finite-dimensional type and removes the nested-projection defect on all of them.
artifacts:
  - research/artifacts/rnorm-fibrewise-defect-2026-09-12.md
---

**ESTABLISHED** (route `unbounded-defect-sector-vanishes-proof`). Not independently
reviewed. This is a no-leverage result. It establishes no root, and
`relative-normalization-modulo-kazhdan-kernel` and `nonsofic-hyperbolic-group`
stay OPEN.

## Statement

The setting is that of `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`:
- **Cover:** `1 -> N -> G -> R^x -> 1`, with `Gamma_hat = pi^-1(EL_alpha(R))` and
  strict compressor `u`.
- **Model:** a sofic representation `sigma : G -> S_U`, acting by Koopman unitaries
  on `H = L^2(X_U, mu_U)`, with `A = D^N = D^G`.
- **Sectors:** `H = H_b (+) H_wm (+) H_inf`, `H_rho = V_rho (x) W_rho`, and
  `A|_(H_rho) = 1 (x) A_rho`.
- **Defect data:** `P` is the fixed-space projection of `W_rho(Gamma_hat)`,
  `P' = W_rho(u)^* P W_rho(u)`, relabeled so that `P' <= P`, and `Q = P - P'`.

1. **Gram bound. No group hypotheses.** Let a group `N` act on a probability space
   `(Y, mu)` by measure-algebra automorphisms, and let `A = L^inf(Y)^N` act by
   multiplication on `L^2(Y)`. For every irreducible `rho` of dimension `d`, `A`
   has multiplicity at most `d` on `W_rho = Hom_N(V_rho, L^2(Y))`. So
   `End_A(W_rho)` is a finite type I von Neumann algebra.
2. **Nested conjugates coincide.** Let `V` be a unitary and `P` a projection on
   `W_rho`, both commuting with `A_rho`. If `V^* P V <= P` or `P <= V^* P V`, then
   `V^* P V = P`.
3. **The cover.** For every sofic representation `sigma`:
   - `H_inf = 0` and `H_b = H (-) H_wm`;
   - `Q = 0` for every `rho` and every choice of scalars in `W_rho`, so `Ind(E_P) = 1`
     in the notation of `jones-index-blind-on-unbounded-defect-sector`;
   - `W_rho(g)` is scalar on `W_rho` for every `g in G`, so `sigma(g)|_(H_rho)`
     lies in the strong closure of `T . sigma(N)|_(H_rho)` for every `rho`;
   - `N`, `Gamma_hat`, `u^-1 Gamma_hat u` and `G` have the same closed invariant
     subspaces in `H (-) H_wm`, and every finite-dimensional subrepresentation of
     `sigma|_(Gamma_hat)` lies there;
   - items 1–4 of `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`
     hold with `H_b = H (-) H_wm`.

## Remarks

- **(T) does not enter on the fibres.** Items 1 and 2 use no property (T), no
  soficity and no property of `R^x`. The inputs specific to the cover are items
  1–3 of `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure` and
  block invariance, which puts `W_rho(u)` and `P` in `End_A(W_rho)`. Nothing is
  disintegrated, so no measurability issue arises.
- **Boundary.** Take `W = l^2(R^x / EL_alpha(R)) (x) l^2(Nat)` with
  `A_rho = 1 (x) l^inf(Nat)`, where `W_rho` is the quasi-regular representation.
  - The base coset is fixed by `EL_alpha(R)` but not by `u^-1 EL_alpha(R) u`, so
    `Q != 0` on every fibre.
  - The spectral gap is uniform.
  - Only the Koopman hypothesis fails: `A_rho` has infinite multiplicity.
- **For RNORM.** `Q = 0` holds in every sofic model, so it gives no leverage. A size
  that registers the defect must be read on `H_wm`, where `sigma|_N` has no
  finite-dimensional subrepresentation, or from realizers directly.
- **Novelty.** Item 1 is the matrix-valued relative form of simple spectrum for
  ergodic actions, and is standard in substance.
