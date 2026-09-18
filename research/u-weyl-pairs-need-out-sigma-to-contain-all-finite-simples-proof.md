---
rg: 2
id: u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples-proof
kind: route
title: "Proof: an element of the Weyl group acting innerly on Sigma lifts into the centralizer; Schur's theorem in torsion-free Lambda makes the lifted finite part abelian; Minkowski bounds the action on homology"
target: u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples
requires:
  - normalized-benign-witnesses-give-the-semidirect-join
---

Verification tier: proposed-established. Elementary, plus Schur's theorem
(if `[D : Z(D)]` is finite then `[D, D]` is finite), Minkowski's lemma
(the kernel of `GL_b(Z) -> GL_b(Z/3)` is torsion-free), and the cited facts
on `Out` in item 5.

## Item 1

Let `Q ≤ W` be finite, `Q_0 = Q ∩ ker ρ`, and let `Q̃_0 ≤ M` be the preimage
of `Q_0`.
- **Lift into the centralizer.** For `x ∈ Q̃_0`, `conj(x)|_Σ` is inner, say
  `inn(σ_x)` with `σ_x ∈ Σ`. So `σ_x^{-1} x ∈ C_Λ(Σ)`. Hence `Q̃_0 = Σ D`
  with `D = Q̃_0 ∩ C_Λ(Σ)`.
- **The quotient.** `D ∩ Σ = C_Λ(Σ) ∩ Σ = Z(Σ)`. So
  `D/Z(Σ) ≅ DΣ/Σ = Q̃_0/Σ = Q_0`.
- **Schur.** `D` centralizes `Σ ⊇ Z(Σ)`, so `Z(Σ) ≤ Z(D)`, and
  `[D : Z(D)] ≤ |Q_0| < ∞`. By Schur, `[D, D]` is finite. `D ≤ Λ` is
  torsion-free, so `[D, D] = 1`.
- **Conclusion.** `D` is abelian, so `Q_0 = D/Z(Σ)` is abelian. If
  `Z(Σ) = 1`, then `D ≅ Q_0` is finite and torsion-free, so `Q_0 = 1`. ∎

## Item 2

- `Q_0 ⊴ Q` is abelian. If `Q` is nonabelian simple then `Q_0 = 1`, and `ρ|_Q`
  is injective.
- In general `Q/Q_0 ≅ ρ(Q) ≤ Out(Σ)`. ∎

## Item 3

`Σ` is of type `F`, so each `H_k = H_k(Σ; Z)` is finitely generated, and
`H_k = 0` for `k` above the dimension. `Out(Σ)` acts on `H_k`, since inner
automorphisms act trivially.
- **The automorphism group of `H_k`.** Write `H_k = Z^{b_k} ⊕ T_k` with
  `T_k` finite. `T_k` is characteristic, so there is a map
  `Aut(H_k) -> GL_{b_k}(Z) × Aut(T_k)`.
  - Its kernel consists of the maps `x -> x + h(x̄)` with
    `h : H_k/T_k -> T_k`, so it is `≅ Hom(Z^{b_k}, T_k)`, which is abelian.
- **`A_n` acts trivially for large `n`.** Let `n ≥ 5` and `A_n ≤ Out(Σ)`
  act nontrivially on `H_k`.
  - `A_n` is simple, so the action is injective.
  - The kernel above is abelian, so `A_n` injects into
    `GL_{b_k}(Z) × Aut(T_k)`.
  - The kernels of the two projections are normal and meet trivially. So
    `A_n` injects into one factor.
  - By Minkowski, finite subgroups of `GL_b(Z)` inject into `GL_b(Z/3)`.
  - So `n!/2 ≤ c(Σ) = max_k max(|GL_{b_k}(Z/3)|, |Aut(T_k)|)`.
- **Conclusion.** Take `n_0` with `n_0!/2 > c(Σ)`. For `n ≥ n_0`, every
  `A_n ≤ W` embeds in `Out(Σ)` by item 2, with image in `T(Σ)`. ∎

## Item 4

- `U` contains every finitely presented group, hence every `A_n`.
- A normalized witness `(Λ, Σ)` for `N_U ⊴ F(B)` gives
  `U = F(B)/N_U ↪ N_Λ(Σ)/Σ = W` (item 2 of
  `normalized-benign-witnesses-give-the-semidirect-join`), with `Λ` of type
  `F`, hence torsion-free.
- Items 2 and 3 give `A_n ≤ T(Σ)` for every `n ≥ n_0(Σ)`.
- The same argument works for any `G ≤ W` containing `A_n` for infinitely
  many `n`. ∎

## Item 5

If `Out(Σ)` has a torsion-free subgroup of index `d`, then every finite
subgroup meets it trivially, so it has order `≤ d`. That contradicts
`A_n ≤ Out(Σ)` for all large `n`. If `T(Σ)` is torsion-free, it contains no
`A_n`. The listed classes satisfy these conditions:
- **`Out(F_r)`.** The kernel of `Out(F_r) -> GL_r(Z/3)` is torsion-free
  (Baumslag--Taylor).
- **`GL_r(Z)`.** Minkowski.
- **Mapping class groups of closed surfaces.** The level-3 subgroup is
  torsion-free (Serre).
- **`Out(A_Γ)`.** It is virtually torsion-free (Charney--Vogtmann, 2009).
- **Finite `Out(Σ)`.** Its order bounds all its finite subgroups. Mostow
  rigidity gives finite `Out` for closed hyperbolic `n`-manifold groups,
  `n ≥ 3`. ∎

## Calibration

- **Finite `Q = F/N`.** `Σ = N` is free of rank `r ≥ 2` (when `rk F ≥ 2`
  and `|Q| ≥ 2`), so `Z(Σ) = 1`, and item 1 predicts `Q ↪ Out(N)`.
  - This is correct: if `f ∈ F` acts on `N` as `inn(ν)`, then `ν^{-1} f`
    centralizes the finite-index subgroup `N` of `F`. That centralizer is
    trivial, so `f ∈ N`.
  - No contradiction with the bound: `r = 1 + |Q|(rk F - 1)` grows with `|Q|`.
- **`Γ/M` with `M ⊴ Γ` of type `F`.** Item 2 applies with `Σ = M`,
  `W = Γ/M`, and is consistent with every known example. ∎
