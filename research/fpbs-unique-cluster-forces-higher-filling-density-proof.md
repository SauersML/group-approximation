---
rg: 2
id: fpbs-unique-cluster-forces-higher-filling-density-proof
kind: route
title: Induce the orbit relation on the infinite cluster, then bound beta_k by Morse inequalities of a filling complex
target: fpbs-unique-cluster-forces-higher-filling-density
requires: []
---

A direct deduction from published theorems. Every import is quoted verbatim.

## Imports

Source [G02]: Damien Gaboriau, *Invariants l2 de relations d'equivalence et
de groupes*, Publ. Math. IHES 95 (2002), 93-150,
https://www.numdam.org/item/10.1007/s102400200002.pdf. Text was extracted from
that PDF on 2026-09-17, with whitespace normalized.

- **(I1) [G02, Corollaire 3.16].** "Si R est produite par une action libre de
  Γ préservant µ sur X, alors pour tout n∈N βn(R,µ) = βn(Γ)."
- **(I2) [G02, Corollaire 5.5].** "Les nombres de Betti L2 de la relation R
  et de la relation RY, induite sur un borélien Y⊂X qui rencontre presque
  toutes les classes de R, sont reliés par la formule : βn(R,µ) =
  µ(Y)βn(RY,¯µ)."
  - Section 5.1 fixes the notation: "¯µ = µ|Y/µ(Y) la mesure induite
    normalisée et on définit la relation induite RY = R∩(Y×Y) sur (Y,¯µ)."
- **(I3) [G02, Théorème 3.13].** "Tous les R-complexes simpliciaux
  p-connexes ont le même nombre de Betti βp. Si Σ et Ψ sont deux
  R-complexes simpliciaux tels que Σ soit p-connexe et Ψ soit
  (p−1)-connexe, alors βp(Σ,R) ≤ βp(Ψ,R)."
  - [G02, Définition 3.14] then defines βn(R,µ) as "le n-ième nombre de
    Betti L2 de n'importe quel R-complexe simplicial n-connexe, par exemple
    celui de son R-complexe simplicial universel ER".
- **(I4) [G02, Proposition 3.19, Inégalités de Morse].** "Si les αi(Σ) sont
  finis pour i = 0,···,n, alors : αn(Σ)−αn−1(Σ)+···+(−1)^n α0(Σ) ≥
  βn(Σ)−βn−1(Σ)+···+(−1)^n β0(Σ)."
  - Here "αi(Σ) = dimM C(2)i(Σ) = νi(Σ(i)/R)/(i+1)!".
- **(I5) [G02, Section 2.2.3].** "La mesure νn(Σ(n)/R) est égale à celle
  d'un domaine fondamental F pour l'action de R sur Σ(n)."
  - Here Σ(n) is the space of ordered n-simplices (Section 2.2, "Un point
    (v0,v1,···,vn) ∈ Σ(n) est un n-simplexe ordonné").
  - νn is the natural counting lift of µ (Example 1.12).

## Proof

Identify the vertices of `G` with `Gamma`, with `o = e`, and let `Gamma`
act on configurations by `(gamma omega)(e') = omega(gamma^{-1} e')`. Then
`K(gamma omega) = gamma K(omega)` for clusters.

**Step 1 (the orbit relation).** Let `R` be the orbit relation of the free
p.m.p. action on `(Omega, mu)`.

- Freeness is part of the setting. For Bernoulli bond percolation with `p` in
  `(0,1)`, fix `gamma != e`. It moves infinitely many edges, since at most
  one edge at each vertex `x` can be the fixed edge `{x, gamma x}`. A
  configuration fixed by `gamma` is therefore constant along infinitely many
  nontrivial edge orbits, which is an event of measure `0`.
- If extra randomness is used, the product with an independent Bernoulli
  coordinate is still free. Everything below runs on the product space.

By (I1), `beta_k(R, mu) = beta_k(Gamma)`.

**Step 2 (Y meets almost every class).** Put `Y = Omega_inf`.

- Under uniqueness, a.s. some vertex `x` lies in the infinite cluster. Then
  `o = x^{-1} x` lies in `K_inf(x^{-1} omega)`, so `x^{-1} omega` is in `Y`.
- Hence `Y` meets a.e. class, and `theta = mu(Y) > 0`.

**Step 3 (the induced relation is the cluster relation).** Let `omega` and
`gamma omega` both lie in `Y`.

- Then `o` is in `K_inf(omega)`, and `gamma^{-1} o` is in `K_inf(omega)`,
  because `o` is in `K_inf(gamma omega) = gamma K_inf(omega)`. By uniqueness
  they lie in the same cluster.
- So the class of `omega` in `R_Y` is `{v^{-1} omega : v in K_inf(omega)}`.
- By freeness, `v -> v^{-1} omega` is a bijection from `K_inf(omega)` onto
  that class.
- Transport `Psi_omega` along this bijection. Take `omega' = gamma omega` and
  `v' = gamma v`. Then `v'^{-1} omega' = v^{-1} omega`. Since
  `Psi_{gamma omega} = gamma Psi_omega`, the transported complexes of
  `omega` and `omega'` are the same complex on the same class.
- This gives an `R_Y`-simplicial complex whose fibre over `omega` is `Psi_omega`.
  It is `(k-1)`-connected. Its vertex set is the class itself, so
  Lemma 2.3 of [G02] applies with `Sigma^(0) = R_Y`.

**Step 4 (induction).** By (I2) and Step 1,
`beta_k(R_Y, mu_bar) = beta_k(Gamma) / theta`.

**Step 5 (comparison).** Let `Sigma` be the universal `R_Y`-complex, which is
`k`-connected. By (I3) with `p = k`, and by Definition 3.14,
`beta_k(R_Y) = beta_k(Sigma, R_Y) <= beta_k(Psi, R_Y)`.

**Step 6 (Morse).**

- Admissibility and Step 7 show that `alpha_i(Psi)` is finite for
  `i <= k`.
- Add the Morse inequality (I4) at level `k` to the one at level `k-1`.
  At level `0` it reads `alpha_0 >= beta_0`.
- The alternating sums cancel except for the top terms. So
  `alpha_k(Psi) >= beta_k(Psi, R_Y)`.

**Step 7 (the density).** The ordered `k`-simplices `(v_0, ..., v_k)` of the
fibre over `omega` with `v_0 = omega` form a Borel fundamental domain for
`R_Y` acting on `Psi^(k)`: every orbit of an ordered simplex meets it
exactly once, namely when the base point is moved to its first vertex.

- In cluster coordinates, `v_0` is the vertex `o`.
- By (I5), `nu_k(Psi^(k)/R_Y) = k! E[#{k-simplices of Psi_omega containing o} | Y]`,
  since each unordered simplex containing `o` has `k!` orderings with
  `v_0 = o`.
- Hence `alpha_k(Psi) = E[#{k-simplices containing o} | Y] / (k+1)`.
- Sanity checks: `alpha_0 = mu_bar(Y) = 1`. For the standard Cayley graph of
  `F_2` viewed as an `R`-complex, `alpha_1 = 4/2 = 2`.

**Step 8.** Chain Steps 4-7:
`E[#k-simplices containing o | Y] / (k+1) >= beta_k(Gamma) / theta`.
Multiply by `theta = mu(Y)` to get the claim. QED.

## Values used downstream

- [G02, after Corollaire 0.3]: "les βj sont tous nuls sauf βℓ = ∏(pj −1)"
  for `F_{p_1} x ... x F_{p_l}`. So `beta_2(F_2 x F_2) = 1` and
  `beta_1(F_2 x F_2) = 0`.
- Fixed price one of `F_2 x F_2` is not used.
