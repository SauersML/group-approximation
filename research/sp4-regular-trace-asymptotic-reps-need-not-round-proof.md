---
rg: 2
id: sp4-regular-trace-asymptotic-reps-need-not-round-proof
kind: route
title: Compress a balanced pair of regular principal series by one dimension; property (T) blocks rounding
target: sp4-regular-trace-asymptotic-reps-need-not-round
requires:
  - sp4-fp-regular-principal-series-irreducible
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
---

## Imports checked at source (2026-09-13, texts read on MSI)

- **(I1)** Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, author PDF
  `KazhdanTotal.pdf`, Proposition 1.1.9: "Let G be a topological group, let
  (Q,ε) be a Kazhdan pair for G, and let δ > 0. Then, for every unitary
  representation (π,H) of G and every (Q,δε)-invariant vector ξ, we have
  ‖ξ − Pξ‖ ≤ δ‖ξ‖, where P : H → H^G is the orthogonal projection on the subspace
  H^G of all G-invariant vectors in H."
- **(I2)** Same book, after Theorem 1.3.4: "Property (T) is inherited by
  quotients: if G1 has Property (T), then so does G1/N for every closed normal
  subgroup N of G1."
  - `deligne-universal-cover-lattice-is-non-rf-kazhdan` gives property (T) for
    the lattice `Gamma~` with `Gamma~/Z ≅ Sp_4(Z)`, so `Gamma = Sp_4(Z)` has (T).
  - Fix a finite Kazhdan pair `(Q, kappa)` and a symmetric generating set
    `S ⊇ Q`.
- **(I3)** Fournier-Facio–Gerasimova–Spaas, arXiv:2307.13155, TeX `HS.tex`, lemma
  `lem:BLTperturb`, citing Becker–Lubotzky Proposition 2.3:
  - The lemma: "Let Γ be a countable group with a fixed finite generating set
    S, π: F_S → Γ, and let σ: Γ → U(n) be a representation of Γ. Then there
    exists a homomorphism τ: F_S → U(n−1) such that (1) ∀ w ∈ ker(π):
    ‖τ(w) − 1‖_2 ≤ 3^{|w|}/√(n−1). (2) The inclusion map ι: C^{n−1} → C^n
    satisfies for all s ∈ S: ‖σ(s^{−1}) ∘ ι ∘ τ(s) − ι‖_2 ≤ 2/√n."
  - FFGS use exactly this lemma for Theorem `thm:T`: an infinite hyperlinear
    (T) group is not locally HS-stable.
- **(I4)** Etingof et al., *Introduction to representation theory*,
  arXiv:0901.0827, TeX `replect.tex`, Theorem `indr` (the Mackey formula):
  "χ(g) = Σ_{σ ∈ H\G : x_σ g x_σ^{−1} ∈ H} χ_V(x_σ g x_σ^{−1})" for
  `χ` the character of `Ind_H^G V`.
- **(I5)** Reduction `Sp_4(Z) -> Sp_4(F_p)` is surjective. The elementary
  symplectic matrices generate `Sp_4(F_p)`; this is Ree's theorem, seen only as
  cited in arXiv:1901.00892, l.1149. Those matrices lift to integral
  elementary symplectic matrices. Secondary source only.

## Proof

**Step 1: a balanced pair of large irreducibles.**
- For a prime `p >= 11` let `red_p : Gamma -> G_p = Sp_4(F_p)` be reduction,
  which is onto by (I5). Let `theta_p^±` be as in part (3) of
  `sp4-fp-regular-principal-series-irreducible`, and put
  `sigma_p^± = Ind theta_p^± ∘ red_p`, of common degree
  `m_p = (p+1)^2 (p^2+1)`.
- By that node, both are irreducible for `G_p`, hence for `Gamma`. They are
  non-isomorphic, since `-I` acts by `+1` on one and `-1` on the other.
- Put `sigma_p = sigma_p^+ ⊕ sigma_p^-` on `C^(k'_p)` with `k'_p = 2 m_p`. By
  Schur's lemma its invariant subspaces are exactly `0`, the two summands and
  everything. So every proper invariant subspace has dimension at most `m_p`.

**Step 2: `sigma_p` has regular limit trace.**
- **Central elements.** `tr(sigma_p(I)) = 1` and
  `tr(sigma_p(-I)) = (m_p - m_p)/k'_p = 0`.
- **Reduction is non-scalar.** Let `g ∉ {±I}`. For all but finitely many `p`,
  `red_p(g)` is not scalar, and the only scalars in `G_p` are `±I`.
- **Character bound.** By (I4) with `H = B_p` and `V = theta` one-dimensional,
  `|chi(x)|` is at most the number of cosets `σ` with `σx = σ`, i.e. the number
  of fixed points of `x` on `G_p/B_p`. The map `gB_p ↦ g·(<e_1> ⊂ <e_1,e_2>)` is
  injective, since `B_p` is that flag's stabilizer. So fixed cosets are at most
  fixed flags `L ⊂ P`, with `L` a line and `P` a Lagrangian plane.
- **Counting fixed flags.**
  - An `x`-invariant line lies in an eigenspace. A non-scalar `x` has
    eigenspaces of dimension at most 3, with dimensions summing to at most 4, so
    there are at most `(p^3-1)/(p-1) + 1 <= 2p^2` invariant lines.
  - Given `L`, the planes `P ⊃ L` correspond to lines of `L^⊥/L`, so there are
    at most `p + 1` of them.
  - Hence `|chi(red_p g)| <= 2p^2 (p+1) <= 4p^3`, and
    `|tr_(m_p)(sigma_p^±(g))| <= 4p^3/m_p <= 4/p -> 0`.
- **Conclusion.** `tr_(k'_p)(sigma_p(g)) -> delta_e(g)` for every `g ∈ Gamma`.

**Step 3: the compressed witness.**
- **Construction.** Apply (I3) to `sigma_p` with `n = k'_p`, obtaining
  `tau_p : F_S -> U(k_p)`, where `k_p = k'_p - 1`. For `g ∈ Gamma` fix a word
  `w_g` with `π(w_g) = g`, and `w_s = s` for `s ∈ S`. Put
  `phi_p(g) = tau_p(w_g)`.
- **(1) Asymptotic.** `phi_p(g) phi_p(h) phi_p(gh)^(-1) = tau_p(w_g w_h w_gh^-1)`,
  and `w_g w_h w_gh^-1 ∈ ker π`. So (I3)(1) gives
  `||phi_p(g)phi_p(h) - phi_p(gh)||_2 <= 3^(L)/sqrt(k_p) -> 0`, where `L` is the
  length of that relator.
- **(2) Regular trace.**
  - By unitary invariance, (I3)(2) says `||ι tau_p(s) - sigma_p(s) ι||_2 <= 2/sqrt(k'_p)`.
    The same bound holds for `s^-1`, after conjugating by `sigma_p(s^-1)` and
    `tau_p(s^-1)`.
  - Telescoping along a word `w` of length `r` gives
    `||ι tau_p(w) - sigma_p(w) ι||_2 <= C r / sqrt(k'_p)`, with `C` absorbing the
    normalization ratio `k'_p/k_p`.
  - Hence `|tr_(k_p)(tau_p(w)) - tr_(k_p)(ι^* sigma_p(w) ι)| <= C r/sqrt(k'_p)`,
    by Cauchy–Schwarz for the normalized trace.
  - With `ξ` a unit vector spanning the orthocomplement of `ι(C^(k_p))`,
    `tr_(k_p)(ι^* sigma_p(w) ι) = (k'_p tr_(k'_p)(sigma_p(w)) - <sigma_p(w) ξ, ξ>)/k_p`.
  - By Step 2 the right-hand side tends to `delta_e(π w)`. So
    `tr(phi_p(g)) -> delta_e(g)`.
- **(3) No rounding.**
  - Suppose, along some subsequence, homomorphisms `rho_p : Gamma -> U(k_p)`
    satisfy `delta_p := max_s ||phi_p(s) - rho_p(s)||_2 -> 0`.
  - On the Hilbert space of operators `C^(k_p) -> C^(k'_p)` with normalized HS
    inner product, `pi_p(g) X = sigma_p(g) X rho_p(g)^-1` is a unitary
    representation.
  - For `s ∈ S`: `||pi_p(s) ι - ι||_2 <= ||sigma_p(s) ι - ι tau_p(s)||_2 + ||tau_p(s) - rho_p(s)||_2 -> 0`,
    while `||ι||_2 = 1`.
  - By (I1), `theta_p := P ι` is invariant and `||ι - theta_p||_2 -> 0`.
    Invariance means `sigma_p(g) theta_p = theta_p rho_p(g)`, so `Im theta_p` is
    `sigma_p`-invariant, of dimension at most `k_p < k'_p`. By Step 1 that
    dimension is at most `m_p = k'_p/2`.
  - With `E` the projection onto `Im theta_p`, `theta_p = E theta_p`, so
    `||ι - theta_p||_2^2 >= ||(1-E) ι||_2^2 = (k_p - tr(E ι ι^*))/k_p >= (k_p - m_p)/k_p -> 1/2`.
  - This contradicts `||ι - theta_p||_2 -> 0`. So `c > 0` exists as claimed.

## Scope

- **Flexible stability.** `phi_p` is a codimension-one corner of the genuine
  `sigma_p`, so the construction does not bear on flexible HS-stability.
- **Pinned trace.** It differs from the unspecified witnesses behind
  `infinite-hyperlinear-kazhdan-group-is-not-hs-stable` only by pinning the trace
  to `delta_e`. That needs two opposite central signs of equal degree, since a
  single irreducible has normalized trace `±1` at `-I`.
