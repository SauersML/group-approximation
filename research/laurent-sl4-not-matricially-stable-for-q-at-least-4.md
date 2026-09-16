---
rg: 2
id: laurent-sl4-not-matricially-stable-for-q-at-least-4
kind: claim
title: For q at least 4, SL_4(F_q[t,t^-1]) is not point-norm matricially stable
distinct_from:
  laurent-sl4-matricially-stable: that asserts point-norm matricial stability of the Laurent lattice for a prime power q; this is its negation only for q >= 4, where F_q^* has an element a with a^2 != 1, and it says nothing about q = 2, 3.
  sl4z-matricially-stable: that is the stability question for SL_4(Z), where the obstruction candidates are Voiculescu pairs in unipotent subgroups; this is a refutation for the positive-characteristic Laurent lattice through tori in centralizers of semisimple torsion.
artifacts:
  - research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md
---

**OPEN.** Let `q ≥ 4` be a prime power and `Λ = SL_4(F_q[t,t^{-1}])`. There is an operator-norm asymptotic
homomorphism `φ_n : Λ → U(k_n)` such that no homomorphisms `π_n : Λ → U(k_n)` satisfy `‖φ_n(h) − π_n(h)‖ → 0` for
every `h ∈ Λ`. That is, `Λ` is not point-norm matricially stable.

**Relation to `laurent-sl4-matricially-stable`.** That claim leaves `q` a free prime power, and its consumer
`subshift-el-reduced-not-mf-from-laurent-sl4-stability` uses the `q` of the subshift ring. This claim is **not** listed
in that claim's `refuted_by`. It refutes the `q ≥ 4` instances only, and how the target is quantified over `q` is left
to whoever maintains it. The weaker crux `laurent-sl4-corona-representations-have-block-sl2-norm-four` is not
affected, since instability does not refute it.

**Where an obstruction must live.** The identity-sector obstructions are void for `Λ`.
- `H_2(Λ;Z)` is finite, so the Exel–Loring two-homology invariants vanish (Attempts of `laurent-sl4-matricially-stable`).
- `H^{2k}(Λ;Q)` can be nonzero only for `k = 3`, and there is a sketch that it is zero (same Attempts).

The nonzero class used here lives in a torsion centralizer (artifact §3).
- Choose `a ∈ F_q^*` with `a² ≠ 1` and put `g = diag(a, a^{-1}, 1, 1)`.
- Then `Z_Λ(g) = {diag(x, y, h) : x, y ∈ A^*, h ∈ GL_2(A), xy·det h = 1}` with `A = F_q[t,t^{-1}]`.
- `s_1 = diag(t, 1, t^{-1}, 1)` and `s_2 = diag(1, t, 1, t^{-1})` span a torus whose class survives in
  `H_2(Z_Λ(g);Q)`, because `diag(x, y, h) ↦ (deg x, deg y)` retracts it onto `Z^2`.

## Attempts

- **Reduction to the delocalized Dadarlat statement.** Route `laurent-sl4-instability-from-delocalized-dadarlat`
  derives this claim from `weak-matricial-stability-kills-centralizer-even-cohomology` (OPEN) and the established
  `dadarlat-matricial-stability-obstruction`. The gap is that OPEN claim, specifically its step (P3) (artifact §5).
- **No explicit asymptotic homomorphism found.** A direct refutation needs an asymptotic homomorphism with nonzero
  delocalized Bott invariant `β_ω(g; s_1, s_2)` (artifact §1). `Λ` has property (T) (recalled: it is a lattice in
  `SL_4(F_q((t))) × SL_4(F_q((t^{-1})))`), so the obvious source is induction from finite-index subgroups. Such models
  die in two ways.
  - Induction from a normal finite-index `N` with `⟨g⟩ ∩ N = 1` gives `β_ω` independent of `ω`, hence `0` by Weyl
    antisymmetry (artifact Lemma 4.1, Corollary 4.2).
  - If `g ∈ N`, then `N` is again a finite-index lattice with property (T) and the problem is unchanged.
- **Weyl antisymmetry fixes the sector (artifact Lemma 3.3).** The permutation matrix of `(12)(34)` lies in `Λ`,
  inverts `g` and swaps `s_1, s_2`. So `β_ω = −β_ω̄` for every asymptotic homomorphism. Only nonreal `ω` can carry the
  invariant, and that needs `ord(g) ≥ 3`. This is where `q ≥ 4` enters.
  - For `q = 3` and `g = diag(−1,−1,1,1)`, the same matrix centralizes `g` and the torus class is zero in
    `H_2(Z_Λ(g);Q)`.
  - `q = 2, 3` are not decided (artifact Remark 3.5).
