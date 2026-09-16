---
rg: 2
id: laurent-sl4-matricially-stable
kind: claim
title: SL_4(F_q[t,t^-1]) is point-norm matricially stable
distinct_from:
  sl4z-matricially-stable: that is the same question for SL_4(Z), whose unipotent subgroups are free abelian and carry Voiculescu's almost-commuting pairs; this is the positive-characteristic Laurent lattice inside every G_X, whose root subgroups are elementary abelian p-groups and whose rational cohomology vanishes below degree 6.
  sl3-laurent-f2-is-flexibly-hs-stable: that asks flexible Hilbert-Schmidt stability of SL_3 over F_2[t,1/t], which bears on hyperlinearity; this asks same-dimension operator-norm stability of SL_4, which bears on MF of reduced algebras.
artifacts:
  - research/artifacts/sk-matricial-stability-laurent-sl4-2026-09-13.md
---

**OPEN.** Let `q` be a prime power and `Λ = SL_4(F_q[t,t^{-1}])`. Every operator-norm asymptotic homomorphism
`φ_n : Λ → U(k_n)` (`‖φ_n(gh) − φ_n(g)φ_n(h)‖ → 0` for all `g, h`) admits homomorphisms `π_n : Λ → U(k_n)` with
`‖φ_n(g) − π_n(g)‖ → 0` for each `g`.

**What it decides.**
- **A positive answer** makes `C*_r(Γ)` non-MF for every countable `Γ ⊇ Λ`
  (`laurent-sl4-stability-makes-overgroups-reduced-non-mf`). In particular `C*_r(G_X)` would be non-MF for every infinite
  minimal subshift `X` (route `subshift-el-reduced-not-mf-from-laurent-sl4-stability`).
- **A negative answer is forced** by any MF embedding of the reduced algebra of any group containing `Λ`.

**Facts about `Λ` that bear on it.**
- **Presentation.** `Λ` is finitely presented, of type `F_5`: the Rank Theorem quoted in
  `laurent-s-arithmetic-finiteness-lengths-citation`, with local ranks `3 + 3 = 6`.
- **Perfect.** `Λ = E_4(A)` is its own commutator subgroup (`bms-congruence-kernel-trivial-not-totally-imaginary`).
- **Rational cohomology.** By Harder (`harder-function-field-s-arithmetic-cohomology-vanishing`, rank `r = 3`,
  `|S| = 2`), `H^ν(Λ;Q) = 0` for `ν ≠ 0, 6`. Since `H_2(Λ;Z)` is finitely generated, it is finite.
- **Finite-dimensional representations.** All are congruence, with block-`SL_2` fixed vectors
  (`laurent-sl-n-representations-have-sl2-invariant-vectors`).

## Attempts

- **Asymptotically projective models round.** This is an instance of an established claim. `Λ` is finitely generated
  with `H_1 = 0` and `H_2(Λ;Z)` finite, so `finite-multiplier-projective-models-round-strictly` applies: every model
  `α_n(g)α_n(h) = c_n(g,h)α_n(gh)` with `c_n → 1` pointwise is `o(1)`-close to genuine representations. A non-roundable
  asymptotic homomorphism must have non-scalar defects.
- **Dadarlat's cohomological obstruction can only live in degree 6.** Dadarlat's Theorem 1.1
  (`dadarlat-matricial-stability-obstruction`) refutes stability of an MF group with a gamma-element once
  `H^{2k}(G;Q) ≠ 0` for some `k ≥ 1`. `Λ` is residually finite and linear, so those hypotheses are available (recalled,
  not re-checked for linear groups in positive characteristic). By Harder only `k = 3` can occur.
  - **Sketch, not established.** The action on the `t`-adic building has one chamber as quotient, so
    `H^6(Λ;Q) = coker(⊕_panels H^3(P_i;Q) → H^3(I;Q))` for the Iwahori subgroup `I ≤ SL_4(F_q[t])`. By Harder this is
    the multiplicity of Steinberg ⊗ Steinberg at level one in the discrete spectrum.
  - A cuspidal contribution corresponds, through Lafforgue, to a rank-4 tame local system on `G_m` with maximally unipotent
    monodromy, which cannot be geometrically semisimple. So the obstruction is heuristically void. Not source-checked.
- **Two-homology invariants are void.** Dadarlat's quasi-representation invariants (`exel-loring-relative-quasirep-invariant`)
  are homomorphisms on `H_2(Λ;Z)` with values in `Z`, and `H_2(Λ;Z)` is finite. So Bott-type winding of the almost
  commuting torus pair `diag(t,t^{-1},1,1)`, `diag(1,1,t,t^{-1})` cannot obstruct. That the invariant restricts to the
  Bott index on commuting pairs is recalled, not read.
- **Uniform (Ulam) stability does not apply.** Theorems of Glebsky–Lubotzky–Monod–Rangarajan type control
  almost-representations with uniformly small defect. Asymptotic homomorphisms have only pointwise defect
  (`corona-defect-is-not-uniform`).
- **Torsion unipotents remove the `SL_4(Z)` obstruction, and the difficulty moves to gluing.**
  - In `SL_4(Z)` the unipotent `Z^2` carries Voiculescu pairs. Here root subgroups are elementary abelian `p`-groups, so
    every finitely generated subgroup of them is finite, and almost-representations of finite groups are uniformly near
    genuine ones.
  - `Λ` acts on the product of two Bruhat–Tits buildings with finite cell stabilizers and non-compact quotient (a chamber
    times a Soulé sector). A correction must glue finite-group corrections coherently across infinitely many cells, and
    the pointwise defect gives no uniformity deep in the sector.
- **The same wall as `SL_4(Z)`.** Stability implies the robust statement that every corona representation of `Λ` gives
  the block-`SL_2` Laplacian norm 4.
  - In a unitary representation, the column unipotent `A^3` has spectrum in the compact dual group of `A^3`, where every
    character has order `p`.
  - Characters factoring through `A/J` have finite `SL_3(A)`-orbits, and Magee–de la Salle averaging gives norm 4 there.
  - Generic characters have infinite orbits, and an MF embedding of `C*_r(Λ)` has Haar spectrum.
  - So the question reduces to the full-spectrum case, exactly as in `sl4z-corona-representations-have-block-sl2-norm-four`.
  - The analogue of `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full` for `Λ` is expected but not written out.
- **The analogue is now written out (sk-mf-laurent, 2026-09-14, unreviewed).**
  - `laurent-unipotent-spectra-are-finite-or-full`: every closed `E_3(A)`-invariant subset of `Â^3` is finite (bounded
    level) or all of `Â^3`. It is proved by a window-density argument, with no dynamics on tori. So a representation with
    non-full column unipotent spectrum factors through `SL_4(A/J)`.
  - `laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum`: such representations have block-`SL_2` norm 4.
  - The weaker crux `laurent-sl4-corona-representations-have-block-sl2-norm-four` (implied by this claim, and implying
    non-MF of `C*_r(G_X)`) is therefore equivalent to its full-spectrum case. Every MF embedding lies in that case.
- **Rational cohomology, purity step made precise (sketch, not established; artifact
  `research/artifacts/sk-mf-laurent-2026-09-14-part1.md` §6).**
  - A cuspidal `St_0 ⊗ St_∞` form would give, by Lafforgue, a pure lisse sheaf on `G_m`, tame at `0` and `∞`, with
    unipotent inertia `N ≠ 0` at `0`.
  - Pure sheaves are geometrically semisimple (Deligne, Weil II 3.4.1(iii)). A semisimple representation of the abelian
    tame geometric `π_1(G_m)` has semisimple inertia, so `N = 0`. Contradiction.
  - Residual representations of `GL_4` (Mœglin–Waldspurger) have non-generic local components, never Steinberg.
  - So `H^6(Λ;Q) = 0`: `Λ` is `Q`-acyclic and Dadarlat's even-cohomology obstruction is void. Imports not read at source.
- **Delocalized sectors are not void; reduction of the negation for `q ≥ 4` (swarm, 2026-09-16; artifact
  `research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md`).**
  - The two bullets above concern the identity sector only: `H_2(Λ;Z)` and `H^*(Λ;Q)`. Centralizers of torsion can
    carry even rational cohomology. For `q ≥ 4`, `a ∈ F_q^*` with `a² ≠ 1` and `g = diag(a, a^{-1}, 1, 1)`, the torus
    `s_1 = diag(t,1,t^{-1},1)`, `s_2 = diag(1,t,1,t^{-1})` gives `H^2(Z_Λ(g);Q) ≠ 0` via the retraction
    `diag(x,y,h) ↦ (deg x, deg y)`.
  - The delocalized Bott invariant `β_ω(g; s_1, s_2)` (Bott index of the compressions of `φ(s_1), φ(s_2)` to the
    `ω`-spectral projection of `φ(g)`) vanishes on representations and survives `o(1)` perturbation. So a nonzero
    value refutes stability. The toy group `(Z^2 × Z/3) ⋊ Z/2` has vanishing even rational cohomology but a model with
    `β_ω = ±1`, so the sector phenomenon is strictly beyond Dadarlat's theorems.
  - Reduction: `laurent-sl4-not-matricially-stable-for-q-at-least-4` (OPEN) follows by route
    `laurent-sl4-instability-from-delocalized-dadarlat` from the OPEN delocalized form of Dadarlat's Corollary 1.3,
    `weak-matricial-stability-kills-centralizer-even-cohomology`. That claim dies at the equivariant realization step
    (its step P3).
  - No explicit refuting model was found. `β_ω = −β_ω̄` by Weyl antisymmetry, and models induced from normal
    finite-index subgroups avoiding `⟨g⟩` have `β_ω = 0` (artifact Lemmas 3.3, 4.1).
  - `q = 2, 3` are not decided: `F_q^*` has no `a` with `a² ≠ 1`, and for `q = 3`, `g = diag(−1,−1,1,1)` the torus
    class is zero.
  - `refuted_by` is not wired, because the negation is OPEN and it covers only `q ≥ 4` while `q` here is free.
