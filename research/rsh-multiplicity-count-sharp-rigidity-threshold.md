---
rg: 2
id: rsh-multiplicity-count-sharp-rigidity-threshold
kind: claim
title: Tracial eigenvalue rigidity at level ε_0 forces every unital RSH subalgebra to have a block with ε_0 n < √(d+2), and at the threshold dimension the certificate is an n-primary torsion twist
distinct_from:
  hilbert-cube-bauer-strict-comparison-indivisible-unit-exists: that is the open witness node and records the count `d ≳ ε_0² n²` only as a heuristic, and the subquadratic ASH exclusion only by citation; this proves a sharp inequality for every unital RSH subalgebra of any unital algebra, with no ASH hypothesis on the ambient algebra.
  simple-unital-ash-strict-comparison-is-z-stable: that asks for all unital simple ASH algebras with strict comparison; this closes the Bauer case only when arbitrarily small ratios `√(d+2)/n` occur, in subalgebras of an arbitrary algebra.
  bauer-strict-comparison-unit-divides-iff-atomless-element: that turns one element with small atoms into division of the unit; this produces such elements from low-dimensional recursive subhomogeneous subalgebras by general position.
  pauli-tower-sections-are-somewhere-scalar: that proves rigidity at level 1 for one explicit tower by a Stiefel–Whitney computation; this shows the tower sits exactly at the dimension threshold, and that at the threshold only torsion twisted certificates exist.
  simple-algebra-completions-have-no-scalar-points: that bounds the rigidity level of a simple algebra by 1 and by its division capacity; this bounds it by the dimension-to-size ratio of every RSH subalgebra, with no simplicity.
---

**Status: proposed ESTABLISHED** (complete proof in
`research/rsh-multiplicity-count-sharp-rigidity-threshold-proof.md`; not yet refereed).

**Setting.** `B` is a unital recursive subhomogeneous (RSH) algebra with blocks
`(X_j, n_j, ∂X_j, ψ_j)`, `j = 0..J`, each `X_j` compact metrizable with covering dimension
`d_j < ∞`. For a unital C*-algebra `A` and a set `K` of tracial states, `A` is
**`ε_0`-rigid over `K`** if every self-adjoint `h ∈ A` has some `τ ∈ K` whose spectral
distribution `μ_{h,τ}` has an atom of mass `≥ ε_0`. Put `L_k ⊂ Herm_n` for the Hermitian
matrices with an eigenvalue of multiplicity `≥ k`.

**Theorem A (multiplicity general position).** Let `0 < ε ≤ 1` and `k_j = ⌈ε n_j⌉`. If
`d_j ≤ k_j² − 2` for every `j`, then the self-adjoint `h ∈ B` with `h_j(x) ∉ L_{k_j}` for
all `j` and all `x ∈ X_j` are dense in `B_sa`. The count is von Neumann–Wigner: `L_k` is
closed semialgebraic of codimension `k² − 1`.

**Theorem B (rigidity inequality).** If `B ⊆ A` is a unital RSH subalgebra, then for
`ε_B = max_j √(d_j + 2)/n_j ≤ 1` some self-adjoint `h ∈ B` has every atom of every `μ_{h,τ}`,
`τ ∈ T(A)`, of mass `≤ max_j (⌈ε_B n_j⌉ − 1)/n_j < ε_B`. Hence if `A` is `ε_0`-rigid over
any nonempty `K ⊆ T(A)`, then **`ε_0 n_j < √(d_j + 2)` for some block of every unital RSH
subalgebra of `A`** (trivially so when `ε_B > 1`, since `ε_0 ≤ 1`).

**Corollary C (Bauer strict comparison).** Let `A` be unital, simple, separable, exact and
non-elementary, with strict comparison and Bauer `T(A)`. If for every `ε > 0` the algebra `A`
contains a unital RSH subalgebra with `max_j √(d_j+2)/n_j < ε`, then the unit of `A` is
tracially divisible and `A` is pure (via `bauer-strict-comparison-unit-divides-iff-atomless-element`
and `bauer-strict-comparison-pure-iff-divisible-unit`). If moreover `A` is a simple ASH limit of
RSH algebras over finite-dimensional spaces with these ratios tending to `0`, then `A` is
`Z`-stable (Winter, via `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`). This reproduces the
Bauer case of the subquadratic ASH theorem cited on the witness node, and extends the exclusion to
arbitrary ambient algebras.

**Theorem D (the threshold is torsion).** Let `X` be a finite CW complex of dimension
`≤ k² − 1`, `2 ≤ k ≤ n`, `P` a principal `PU(n)`-bundle and `A_P` its algebra of sections.
1. `U_k = Herm_n \ L_k` is `(k²−3)`-connected with `π_{k²−2}(U_k) ≅ Z^{n−k+1}` (one class per
   position `i` of a `k`-fold coincidence `λ_{i+1} = … = λ_{i+k}`).
2. Some self-adjoint `h ∈ A_P` misses `L_k` everywhere iff `f_P^* θ_k = 0`, where
   `θ_k ∈ H^{k²−1}(BPU(n); Z^{n−k+1})` is the primary obstruction of `EPU(n) ×_{PU(n)} U_k`.
3. `θ_k` restricts to `0` on `BT` and on `BU(n)`. So `θ_k` is torsion, and its `p`-primary
   part vanishes for `p ∤ n`. In particular every `End(E)` block (untwisted Dixmier–Douady
   class) over a complex of dimension `≤ k² − 1` contains a self-adjoint element with all
   multiplicities `≤ k − 1`.
4. **Sharpness.**
   - The `PU(2) = SO(3)`-bundle with `w_2 ≠ 0` over the Moore space `S² ∪_2 e³` has
     `θ_2 = e(ad P) = β w_2 ≠ 0`. Every self-adjoint section of this `M_2`-bundle is
     somewhere scalar, at `d = 3 = k² − 1`.
   - The Pauli tower at `n = 2^r` is rigid at level `1` over a base of dimension `4^r − 1 = n² − 1`.
   - Above the threshold, untwisted certificates exist. The `SU(2)` instanton bundle `E` over `S⁴`
     (`d = 4 = k²`) has every self-adjoint section of `End(E)` somewhere scalar, because a nowhere
     scalar one splits `E = L ⊕ L^{−1}` and forces `c_2(E) = −c_1(L)² = 0`.
5. **Sharpness at every level `1/t`.** If `P` is a `PU(k)`-bundle over a complex of dimension
   `≤ k² − 1` with `e(ad_0 P) ≠ 0`, then for every `t ≥ 1` every self-adjoint element of
   `A_P ⊗ M_t` has an eigenvalue of multiplicity `≥ k` somewhere.
   - The block-diagonal equivariant map `U_k(k) → U_k(kt)`, `h ↦ ⊕_j (ĥ + 3j)`, sends the
     generator to a unimodular vector of `Z^{kt−k+1}`. So `θ_k(P ⊗ 1_t) = f_* e(ad_0 P) ≠ 0`.
   - Applied to the Pauli tower (`k = 2^r`, `d = 4^r − 1`), `B_{0,r} ⊗ M_t` is `1/t`-rigid. Theorem B
     permits exactly levels `< √(k²+1)/(kt)`, and the largest multiple of `1/n` below that is `1/t`.
     So Theorem B is attained at every level `1/t`, at block sizes `n = 2^r t → ∞`.

**What this kills.** Take any design for `hilbert-cube-bauer-strict-comparison-indivisible-unit-exists`
(or any strict-comparison Bauer counterexample to STW XXVII / Toms–Winter) with rigidity level
`ε_0`.
- Its rigidity certificate cannot live in any unital RSH subalgebra of dimension ratio
  `max_j √(d_j+2)/n_j ≤ ε_0`. That includes dimension drop algebras, `C(Y) ⊗ M_n` with
  `dim Y ≤ ε_0² n² − 2`, and every ASH stage of subquadratic growth.
- In the borderline regime `d ≤ k² − 1`, homogeneous blocks certify rigidity only through an
  `n`-primary torsion class of a genuinely projective bundle.
- In homogeneous blocks, rational (Chern-class, Villadsen-type) certificates first appear strictly above the threshold.
- The first failing step of any linear-growth design (`d = O(n)`, e.g. rank-gap twisted attaching
  maps) is the general-position perturbation of Theorem A inside one finite stage.

**Not covered.** Rigidity with `ε_0 n_j < √(d_j+2)` at infinitely many blocks, i.e. the quadratic
regime itself, remains open: D.5 gives threshold blocks at every level `1/t`, but these algebras are not simple, and whether mixing connecting maps can preserve the torsion certificate is not addressed.
