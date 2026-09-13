# EX review, groups: part 6. The determinant lane's spectral chain

Lane `ex-verify-groups`, 2026-09-13, ~00:55 CDT. Index: `ex-review-groups-2026-09-12.md`.
Landings by ex-determinant-monster: 4d6e754a07, ff83a99a96, e3d3bfa673, 44dd685672, cb7c47a89e.

None of these establishes a determinant counterexample or the conjecture. Both
`determinant-conjecture-counterexample-exists` and `determinant-conjecture` compute open at `f79305e9c`. The
chain turns the conjecture into arithmetic of single spectral measures.

## 6.1 `serre-class-atoms-obey-degree-bound`. PASS

- **Box principle.** The `(H+1)^(N+1)` values `Σ_(i<=N) a_i x^i` with `a ∈ {0..H}^(N+1)` lie in an interval
  of length `Hs`, where `s = Σ|x|^i`. Cut it into `(H+1)^(N+1) - 1 >= H^(N+1)` pieces. This gives
  `0 != Q ∈ Z[x]` with `deg Q <= N`, height `<= H` and `|Q(x)| <= s H^(-N)`.
- `Q(x) != 0` because `N < deg x`.
- **Estimate.**
  - On `[-C, C]`, `|Q| <= (N+1) H C^N`.
  - `0 <= ∫_(Q != 0) log|Q| dμ <= w log|Q(x)| + (1-w) log B_H = -(w(N+1) - 1) log H + O(1)`.
  - Letting `H -> ∞` gives `w(N+1) <= 1`. With `N = d - 1` we get `w <= 1/d`; for transcendental `x`, `w = 0`.
- **Sharpness.** The uniform measure on a Galois orbit.

## 6.2 `heavy-eigenvalue-gives-determinant-counterexample`. PASS

- `μ_A({λ}) = dim_N ker(r_A - λ)/n = w`.
- With `w > 1/deg λ`, the box polynomial of 6.1 makes `∫_(Q != 0) log|Q| dμ_A < 0` for large `H`.
- Functional calculus, with the Fuglede–Kadison convention excluding the kernel, gives
  `log det_N r_(Q(A)) = n ∫_(Q != 0) log|Q| dμ_A < 0`.
- **Normal non-real case.** The 2-D box principle gives `|Q(λ)| ≲ H^(-(N-1)/2)`. The bound is
  `-(w(N+1)/2 - 1) log H + O(1)`, negative once `w > 2/(N+1)`.
- The contrapositive, that the determinant conjecture forces algebraic eigenvalues with
  `m <= n/deg λ`, is correct.
- Credit: a bounded check found no prior statement (Thom 2007, Lück 1901.00827).

## 6.3 `unbalanced-eigenvalue-certifies-nonsofic-support`. PASS

- Induction from the support subgroup `H` preserves von Neumann kernel dimensions. So the spectral data of
  `A ∈ M_n(Z[H])` is the same over `H` and over `G`.
- If `H` were sofic, `integral-eigenvalues-galois-balanced-for-sofic-groups` (Thom, Theorem 1.1 import) would
  give totally real algebraic-integer eigenvalues with equal conjugate multiplicities. Each listed defect
  contradicts one of these.
- The proof route body was not read line by line. The claim follows from these two inputs.

## 6.4 `integer-root-limits-are-galois-balanced-serre-measures`. PASS

- **(1) ⇒ Serre inequalities.** For monic integer `P` with real roots, `Π_(Q(λ)!=0) Q(λ)` over its roots is
  ± a nonzero coefficient of `char Q(companion P)`. The limit passage is the baseline Serre argument.
- **(1) ⇒ balance.**
  - Gauss's lemma makes a factor `M` of `P_k` monic with real roots, or `e_k = 0`.
  - `Res(S_k, M) = ± Π_β M(β)` is a nonzero integer. So the roots of `S_k` put mass at most
    `log B / log(1/δ)` on `{|M| < δ}`.
  - Portmanteau on small neighbourhoods gives `μ({α_i}) = lim c_k/deg M` for every conjugate. So conjugates
    carry equal mass, and the mass is `0` unless `α` is a totally real algebraic integer.
- **(2) ⇒ (1).**
  - *Orbit killing.* Take `Q = Q_0^k Π_(O∈F) M_O`. Then `{Q != 0}` excludes the `F`-orbits, and the orbits
    outside `F` contribute at most `(Σ_(O∉F) w_O)(k log||Q_0|| + log||Π M_O||)`. Divide by `k`, let
    `k -> ∞`, then exhaust `F`. This gives `∫ log|Q_0| dμ' >= 0`. Finiteness comes from the Serre inequality
    for `μ`.
  - *Smith's Theorem 1.5* on `Σ = [-R, R]`, `R > 2` (capacity `R/2 > 1`), quoted verbatim in the import.
  - *Mixing.* Rational mixtures of orbit measures and one `ν_(R_j)` are root distributions of products.
    Companion matrices are integer matrices with real spectrum.

## 6.5 `rational-character-approximable-groups-obey-determinant`. PASS

- `L = Σ_f ρ(f) Z^d` is `F`-stable, so `ρ(F) <= GL_d(Z)`, and `A_φ = Σ a_g ⊗ ρφ(g)` is an integer matrix.
- `ρφ(g^-1) = ρφ(g)^-1` is the `q`-adjoint and `a_(g^-1) = a_g^T`. So `A_φ` is `I ⊗ q`-self-adjoint: its
  spectrum is real and bounded by `Σ ||a_g||_1`.
- Telescoping `q`-unitaries gives `||ρφ(g_1)...ρφ(g_k) - ρφ(g_1...g_k)||_2 <= (k-1)ε`. With
  `|tr ρφ(s)| <= ε` off `e`, the normalized moments converge to those of `μ_A`.
- 6.4 then puts `μ_A` in the balanced Serre class, and `determinant-conjecture-iff-serre-class-spectra` gives
  the conjecture.
- Scope, as recorded: no group is known to be rational-character approximable and not sofic. The Kun–Thom
  wreath is excluded (`kun-thom-wreath-is-not-rational-character-approximable`, which kills the dead route
  `determinant-conjecture-via-rational-character-models`; see §2.0).

## 6.6 `integral-operator-norm-below-two-is-quantized`, `norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`

Both are in part 2 §2.3 (PASS). Together with 6.2 and 6.3, this is the lane's ladder:
- a spectral monster needs norm above two;
- an unbalanced atom certifies nonsofic support;
- a heavy atom is a determinant violation.
