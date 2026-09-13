# Transcendence degree one under the determinant conjecture, and the remaining crux

Lane `ex-atiyah-torsion-free`, 2026-09-13. Continues `research/artifacts/atiyah-one-variable-base-change-2026-09-12.md` (Theorem 3 and Sections 1-7 there). Supports `atiyah-base-change-in-transcendence-degree-one-under-det` and the open claim `determinant-conjecture-gives-full-atiyah-base-change`.

## 8. Addendum: every coefficient field of transcendence degree one

**Theorem 4.** Let `G` be as in Theorem 3, and let `F ⊂ C` be a field with
`trdeg_(Qbar) F <= 1`. Then every matrix over `F[G]` has integral kernel
dimension. This dimension is invariant under automorphisms of `C` fixing `Qbar`.

**Setting.**
* We may take `F` finitely generated, `F = Qbar(C)` for an irreducible smooth
  affine curve `C` over `Qbar`, embedded through a transcendental point
  `P_0 in C(C)`.
* Clearing denominators by a regular function nonzero at `P_0` changes no
  kernel. So it suffices to treat a family `M` over `Qbar[C][G]` evaluated at
  points `P` of `C`, and to write `k(P) = dim ker M(P)`.
* Choose a finite map `x: C -> A^1` (Noether normalization). `Qbar[C]` is then
  free over `Qbar[x]`, of rank `e`.

**Step 1: fibre sums are constant.**
* Restriction of scalars along `Qbar[x] ⊂ Qbar[C]` gives a family `rho(M)` over
  `Qbar[G][x]`.
* Over an unramified value `z`, evaluating a basis at the `e` points of the fibre
  gives an invertible scalar matrix. It conjugates `rho(M)(z)` to
  `(+)_(x(P) = z) M(P)`, so `dim ker rho(M)(z) = sum_(x(P) = z) k(P)`.
* By Theorem 3, and the finiteness of algebraic jumps, this sum equals a constant
  `K` for every `z` outside a finite set `Z_0` of algebraic numbers (ramified or
  jump values).

**Step 2: k is continuous on `C° = C \ x^-1(Z_0)`.**
* **Upper semicontinuity.** `k` is upper semicontinuous by Lemma 4 of the
  Liouville artifact, since `M(P)` depends norm-continuously on `P`.
* **Lower semicontinuity.** Let `P in C°` lie over `z`, with fibre
  `P = P_1, P_2, ..., P_e`. For `P'` near `P`, the fibre of `x(P')` consists of
  points `P'_i` near `P_i`, with `P'_1 = P'`. By upper semicontinuity at `P_2..P_e`,

  ```text
  k(P') = K - sum_(i >= 2) k(P'_i)  >=  K - sum_(i >= 2) (k(P_i) + eps)  =  k(P) - (e-1) eps.
  ```

**Step 3: constancy.**
* At algebraic points of `C°`, `k` is an integer by Strong Atiyah over `Qbar`.
  Algebraic points are dense in `C°`, so the continuous `k` is integer-valued.
  Hence it is locally constant.
* `C°` is an irreducible curve minus finitely many points, hence connected. So
  `k` is a constant integer on `C°`.
* Every transcendental point lies in `C°`, so the value at `P_0` is that integer,
  the same for every transcendental point of `C`.
* An automorphism `sigma` of `C` fixing `Qbar` sends `P_0` to another
  transcendental point of `C`. That gives the invariance. ∎

**Corollary 5 (two further Jaikin-Zapirain--Lopez-Alvarez conjectures over
`Qbar`).** Under the hypotheses of Theorem 3:
1. **Strong algebraic eigenvalue conjecture over `Qbar`.** Every eigenvalue of
   every square matrix over `D = D_(Qbar[G])` is algebraic.
   - Let `C` be over `D` with `dim ker(z - C) > 0` and `z` transcendental.
   - Using linear representations `C = U B^-1 V` and the Schur complement, as in
     Section 2 of the countable-exceptions artifact, the family
     `[[B, V], [U, x I]]` over `Qbar[G][x]` jumps at `z`. So `z in E_G`, which is
     empty.
2. **Center conjecture over `Qbar`.** `D ∩ C = Qbar`. A transcendental `z = d in D`
   is an eigenvalue of the `1 x 1` matrix `d`.

These are two of the four conjectures of arXiv:1810.12135v4, p. 3, stated there
for subfields closed under complex conjugation. Part 3 of Theorem 3 is the
independence conjecture in the one-transcendental case.

## 9. The remaining crux: transcendence degree at least two

Under the determinant conjecture, Strong Atiyah over `C` is still missing for
coefficient fields of transcendence degree at least 2. This is the open claim
`determinant-conjecture-gives-full-atiyah-base-change`. The attempts, and where
each stops:

* **Kronecker product of companion pencils.** It gives
  `Delta(X) = |a_1|^(N d_2) |a_2|^(N d_1) prod_(j,k) Delta(M(alpha_j, beta_k))`.
  The upper bound involves `prod_(j,k) dist((alpha_j, beta_k), z)^kappa`, which has
  no product formula in the values `p_1(z_1), p_2(z_2)`. Only the nearest block
  gains, while the loss is `N (d_2 log M(p_1) + d_1 log M(p_2))`.
* **u-resultants and Chow forms.** In `s` variables Minkowski's gain grows like
  `n^s log H` and the arithmetic Bezout loss like `N s n^(s-1) log H`, so the
  exponents would close. The gap is the needed bound on
  `prod_(zeta in V) ||zeta - z||` by polynomial values. It fails without
  transversality control, which is the elimination machinery of Nesterenko and
  Philippon. Not attempted.
* **Rational functions of one coordinate.** Approximate `z_2` by `r(z_1)` and
  restrict to the curve `x_2 = r(x_1)`. The Lipschitz constant of `r` enters for
  each root, and balancing the degrees does not close.
* **Continuity along subvarieties.** Section 8 needs a finite map to a base where
  fibre sums are known to be constant. A point of transcendence degree 2 lies on
  no curve defined over `Qbar`, so there is no such base.
* **Central variables.** Theorem 3 for `G x Z` gives
  `integral_T (k(z_1, omega) - g_0) d omega = 0` with a nonnegative integrand. So
  the excess vanishes for almost every `omega`, not pointwise.

If this claim is proved, `SA(E)` together with `Det(E)` for the master host
implies `strong-atiyah-torsion-free`, through
`algebraic-atiyah-and-determinant-one-group-tester`. That route is
`strong-atiyah-torsion-free-via-master-host-determinant`.
