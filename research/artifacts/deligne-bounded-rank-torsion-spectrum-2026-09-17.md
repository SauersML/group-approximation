# Bounded-rank rung: the D2 repair at atom level and where it actually breaks

Lane sw-124 (scale-shifter), 2026-09-17. Node: `deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension`,
built on sw-021's anatomy (`research/artifacts/deligne-bounded-rank-rung-anatomy-2026-09-17.md`, section D2).

**Summary.**
1. **Part I (proposed-established).** D2's failing step, "an almost-invariant finite atomic measure is torsion",
   is **true** once both generators of `SL_2(Z)` are used and defect is counted in atoms. All but
   `C_0 x defect` atoms lie on finite torsion orbits, and each such orbit of order `m` has mass `>= (6/pi^2) m^2`.
   The single-generator orbit segment of D2 has defect of order `d` under the pair.
2. **Part II (dead end, exact step).** A rank-`k` tuple does **not** give an atom-level almost-invariant joint
   spectral measure. Two things fail:
   - **Rank moves every atom.** Let `u = diag(lambda_1..lambda_d)` have simple spectrum and let
     `u' = u (1 + K)` with `K` a generic rank-one perturbation (unitary). Then `u'` has no eigenvalue
     in common with `u`, by the secular equation `sum_j |w_j|^2 / (lambda_j - z) = const` with all
     `w_j != 0`. So `||mu_u - mu_(u')||_1 = 2d`. Rank controls only interlacing: arc counts change by
     `<= rank`, and each single-point multiplicity changes by `<= rank`.
   - **The joint spectrum need not exist.** `rank([b,c] - 1) <= k` does not localize the eigenspaces of
     `b`. Example: `b` is the cyclic shift on `C^(Z/d)` and `c = diag(+1 on [0,d/2), -1 on [d/2,d))`. Then
     `rank(bcb^(-1)c^(-1) - 1) = 2`. In the Fourier eigenbasis of `b`, `c` is the full Cauchy/Hilbert-transform
     matrix `((1 - omega^(i-j))^(-1) X_(ij))` with `X` of rank 2, and no eigenline of `b` is almost preserved.
     Here a rank-2 change of `b` (cutting the cycle) commutes. In general, producing a joint measure needs
     **bounded-rank stability of `Z^2` for unitaries**: a pair within rank `C(k)` of a commuting pair. That is
     open and posted as a `need`. It is necessary but **not sufficient**. Even for a commuting pair, the
     conjugation relators `rho(s) b rho(s)^(-1) = w(b,c)` hold only up to rank `k`. By the first bullet,
     that matches joint spectra only up to interlacing, not atoms.
   - **Consequence.** Part I applies verbatim only to **monomial-type** tuples, where the long-root pair
     is diagonal in a basis that the lifts of `SL_2(Z)` permute up to `O(k)` coordinates. For general
     unitary tuples the right hypothesis is interlacing (Kolmogorov-type) almost-invariance. There,
     near-Lebesgue clouds of non-torsion points are not excluded by Kesten isoperimetry, because
     isoperimetry controls `l^1` level-set boundaries and not discrepancy.
3. **Part III (Deligne cost along `g_M = x_alpha(1)^M`: the exact obstacle).**
   - (LOC) counts `rank(rho(g_M) - I) = d - sum_(lambda^M = 1) mult_u(lambda)`, with `u = rho(x_alpha(1))`.
     So it sees only **exact** `M`-torsion multiplicities.
   - By Part II these are robust per point (`+-k`) but not in total. A rank-`r` modification of `u`
     changes `rank(u^M - I)` by at most `M r`, and by nothing better in general.
   - A spectral bound `rank(rho(g_M) - I) = o(d / N_M)` therefore needs structural torsion multiplicity,
     not approximate torsion. The only mechanism in sight is the Part I torsion theorem, and it requires
     the monomial structure or the `Z^2` stability `need`.
   - **Replacing rank by an `eps`-rank** (singular values `> eps`, subadditive with `eps` adding along
     products) changes the cost to `d <= A_M k + N_M rank_(c/N_M)(u^M - 1)`. This needs
     `|lambda^M - 1| <= c / N_M` for all but `d / (2 N_M)` eigenvalues. By Dirichlet this can be forced
     only with `M <= (N_M / c)^d`, so (LOC) along `g_M` would need the relator area `A_M` to grow like
     `o(log M) = o(d log N_M)` per unit of `d / k`. No word identity with such sublogarithmic area is
     known, and the Steinberg commutator area of `x_alpha(Mt)` grows at least linearly in `t`.
     Status: heuristic barrier, not a theorem.

# Part I. Torsion theorem for almost-invariant integer measures (proof)


## Setting

`Lambda = SL_2(Z)` acts on `T^2 = R^2 / Z^2` by automorphisms. `S = {s_1, s_2}` is a generating pair
(for instance `s_1 = [[0,-1],[1,0]]`, `s_2 = [[1,1],[0,1]]`). A **defect-`K` integer measure** is a
finitely supported `f : T^2 -> Z_(>=0)` with

```text
D(f) := sum_(s in S) || f o s - f ||_1 <= K.
```

## Theorem

There is an absolute constant `C_0` such that every finitely supported `f : T^2 -> Z_(>=0)` can be written as

```text
f = sum_(O finite orbit) c_O 1_O + nu,     c_O in Z_(>=0),   ||nu||_1 <= C_0 D(f).
```

Every finite orbit consists of torsion points. If `c_O >= 1` for an orbit of points of exact order `m`,
then `||f||_1 >= |O| >= (6 / pi^2) m^2`.

## Step 1. Stabilizers

Let `x in T^2` and `L_x = {n in Z^2 : <n, x> in Z}`, a subgroup of `Z^2`.

- **rank `L_x = 2`.** Then `x` is torsion.
- **rank `L_x = 0`.** If `A x = x`, then `(A - 1)x = 0` in `T^2`. The integer rows of `A - 1` lie in
  `L_x = 0`, so `A = 1`. The stabilizer is trivial.
- **rank `L_x = 1`.** `A x = x` forces `A^T` to preserve `L_x`, since `L_(Ax)` is the image of `L_x`
  under `A^(-T)`. So the stabilizer lies in the stabilizer of the rational line `Q L_x`. That is a
  Borel subgroup of `SL_2(Z)`, isomorphic to `{+-1} x Z`, hence amenable.

A non-torsion point has an amenable stabilizer of infinite index, so its orbit is infinite. A torsion point
of order `m` is fixed by the principal congruence subgroup `Gamma(m)`, so its orbit is finite.

## Step 2. Uniform spectral gaps

Let `P = (1 / 2|S|) sum_(s in S) (s + s^(-1))` act on `l^2(Lambda / H)`.

- **(G-inf) Infinite orbits.** `H` is amenable. By Hulanicki–Kesten, `l^2(Lambda/H)` is weakly contained in
  `l^2(Lambda)`. So `||P|| <= ||lambda_Lambda(P)|| =: rho_inf`, and `rho_inf < 1` by Kesten's theorem,
  because `Lambda` is non-amenable.
- **(G-fin) Finite orbits.** `H` contains `Gamma(m)`, so `l^2_0(Lambda/H)` embeds `Lambda`-equivariantly
  in `l^2_0(Lambda / Gamma(m))`. Property (tau) of `SL_2(Z)` with respect to congruence subgroups (Selberg's
  `lambda_1 >= 3/16`, transferred to Schreier graphs by the Brooks–Burger comparison; Lubotzky,
  *Discrete Groups, Expanding Graphs and Invariant Measures*, Ch. 4) gives `||P|_(l^2_0)|| <= rho_tau < 1`
  uniformly in `m`.

Put `rho = max(rho_inf, rho_tau) < 1`.

## Step 3. Isoperimetry for sets

For `F` contained in one orbit `O`, write `b(F) = sum_(s in S) |sF Delta F|`.

For any `phi in l^2(O)`, since `<P phi, phi> = (1/|S|) sum_s Re <s phi, phi>`,

```text
sum_(s in S) ||s phi - phi||_2^2 = 2|S| ( ||phi||^2 - <P phi, phi> ).
```

- **`O` infinite, `F` finite.** Take `phi = 1_F`. Then `b(F) = sum_s ||s 1_F - 1_F||_2^2 >= 2|S|(1 - rho)|F|`.
- **`O` finite.** Take `phi = 1_F - (|F|/|O|) 1_O`, which lies in `l^2_0(O)`. Constants are invariant, so
  `b(F) = sum_s ||s phi - phi||^2 >= 2|S|(1 - rho) ||phi||^2`. Also
  `||phi||^2 = |F| |O \ F| / |O| >= min(|F|, |O \ F|) / 2`, so `b(F) >= |S|(1 - rho) min(|F|, |O \ F|)`.

## Step 4. Coarea

Restrict `f` to one orbit `O` and let `F_t = {f >= t}` for `t >= 1`; the sets decrease in `t`. For integer
`f >= 0` and a bijection `s`, `|f(s y) - f(y)| = #{t : exactly one of y, s y lies in F_t}`. Summing over `y`,

```text
|| f o s - f ||_1 = sum_(t >= 1) |s^(-1) F_t Delta F_t| = sum_(t >= 1) |F_t Delta s F_t|.
```

So `D(f|_O) = sum_t b(F_t)`, and `D(f) = sum_O D(f|_O)`, because each `s` preserves every orbit.

- **`O` infinite.** `||f|_O||_1 = sum_t |F_t| <= sum_t b(F_t) / (2|S|(1 - rho)) = D(f|_O) / (2|S|(1-rho))`.
  Put `c_O = 0`.
- **`O` finite.** Let `c_O = #{t : |F_t| >= |O|/2}`. The sets decrease, so these are exactly `t = 1..c_O`. Then

  ```text
  || f|_O - c_O 1_O ||_1 = sum_(t <= c_O) |O \ F_t| + sum_(t > c_O) |F_t| = sum_t min(|F_t|, |O \ F_t|)
                         <= D(f|_O) / (|S|(1 - rho)).
  ```

  The middle equality holds because `(f - c_O)^+` and `(c_O - f)^+` are counted by the level sets above and
  below `c_O`.

Summing over orbits gives the theorem with `C_0 = 1 / (|S|(1 - rho))`.

**Order bound.** The points of exact order `m` number `m^2 prod_(p | m) (1 - p^(-2)) >= (6/pi^2) m^2`.
An orbit contains points of one exact order only, and `SL_2(Z)` acts transitively on the vectors of exact
order `m` in `(Z/m)^2` (it acts transitively on unimodular rows modulo `m`). So `|O| >= (6/pi^2) m^2`. QED.

## Calibration

- **D2's single-generator example.** The orbit segment `{A^j x : 0 <= j < d}` of a non-periodic `x` has
  defect 2 under `A` alone. Under the pair `S` it has defect of order `d`, as the theorem requires. So the
  failing step of D2 ("almost-invariant atomic measure implies torsion") holds **for two generators**.
- **Amenable control.** For `Z` acting on `T^1` by an irrational rotation, orbit segments have defect 2 and
  mass `d`. The theorem fails there, and the proof fails at Step 2: Kesten gives no gap for an amenable group.
