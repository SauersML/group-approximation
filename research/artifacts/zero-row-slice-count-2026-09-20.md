# Zero-row slice count: inputs controlled by null-homotopic outputs are outnumbered by them

Agent: swarm-0917-w21-w21-gs-pull, 2026-09-20. Target:
`local-rectangular-small-fibre-maps-lose-proportional-rank` (LRSF), family reframing.

## 0. Statement

Work at the level of real coordinates. `T = R/Z` with the metric `||s - t||` (distance to `Z`).

**Setting.** `n, N >= 1`, `g: T^n -> T^N` continuous. The input classes `pi_1, ..., pi_n`
generate `H^1(T^n; Z)`, and `x_1, ..., x_N` generate `H^1(T^N; Z)`. Call an output coordinate `j`
a **zero row** if `g^* x_j = 0`, i.e. `g_j` is null-homotopic. `Z_0` is the set of zero rows.

**Control.** Every input `i` has a set `C_i ⊆ {1..N}` and `eta > 0` such that

> (C) `|g(u)_j - g(u')_j| < eta` for all `j in C_i` implies `||u_i - u'_i|| < 1/16`.

Let `B_0 = {i : C_i ⊆ Z_0}` (inputs controlled only by zero rows) and `P_0 = ∪_(i in B_0) C_i`.

**Theorem Z.** If `|C_i| <= K` for every `i in B_0`, with `K >= 2`, then

    |B_0| <= c_K |P_0|,   c_K = 1 / max_(0<p<=1) (1-p)^(K-2) (1 + (K-1) p).

The maximum is at `p = 1/(K-1)^2`. So:
- `c_2 = 1/2`;
- `c_3 = 8/9`;
- `c_4 = 243/256`;
- in general `c_K = 1 - 1/(2(K-1)^2) + O(K^-3) < 1`.

No locality hypothesis is used. Outputs may depend on all inputs.

**Torus sites, dimension `d`.** Suppose `g: (T^d)^I -> (T^d)^J` satisfies (C) of LRSF: sup-closeness
at the sites of `C_i` controls site `i`. Then each of the `d` coordinates of site `i` is controlled, in the
sense above, by the `d|C_i|` real coordinates of the sites in `C_i`. So Theorem Z applies with `K`
replaced by `dK`.

**Corollary (null-homotopic maps).** If `g^* = 0` on `H^1` and every site is controlled by at most `K`
sites, then `d|I| <= c_(dK) d|J|`. So `|J| - |I| >= (1/c_(dK) - 1)|I|`. This is the linear form of LRSF,
`rank g^* = 0 >= d|I| - C d(|J| - |I|)`, with `C = c_(dK)/(1 - c_(dK))`, for every `K` and `d` and
without (L).

## 1. Lemma N (coarse inverses)

**Lemma N.** For each input `i` there are an open `U_i ⊆ T^(C_i)` containing `Y_i = g_(C_i)(T^n)` and a
continuous `psi_i: U_i -> T` with `psi_i o g_(C_i) ≃ pi_i` (the coordinate map `u -> u_i`).

*Proof.* This is the partition-of-unity gluing used in the two-output case (w19, branch
`w19-gs-break`, artifact Section 2). It is reproduced here so that this note is self-contained.
1. Cover the compact `Y_i` by finitely many open sup-balls `B_alpha` of radius `eta/2` centred at
   `y_alpha in Y_i`, and put `U_i = ∪ B_alpha`. Pick `u^alpha` with `g_(C_i)(u^alpha) = y_alpha` and set
   `p_alpha = u^alpha_i`.
2. If `y in B_alpha ∩ B_beta`, then `y_alpha` and `y_beta` are `eta`-close on `C_i`, so
   `||p_alpha - p_beta|| < 1/16` by (C).
3. Take a partition of unity `lambda_alpha` subordinate to `B_alpha`. For `y in U_i` pick `alpha_0` with
   `y in B_(alpha_0)` and put `psi_i(y) = p_(alpha_0) + sum lambda_alpha(y) delta(p_(alpha_0), p_alpha)`.
   - Here `delta(p, q)` is the representative in `(-1/2, 1/2)` of `q - p`.
   - Every displacement is `< 1/16`, so the value is independent of `alpha_0` and continuous.
4. For `u in T^n` and `y = g_(C_i)(u) in B_alpha`, (C) gives `||u_i - p_alpha|| < 1/16`. So
   `psi_i(g_(C_i)(u)) = u_i + epsilon(u)` with `epsilon` continuous and `|epsilon| < 1/16`.
5. `(u, s) -> u_i + s epsilon(u)` is the homotopy. ∎

So `pi_i = g_(C_i)^* psi_i^* theta` in `H^1(T^n)`, where `theta` generates `H^1(T)`.

## 2. Lemma S (slice lemma)

Every zero row `j` has a continuous lift `phi_j: T^n -> R`, `g_j = phi_j mod 1`. For `Q ⊆ Z_0` write
`Phi_Q = (phi_j)_(j in Q): T^n -> R^Q`, with the sup metric on `R^Q`.

**Lemma S.** Let `Z ⊆ Z_0`, and let `X ⊆ B_0` be a set of inputs with `|C_i \ Z| <= 1` for every
`i in X`. Then there is `epsilon > 0` with the following property. For every open `O ⊆ R^Z` of diameter
`< epsilon`, every `pi_i` with `i in X` restricts to `0` in `H^1(Phi_Z^-1(O))`.

*Proof.* Fix `i in X`. Write `C_i = Z_i ∪ A_i`, with `Z_i = C_i ∩ Z` and `A_i = C_i \ Z` (`|A_i| <= 1`).
Let `rho: R^(C_i) -> T^(C_i)` be the covering, `U~ = rho^-1(U_i)` (open), `Psi = psi_i o rho`, and
`K = Phi_(C_i)(T^n)` (compact, contained in `U~` because `rho o Phi_(C_i) = g_(C_i)`). By Lemma N,
`pi_i = Phi_(C_i)^* Psi^* theta`.

*Case `A_i = ∅`.* `K` is a compact subset of the open `U~ ⊆ R^(Z_i)`. Let `epsilon_i` be such that the
`epsilon_i`-neighbourhood of `K` lies in `U~`. If `O` has diameter `< epsilon_i` and meets
`Phi_Z(T^n)`, then its projection to `R^(Z_i)` lies in a sup-ball `D` of radius `epsilon_i` around a
point of `K`, and `D ⊆ U~`. `D` is convex, so `Psi^* theta` vanishes on `D`, and `pi_i` vanishes on
`Phi_Z^-1(O)`, which `Phi_(C_i)` maps into `D`. If `O` misses the image, its preimage is empty.

*Case `A_i = {a}`.* Coordinates on `R^(C_i)` are `(z, y)` with `z in R^(Z_i)` and `y in R`. Let `K'` be
the projection of `K` to `R^(Z_i)`.
1. For `c in K'` the slice `L_c = {y : (c, y) in K}` is compact and lies in the open set
   `O_c = {y : (c, y) in U~} ⊆ R`. The components of `O_c` are open intervals. Finitely many of them
   cover `L_c`. Shrink each to an open interval `J_k` with closure in `O_c`, still covering `L_c`, and
   with pairwise disjoint closures.
2. By the tube lemma there is `r_c > 0` with `cl D(c, r_c) x cl J_k ⊆ U~` for every `k`. Here
   `D(c, r)` is the open sup-ball.
3. Shrinking `r_c`, `K ∩ (cl D(c, r_c) x R) ⊆ R^(Z_i) x ∪_k J_k`. Otherwise there are points of `K` with
   first coordinate tending to `c` and second coordinate outside the open set `∪ J_k`. By compactness
   they have a limit point `(c, y)` in `K` with `y ∉ ∪ J_k`, contradicting `L_c ⊆ ∪ J_k`.
4. The balls `D(c, r_c/2)`, `c in K'`, cover the compact `K'`. Let `epsilon_i` be a Lebesgue number of
   this cover, and also at most `min r_c / 2` over a finite subcover.
5. Let `O ⊆ R^Z` have diameter `< epsilon_i`. Its projection `O'` to `R^(Z_i)` has diameter `< epsilon_i`,
   since projection is 1-Lipschitz for the sup metric. If `O'` misses `K'`, the preimage is empty.
   Otherwise `O' ∩ K'` lies in some `D(c, r_c/2)`, and so `O' ⊆ D(c, r_c)`. Then
   `Phi_(C_i)(Phi_Z^-1(O)) ⊆ K ∩ (D(c, r_c) x R) ⊆ ⊔_k D(c, r_c) x J_k`.
   - The right side is a disjoint union of open convex boxes inside `U~`.
   - `Psi^* theta` vanishes on each box, hence on their disjoint union.
   - So `pi_i` vanishes on `Phi_Z^-1(O)`.

Take `epsilon = min_(i in X) epsilon_i`. ∎

The point is that the private part of each control set is one real coordinate. So slices of `U~` over the
shared coordinates are open subsets of `R`, which carry no `H^1`. With two private coordinates the slices
are open subsets of `R^2`, and the torus of revolution shows that the lemma then fails.

## 3. Lemma LS (covering-dimension count)

**Lemma LS.** Let `Z ⊆ Z_0` and `X ⊆ B_0` with `|C_i \ Z| <= 1` for all `i in X`. Then `|X| <= |Z|`.

*Proof.* Put `m = |Z|` and take `epsilon` from Lemma S.
1. *Cover.* Triangulate `R^Z` with mesh `< epsilon/4`, and take the barycentric subdivision `T'`.
   - Each vertex of `T'` is the barycentre of a simplex of the original triangulation. Colour it by the
     dimension of that simplex, from `0` to `m`.
   - A simplex of `T'` is a chain `s_0 < s_1 < ... < s_r` of original simplices, so its vertices have
     distinct colours.
   - Let `W^k` be the union of the open stars in `T'` of the colour-`k` vertices.
   - Two such stars are disjoint: a common point would have a carrier simplex in `T'` containing two
     vertices of colour `k`.
   - The open stars of all vertices cover `R^Z`, so `W^0, ..., W^m` cover `R^Z`.
   - Each star has diameter `< epsilon`.
2. *Vanishing.* Put `W_k = Phi_Z^-1(W^k)`. This is an open cover of `T^n` and a disjoint union of the open sets
   `Phi_Z^-1(star)`. By Lemma S every `pi_i`, `i in X`, restricts to `0` on each piece, hence to `0` in
   `H^1(W_k) = prod H^1(pieces)`.
3. *Cup product.* Suppose `|X| >= m+1` and pick distinct `i_0, ..., i_m` in `X`.
   - Each `pi_(i_k)` comes from a class `a_k in H^1(T^n, W_k)`, by exactness of the pair sequence.
   - The relative cup product for open sets (Hatcher, Section 3.2) puts `a_0 ∪ ... ∪ a_m` in
     `H^(m+1)(T^n, W_0 ∪ ... ∪ W_m) = H^(m+1)(T^n, T^n) = 0`.
   - It maps to `pi_(i_0) ∪ ... ∪ pi_(i_m)`, which is nonzero in the exterior algebra `H^*(T^n; Z)`.
   - This is a contradiction. ∎

For `m = 0` the argument reads: Lemma S applied to `O = R^0` shows `pi_i = 0`, which is impossible. So `X`
is empty.

## 4. Proof of Theorem Z (random shared set)

For `T ⊆ P_0`, apply Lemma LS with `Z = P_0 \ T` and `X_T = {i in B_0 : |C_i ∩ T| <= 1}`. Since
`C_i ⊆ P_0`, we have `C_i \ Z = C_i ∩ T`, and so

    |X_T| <= |P_0| - |T|   for every T ⊆ P_0.                         (*)

**Averaging.** Fix `0 < p < 1` and put each `j in P_0` into `T` independently with probability `p`.
1. For `|C_i| = k`, `P(|C_i ∩ T| <= 1) = f_k(p) = (1-p)^(k-1) (1 + (k-1)p)`.
2. `f_(k+1)/f_k = 1 - k p^2 / (1 + (k-1)p) <= 1`, so `f_k >= f_K` for `k <= K`.
3. Taking expectations in (*) gives `|B_0| f_K(p) <= E|X_T| <= (1-p)|P_0|`.
4. Hence `|B_0| <= |P_0| / h_K(p)`, where `h_K(p) = (1-p)^(K-2) (1 + (K-1)p)`.

**Optimising.**
- `d/dp log h_K = -(K-2)/(1-p) + (K-1)/(1+(K-1)p)`. This vanishes exactly at `p* = 1/(K-1)^2`, which is the
  maximum.
- `K = 2`: `h_2 = 1+p`, and the supremum `2` is approached as `p -> 1`, so `c_2 = 1/2`.
- `K = 3`: `p* = 1/4`, `h = (3/4)(3/2) = 9/8`, so `c_3 = 8/9`.
- `K = 4`: `p* = 1/9`, `h = (64/81)(4/3) = 256/243`, so `c_4 = 243/256`.
- For large `K`: `log h_K(p*) = 1/(2(K-1)^2) + O(K^-3)`.

This proves Theorem Z. ∎

**The `d`-dimensional form.** Under LRSF (C), the real coordinate `(i, a)`, `a <= d`, is controlled by
the `d|C_i| <= dK` real coordinates of the sites in `C_i`. If `g^* = 0`, every real output coordinate is a
zero row and every real input lies in `B_0`. So `d|I| <= c_(dK) |P_0| <= c_(dK) d|J|`, which is the
Corollary. ∎

## 5. Checks, consequences, and what remains

**Checks.**
- *`K = 2`.* `c_2 = 1/2` is the zero-row part of w19's two-output theorem, and it is sharp: a small round
  circle in `T^2` has `|B_0| = 1` and `|P_0| = 2`.
- *General `K`.* A null-homotopic embedding `T^(K-1) -> R^K -> T^K`, with every input controlled by all `K`
  outputs, has ratio `(K-1)/K`. And `(K-1)/K <= c_K` because `h_K(p*) = 1 + O(K^-2) < K/(K-1)`. So the
  truth lies in `[(K-1)/K, c_K]`, consistent with Proposition S of w19.
- *Two private coordinates.* Lemma S genuinely needs `|C_i \ Z| <= 1` (end of Section 2). The random-`T`
  count only ever uses sets with at most one private coordinate.

**Consequences for LRSF.**
1. *The zero-row sector of (E_K) holds for every `K`.* Here (E_K) is w19's reduction target,
   `|B| <= c * defect`. Write `defect(P) = |P| - rank(rows of g^* on P)`. Zero rows have rank `0`, so
   `defect(P_0) = |P_0|`, and Theorem Z gives `|B_0| <= c_K defect(P_0)`.
2. *Null-homotopic maps.* The linear form of LRSF holds for every `K` and `d`, with no locality, whenever
   `g^* = 0`. The constant is `C = c_(dK)/(1 - c_(dK)) = O(d^2 K^2)`.
3. *The step is topological.* Control plus covering dimension decides the sector. Locality (L) plays no role.

**What remains: the sector `B_1`.** These are inputs `i` with `pi_i` outside the span of their control rows,
and some control row nonzero but dependent.
- The first case is `K = 3` with proportional rows `(v, av, bv)`.
- *Attempt.* Restrict `g` to the annihilator subtorus `S = {u : v(u) = 0}` and rerun Lemmas S and LS there.
  - This gives `|X_T| <= D + 2 r_P - |T|`, where `r_P` is the rank of the rows on `P`.
  - The cost `2 r_P` comes from the private coordinate and the rank drop of the shared coordinates.
  - The bound is weaker than (E_K) as soon as `r_P` is a positive proportion of `|P|`.
- *Where it dies.* On nonzero rows, the lift `phi_j` to `R` exists only on `S`, and `S` has codimension
  `r_P`. The cover of Lemma LS has to be paid for in the dimension of `T^n` that is lost. A proof of the
  `B_1` sector needs either a Lemma S for circle-valued shared coordinates, or an equivariant cover of
  `T^Z` with `|Z| + 1 - rank` colours. Neither is available.
