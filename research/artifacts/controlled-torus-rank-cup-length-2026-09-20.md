# Boundedly controlled torus maps lose rank at most linearly in their surplus

Agent: swarm-0917-w22-w22-gs-pull, 2026-09-20. Target:
`local-rectangular-small-fibre-maps-lose-proportional-rank` (LRSF), family cohomology-index.

## 0. Statement

`T = R/Z`, `||t||` = distance to `Z`. `g: T^n -> T^N` continuous. `x_j` generates `H^1` of the
`j`-th output circle, `pi_i` that of the `i`-th input circle. The *row* of output `j` is
`row_j = g^* x_j in Z^n = H^1(T^n; Z)`. Put

- `W = span_Q {row_j}` in `Q^n`, `r = dim W = rank g^*`;
- `L = n - r` (the rank loss) and `D = N - r` (the corank of the rows).

**Control.** Each input `i` has `C_i ⊆ {1..N}` and there is `eta > 0` with

> (C) `||g(u)_j - g(u')_j|| < eta` for all `j in C_i` implies `||u_i - u'_i|| < 1/16`.

**Theorem R.** If `|C_i| <= K` for all `i`, with `K >= 2`, then

    L <= c_K D,   c_K = 1 / max_(0<p<1) (1-p)^(K-2) (1 + (K-1) p),

so `c_2 = 1/2`, `c_3 = 8/9`, `c_4 = 243/256`, and `c_K = 1 - 1/(2(K-1)^2) + O(K^-3) < 1`.
(`K = 1` gives `L = 0`.) Equivalently, since `D = (N - n) + L`,

    rank g^* >= n - C_K (N - n),   C_K = c_K / (1 - c_K).

No locality hypothesis is used: outputs may depend on all inputs.

**Torus sites.** For `g: (T^d)^I -> (T^d)^J` satisfying (C) of LRSF with `|C_i| <= K` sites, every
real input coordinate of site `i` is controlled by the `d|C_i| <= dK` real coordinates of the sites
in `C_i` (the sup metric on `T^d` is the max over coordinates). So

    rank g^* >= d|I| - C_(dK) d (|J| - |I|),

which is the **linear form of LRSF**, for every `K`, `d`, `eta`, without (L). LRSF itself follows with
`beta = delta / C_(dK)`.

**Relation to earlier work (bus, not landed in this worktree).**
- `r = 0` is w21's Theorem Z (`zero-row-controlled-inputs-are-outnumbered`, hold ref
  `refs/swarm-hold/w21-gs-pull`), with the same constant. Its Lemmas N and S are reused below,
  localised to a neighbourhood of one fibre.
- `K = 2` reproduces w19's Theorem T (`two-output-control-circle-maps-lose-rank-at-most-surplus`):
  `c_2 = 1/2` gives `rank g^* >= 2n - N`, the sharp `C = 1`.
- w21 recorded the `B_1` sector (nonzero dependent control rows) as open, because restricting to the
  annihilator subtorus costs `2 r_P`. The new step here does not restrict: it works in an open
  neighbourhood of a fibre of the row map and pays for the row classes with `r` extra open sets of a
  cup-length cover (Section 4). Since `L` is exactly the dimension of `Q^n / W`, the `r` row classes
  cost nothing in the count.

## 1. Lemma N (coarse inverses)

**Lemma N.** For each input `i` there are an open `U_i ⊆ T^(C_i)` containing `g_(C_i)(T^n)` and a
continuous `psi_i: U_i -> T` with `psi_i o g_(C_i) ≃ pi_i` (the coordinate map `u -> u_i`).

*Proof* (w19/w21).
1. Cover the compact `Y_i = g_(C_i)(T^n)` by finitely many open sup-balls `B_alpha` of radius `eta/2`,
   centred at `y_alpha = g_(C_i)(u^alpha)`. Let `U_i = ∪ B_alpha` and `p_alpha = u^alpha_i`.
2. If `B_alpha ∩ B_beta ≠ ∅`, then `y_alpha` and `y_beta` are `eta`-close, so
   `||p_alpha - p_beta|| < 1/16` by (C).
3. Take a partition of unity `lambda_alpha` subordinate to `{B_alpha}`. For any `alpha_0` with
   `y in B_(alpha_0)`, set `psi_i(y) = p_(alpha_0) + sum_alpha lambda_alpha(y) delta(p_(alpha_0), p_alpha)`,
   where `delta(p, q) in (-1/2, 1/2)` represents `q - p`.
   - All displacements are `< 1/16`, so this is well defined and continuous.
4. For `y = g_(C_i)(u) in B_alpha`, (C) gives `||u_i - p_alpha|| < 1/16`. So
   `psi_i(g_(C_i)(u)) = u_i + epsilon(u)`, with `epsilon` continuous and `|epsilon| < 1/8`.
5. `(u, s) -> u_i + s epsilon(u)` is the homotopy. ∎

Write `rho: R^(C_i) -> T^(C_i)` for the covering, `U~_i = rho^-1(U_i)` and `Psi_i = psi_i o rho`.

## 2. Coordinates adapted to a private set `T`

Fix `T ⊆ {1..N}` and put `Z = {1..N} \ T`. Let `Lambda = {lambda in Z^N : sum_j lambda_j row_j = 0}`.
It has rank `D`. Put

    delta(T) = dim_Q proj_T(Lambda ⊗ Q) = |T| - (r - r_Z),   r_Z = dim span{row_j : j in Z}.

Indeed `proj_T(Lambda_Q)` has dimension `D - dim(Lambda_Q ∩ Q^Z) = D - (|Z| - r_Z)`. So `delta(T)` is the
rank of `T` in the dual matroid of the rows.

**Characters.**
- Choose `c_1, ..., c_(r_Z) in Z^Z`, supported in `Z`, whose images `w_l = sum_j c_(l,j) row_j` form a
  basis of `span{row_j : j in Z}`.
- Complete with `c_(r_Z+1), ..., c_r in Z^N` so that `w_1, ..., w_r` is a basis of `W`.
- The `c_l` are linearly independent in `Q^N`, because their images are.
- Let `c: R^N -> R^r` be `c(y)_l = c_l · y`, and let `gamma: T^n -> T^r` be `gamma_l = c_l o g`, the
  character `c_l` applied to `g`. Then `gamma^* dt_l = w_l`.

**The subspace `E`.** `E = ker c ⊆ R^N` has dimension `N - r = D`. Every `y in R^T` (supported in `T`)
satisfies `c_l · y = 0` for `l <= r_Z`, so `dim(E ∩ R^T) >= |T| - (r - r_Z) = delta(T)`. Hence

    m := dim proj_Z(E) = D - dim(E ∩ R^T) <= D - delta(T).                              (2.1)

## 3. Real lifts near one fibre, and the localised slice lemma

Fix `q in T^r`. For `rad in (0, 1/2)`, let `Q(rad) = {t in T^r : ||t_l - q_l|| < rad for all l}` (open)
and `N(rad) = gamma^-1(Q(rad))`.

**Lemma F (lifts).** On `N_0 = N(1/4)`, every output `g_j` has a continuous real lift `Y_j: N_0 -> R`.

*Proof.*
1. `row_j in W`, so `a row_j = sum_l b_l w_l` with `a ≠ 0` and `b_l in Z`.
2. Each `w_l` restricts to `0` on `N_0`, because `gamma_l` maps `N_0` into an open arc.
3. So `a (row_j|_(N_0)) = 0` in `H^1(N_0; Z)`. This group is torsion-free, since `N_0` is an open subset
   of a manifold and `H^1(-;Z) = Hom(H_1, Z)`.
4. So `g_j|_(N_0)` is null-homotopic and lifts to `R`. ∎

Put `N_1 = N(1/8)`.
- Its closure is compact and lies in `N_0`, so it meets only finitely many components of `N_0`.
- Let `N_0'` be the union of these components. It is open and contains `cl N_1`.
- Choose the lifts on each such component. Then `Y = (Y_j): N_0' -> R^N` is continuous, and `Y(cl N_1)`
  is compact, inside a ball of radius `R_0`.

**Lemma S' (localised slice lemma).** There is `epsilon > 0` with the following property. For every
input `i` with `|C_i ∩ T| <= 1` and every open `O ⊆ R^Z` of sup-diameter `< epsilon`, `pi_i`
restricts to `0` in `H^1(Y_Z^-1(O) ∩ N_1; Z)`.

*Proof.* This is w21's Lemma S with `T^n` replaced by `N_1` and `Phi` by `Y`. It uses only two things:
the image is compact, and all control coordinates are real-valued.
1. `K_i = Y_(C_i)(cl N_1)` is compact and lies in `U~_i`, since `rho(Y_(C_i)(u)) = g_(C_i)(u) in U_i`.
   On `N_0'`, `pi_i = g_(C_i)^* psi_i^* theta = Y_(C_i)^* Psi_i^* theta` (Lemma N, restricted).
2. Write `C_i = Z_i ⊔ A_i` with `Z_i = C_i ∩ Z`, `A_i = C_i ∩ T` and `|A_i| <= 1`.
3. *Case `A_i = ∅`.*
   - Take `epsilon_i` such that the `epsilon_i`-neighbourhood of `K_i` lies inside `U~_i`.
   - If `O` meets `Y_Z(N_1)`, its projection to `R^(Z_i)` lies in a sup-ball `D ⊆ U~_i`.
   - `D` is convex, so `Psi_i^* theta|_D = 0`, and `Y_(C_i)` maps `Y_Z^-1(O) ∩ N_1` into `D`.
4. *Case `A_i = {a}`.* Use coordinates `(z, y) in R^(Z_i) x R`, and let `K_i'` be the projection of `K_i`.
   - For `c in K_i'`, the slice `L_c = {y : (c, y) in K_i}` is compact and lies in the open set
     `O_c = {y : (c, y) in U~_i} ⊆ R`.
   - Cover `L_c` by finitely many open intervals `J_k` whose closures are pairwise disjoint and lie inside
     `O_c`.
   - By the tube lemma and compactness, there is `r_c > 0` with `cl D(c, r_c) x cl J_k ⊆ U~_i` and
     `K_i ∩ (cl D(c, r_c) x R) ⊆ R^(Z_i) x ∪_k J_k`.
   - Let `epsilon_i` be a Lebesgue number of the cover `{D(c, r_c/2)}` of `K_i'`, and at most half the
     least `r_c` of a finite subcover.
   - For `O` of diameter `< epsilon_i`, `Y_(C_i)(Y_Z^-1(O) ∩ N_1)` lies in the disjoint union of the
     convex boxes `D(c, r_c) x J_k ⊆ U~_i`, on which `Psi_i^* theta` vanishes.
5. Take `epsilon = min_i epsilon_i`. ∎

## 4. Lemma C (cup-length count mod the rows)

Let `X_T = {i : |C_i ∩ T| <= 1}` and write `dim_W(S) = dim (span{pi_i : i in S} + W) / W`.

**Lemma C.** `dim_W(X_T) <= D - delta(T)`.

*Proof.* Keep `T`, the `c_l`, `q`, `N_1`, `Y` and `epsilon` from Sections 2 and 3.

1. *Where `Y(N_1)` lies.*
   - `c · Y` is a real lift of `gamma` on `N_0'`, and `c · Y(cl N_1)` is compact.
   - So `c · Y(cl N_1)` meets only finitely many of the boxes `q~ + k + [-1/8, 1/8]^r`, `k in Z^r`, where
     `q~` is a fixed lift of `q`. Let `G = {g_1, ..., g_M}` be the corresponding points `q~ + k`.
   - Fix a right inverse `c^+` of `c` and put `a_s = c^+ g_s`.
   - For `u in N(rad) ∩ cl N_1` with `rad <= 1/8`, there is `s` with `c · Y(u) in g_s + [-rad, rad]^r`,
     so `dist(Y(u), E + a_s) <= ||c^+|| rad`.
2. *The polyhedron.* Let `P = ∪_s proj_Z((E + a_s) ∩ B(0, R_0 + 1)) ⊆ R^Z`.
   - `P` is a finite union of compact convex sets of dimension `<= m` (see (2.1)), so it is a compact
     polyhedron of covering dimension `<= m` (sum theorem).
   - By Ostrand's theorem (a normal space of covering dimension `<= m`: every finite open cover has an
     open refinement that is a union of `m + 1` families of pairwise disjoint sets; Engelking,
     *Dimension Theory*) and the shrinking lemma,
     `P` has a finite open cover by sets `V_alpha` of diameter `< epsilon/3`. The cover splits into
     `m + 1` families `F_0, ..., F_m`, and within each family the closures `cl V_alpha` are pairwise
     disjoint.
   - Let `3 tau > 0` be less than the least distance between two closures in the same family, and
     `tau < epsilon/3`.
   - Put `V~_alpha = {y in R^Z : dist(y, cl V_alpha) < tau}`. These sets are open, of diameter
     `< epsilon`, and pairwise disjoint within each family. Their union contains the
     `tau`-neighbourhood of `P`.
3. *The fibre part.* Choose `rad < 1/8` with `||c^+|| rad < min(tau, 1)`, and let
   `F = gamma^-1(cl Q(rad)) ⊆ N_1`. By step 1, `Y_Z(F)` lies in the `tau`-neighbourhood of `P`. For
   `k = 0..m`, put

       W_k = ∪_(alpha in F_k) (Y_Z^-1(V~_alpha) ∩ N_1).

   - This is a disjoint union of open sets, so `H^1(W_k) = prod H^1(pieces)`.
   - By Lemma S', every `pi_i` with `i in X_T` vanishes on each piece, and hence on `W_k`.
   - Also `F ⊆ W_0 ∪ ... ∪ W_m`.
4. *The row part.* For `l = 1..r`, put `V_l = gamma^-1({t : ||t_l - q_l|| > rad})`.
   - `gamma_l` maps `V_l` into an open arc, so `w_l = gamma_l^* theta` vanishes on `V_l`.
   - `V_1 ∪ ... ∪ V_r = T^n \ F`.
5. *Cup length.* Suppose that `i_0, ..., i_m in X_T` have `pi_(i_0), ..., pi_(i_m)` independent mod `W`.
   - Then `pi_(i_0), ..., pi_(i_m), w_1, ..., w_r` are independent in `Q^n`, so their product is nonzero
     in `H^(m+1+r)(T^n; Z) = Λ^(m+1+r) Z^n`.
   - But each factor comes from a relative class on its own open set: `pi_(i_k)` from
     `H^1(T^n, W_k)` and `w_l` from `H^1(T^n, V_l)`.
   - So the product comes from `H^(m+1+r)(T^n, W_0 ∪ ... ∪ W_m ∪ V_1 ∪ ... ∪ V_r) = H^*(T^n, T^n) = 0`,
     by the relative cup product for open sets (Hatcher, Section 3.2).
   - This is a contradiction, so `dim_W(X_T) <= m <= D - delta(T)`. ∎

For `r = 0` there are no `V_l`, `F = T^n`, `E = R^N`, and Lemma C is w21's Lemma LS combined with
Lemma S. The only new ingredient is that the `r` row classes are killed on arcs of `gamma` and pay
for themselves in the cup length.

## 5. Proof of Theorem R

1. The `pi_i` span `Q^n`, so there is `B' ⊆ {1..n}` with `|B'| = L` whose classes form a basis of
   `Q^n / W`.
2. For every `T`, Lemma C gives
   `|B' ∩ X_T| = dim_W(B' ∩ X_T) <= D - delta(T)`.
3. *Averaging.* Put each output into `T` independently with probability `p in (0, 1)`.
   - `delta(T) >= |T ∩ B*|` for a basis `B*` of the dual matroid, that is, `|B*| = D` coordinates on which
     `Lambda_Q` projects isomorphically. So `E delta(T) >= p D`.
   - `P(i in X_T) = f_(|C_i|)(p) >= f_K(p)`, where `f_k(p) = (1-p)^(k-1)(1 + (k-1)p)` is decreasing in `k`
     (w21: `f_(k+1)/f_k = 1 - k p^2/(1 + (k-1)p)`).
   - So `L f_K(p) <= (1 - p) D`, that is, `L <= D / h_K(p)` with `h_K(p) = (1-p)^(K-2)(1 + (K-1)p)`.
4. Optimising in `p` gives `c_K` (maximum at `p = 1/(K-1)^2`; as `p -> 1` when `K = 2`).
5. Finally `D = N - r = (N - n) + L`, so `L (1 - c_K) <= c_K (N - n)`. ∎

**Torus sites.** Apply Theorem R to `T^(d|I|) -> T^(d|J|)`, with each real input coordinate
controlled by at most `dK` real output coordinates. ∎

## 6. Checks and consequences

**Checks.**
- *Square case, `N = n`.* Then `D = L`, so `L <= c_K L` with `c_K < 1` forces `L = 0`. This agrees
  with [LEF] Theorem 1 (under bounded control).
- *`K = 2`.* `c_2 = 1/2`, so `L <= N - n`, that is, `rank g^* >= 2n - N`. This is w19's sharp `C = 1`.
- *Proposition S.*
  - `T^k -> T^(k+1)` into a small ball has `r = 0`, `L = k`, `D = k + 1` and `K = k + 1`.
  - Theorem R requires `max_p h_(k+1)(p) <= 1 + 1/k`.
  - This holds: the maximum is `(1 - 1/k^2)^(k-1)(1 + 1/k)`, at `p = 1/k^2` (or `p -> 1` when
    `k = 1`).
  - So `C_K` must be at least `K - 1`. Here it is about `2(K-1)^2`.
- *[LEF] Theorem 3.* `T^(N-1) -> T^N` into a small ball has `L = N - 1` and `D = N`.
  - The bound requires `K` of at least order `sqrt(N/2)`, and that map has control sets of size
    about `N`.
  - So nothing is contradicted.
- *Where `K` enters.* Only in `P(i in X_T) >= f_K(p)`. Lemma C has no constant.

**Consequences.**
1. The linear form of LRSF holds without (L), with `C = c_(dK) / (1 - c_(dK)) = O(d^2 K^2)`,
   independent of `eta`. LRSF holds with `beta = delta (1 - c_(dK)) / c_(dK)`.
2. With `sofic-torus-c2-reduces-to-rectangular-small-fibres`, every injective torus automaton over
   every sofic group has regular degree and is surjective.
   - That reduction is agent-verified only and needs re-audit.
   - In particular, check that (C) holds with `|C_i| <= K` uniformly at certified vertices, and that
     frozen vertices are counted as surplus.
3. w19's `(E_K)` and w21's open `B_1` sector are not needed.

**Not claimed.**
- The constant is not claimed to be optimal.
- Nothing is claimed for non-sofic groups.
- The result is agent-verified only. Audit Lemma S' and Lemma C, steps 4 and 5, first.
