# Rank functions on Thompson's V split off the augmentation rank

Lane `w7-v-rank-split`, 2026-09-12. Supports `v-rank-functions-split-as-augmentation-plus-reduced`. Bears on
`thompson-v-has-no-nontrivial-f2-rank-model` and `thompson-v-ternary-rank-functions-are-augmentation`. These are
candidate proofs, held OPEN until `w3-vf-linear` re-derives them.

**Cited.**
- [FR] `research/artifacts/thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`: facts (S1)–(S6),
  the fixed rank `phi`, Theorem 1.2 (`v-rank-torsion-constant-equals-global-fixed-rank`), Corollary 1.3.
- [TS] the torsion law `rk(e_P) = a + (1 - a)/|P|` (`v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`).
- [CG] `research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md`: corner additivity
  (S3'), Theorem 1.1, Section 4.2.
- [FW] `research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md`.

## 0. Summary

- **(a) Splitting holds, over every field** (Theorem 1.4). If `phi_V < 1`, then
  `rk_0 = (rk - phi_V rk_aug)/(1 - phi_V)` is a Sylvester matrix rank function with `phi_V(rk_0) = 0`.
- **The decisive input** (Lemma 1.2). Averaging idempotents of large clopen-cycle groups are almost invariant on
  both sides. The column bound follows from (S5) with no commutation. The row bound is the column bound for the
  transposed rank function `rk*`, whose fixed rank is again the torsion constant.
- **Convex structure** (Corollary 1.5). The rank functions on `F[V]` form the join of the point `rk_aug` and the
  face `P_0 = {phi_V = 0}`. The decomposition is unique.
- **Models** (Corollary 2.1). A model with `0 < phi_V < 1` is the direct sum of the trivial model and a model with
  `phi_V = 0`, whose rank function is `rk_0`. The fixed idempotent is two-sided invariant. This replaces the
  **[matricial]** step of [FR] Corollary 1.3(5).
- **Not formal** (Section 1.4). For `Z` through a Jordan block, `rk_0` breaks the triangular axiom on `[[y, 1], [0, y]]`.
- **(b)** (Section 3). `<x_0, x_1, t>` is not `V` for interior transpositions or for `pi_0 = [0] <-> [10]`. It
  contains `V_O ≅ V`, so it is sofic iff `V` is. No forcing identity and no `phi_V = 0` model was found.

## 1. Splitting

**Setting.** As in [FR] Section 0.
- `F` is any field, `R = F[V]`, and `rk` a Sylvester matrix rank function on `R` (rectangular matrices included).
- `phi = phi_V(rk)`, and `p` is an odd prime different from `char F`.
- For a clopen-cycle subgroup `P`, `e_P = |P|^(-1) sum_(q in P) [q]`.
- For `A = sum_x a_x [x]` with scalar `m x n` matrices `a_x`: `eps(A) = sum_x a_x`, `supp A = {x : a_x != 0}`, and
  `rk_aug(A) = rank_F eps(A)`.

**Lemma 1.1 (transposed rank function).** Let `A*` apply the `F`-linear anti-automorphism `[g] -> [g^(-1)]`
entrywise, and put `rk*(A) = rk((A*)^T)`. Then `rk*` is a Sylvester matrix rank function on `R`,
`rk*(e_P) = rk(e_P)`, and `phi_V(rk*) = 1 - rk row(1 - [s] : s in S) = phi_V(rk)`.

*Proof.*
- **Axioms.** `((MN)*)^T = (N*)^T (M*)^T` gives the product bound, and direct sums are preserved. `[[M, C], [0, N]]`
  goes to `[[M*^T, 0], [C*^T, N*^T]]`, and a block permutation turns that into `[[N*^T, C*^T], [0, M*^T]]`.
- **Idempotents.** `e_P* = e_P`, since `P` is closed under inverses. So [TS] gives `rk*` the same constant `a`.
- **Fixed rank.** [FR] Theorem 1.2 for `rk` and for `rk*` gives `phi_V(rk) = a = phi_V(rk*)`. Since `S^(-1)` also
  generates, `phi_V(rk*) = 1 - rk row(1 - [s] : s in S)`. ∎

**Lemma 1.2 (two-sided almost invariance).** For every clopen-cycle subgroup `P` and all `g_1, ..., g_m` in `V`,

```text
rk col((1 - [g_i]) e_P : i) <= rk(e_P) - phi_V = (1 - phi_V)/|P|,
rk row(e_P (1 - [g_i]) : i) <= (1 - phi_V)/|P|.
```

*Proof.* Write `e = e_P`.
- **Same left ideal.** Put `Y_1 = {1 - e} ∪ {(1 - [g_i]) e}` and `Y_2 = {1 - e} ∪ {1 - [g_i]}`. They generate the
  same left ideal, because `1 - [g_i] = (1 - [g_i]) e + (1 - [g_i])(1 - e)`. By (S5), `rk col(Y_1) = rk col(Y_2)`.
- **Upper bound.** `1 - e = |P|^(-1) sum_q (1 - [q])`, so `Y_2` lies in the augmentation left ideal. By (S5) and
  deleting rows, `rk col(Y_2) <= 1 - phi_V`.
- **Splitting the column.** Let `C = col(Y_1)`. Since `(1 - [g_i]) e (1 - e) = 0`,
  `C (1 - e, e) = diag(1 - e, col((1 - [g_i]) e))`, and `diag(...) (1; 1) = C`. So
  `rk col(Y_1) = rk(1 - e) + rk col((1 - [g_i]) e)`.
- **Column bound.** `rk(1 - e) = 1 - rk(e)` by (S3). [TS] and [FR] Theorem 1.2 give `rk(e) - phi_V = (1 - phi_V)/|P|`.
- **Row bound.** `(e (1 - [g]))* = (1 - [g^(-1)]) e`, so `rk row(e (1 - [g_i])) = rk* col((1 - [g_i^(-1)]) e)`.
  Apply the column bound to `rk*`, using Lemma 1.1. ∎

Nothing here needs `e_P` to commute with `[g]`: the right factor `e` kills `1 - e` by itself. In [CG] Step 3 the
group `G` had to normalize `Q` instead.

**Lemma 1.3 (cutting).** For `A` in `M_(m x n)(R)` put `c_P(A) = (1 - e_P) A (1 - e_P)` and
`delta_P(A) = 2 |supp A| min(m, n) (1 - phi_V)/|P|`. Then

```text
| rk(A) - rk(e_P) rank_F eps(A) - rk(c_P(A)) | <= delta_P(A),
rk( c_P(AB) - c_P(A) c_P(B) ) <= delta_P(A).
```

*Proof.* Write `e = e_P`.
- **Error terms.** `e A - eps(A) e = - sum_x a_x e (1 - [x])`. A scalar matrix of rank `r` times `e(1 - [x])` has rank
  `r rk(e (1 - [x]))` by (S1) and (S3). So Lemma 1.2 bounds `rk(e A - eps(A) e)` and `rk(A e - eps(A) e)` by
  `delta_P(A)/2` each.
- **Identity.** `A = e A + (1 - e) A e + c_P(A)`, `e A = eps(A) e + (e A - eps(A) e)`, and
  `(1 - e) A e = (1 - e)(A e - eps(A) e)`, because `(1 - e) eps(A) e = eps(A)(1 - e) e = 0`.
- **Corners.** `eps(A) e` sits in the `e` corner and `c_P(A)` in the `1 - e` corner. By (S3'),
  `rk(eps(A) e + c_P(A)) = rank_F eps(A) rk(e) + rk(c_P(A))`. With (S2) this gives the first bound.
- **Products.** `c_P(AB) - c_P(A) c_P(B) = (1 - e) A e B (1 - e) = (1 - e)(A e - eps(A) e) B (1 - e)`. ∎

**Theorem 1.4 (splitting).** Let `phi = phi_V(rk) < 1`. For every matrix `A` over `R`,

```text
rk_0(A) := (rk(A) - phi rank_F eps(A)) / (1 - phi) = lim_(|P| -> inf) rk(c_P(A)) / (1 - phi),
```

and `rk_0` is a Sylvester matrix rank function on `R` with `phi_V(rk_0) = 0`. So
`rk = phi_V rk_aug + (1 - phi_V) rk_0`.

*Proof.* Clopen-cycle subgroups of unbounded order exist (the groups `T_k` of [FR] Theorem 1.2). Along them
`rk(e_P) -> phi` and `delta_P(A) -> 0`, so Lemma 1.3 gives the limit. The axioms, by hand:
- **Normalization.** `rk_0(1) = lim rk(1 - e_P)/(1 - phi) = 1`.
- **Direct sums.** `rk` and `rank_F eps` are additive.
- **Products.** `rk(c_P(AB)) <= min(rk c_P(A), rk c_P(B)) + delta_P(A)`; let `|P| -> inf`. In terms of `rk`, this is
  `rk(A) - rk(AB) >= phi (rank eps(A) - rank eps(AB))`, which is not formal (Section 1.4).
- **Upper-triangular blocks.** `c_P([[M, C], [0, N]]) = [[c_P(M), c_P(C)], [0, c_P(N)]]`. The axiom in `R` gives
  `rk >= rk c_P(M) + rk c_P(N)`; let `|P| -> inf`.
- **Positivity.** `rk_0 >= 0` as a limit of ranks. So `rk(A) >= phi_V rank_F eps(A)` for every `A`.
- **Fixed rank.** `eps(1 - [s]) = 0`, so `rk_0 col(1 - [s]) = (1 - phi)/(1 - phi) = 1`. ∎

**Corollary 1.5 (convex structure).**
- **Faces.** `phi_V` is affine on the convex set `P(F[V])`, with values in `[0, 1]`. So `P_0 = {phi_V = 0}` and
  `{rk_aug} = {phi_V = 1}` ([FR] Corollary 1.3(3)) are faces.
- **Uniqueness.** If `rk = t rk_aug + (1 - t) r` with `r` in `P_0`, then `phi_V(rk) = t`, so `r = rk_0`.
- **Join.** `P(F[V])` is the join of `rk_aug` and `P_0`. Its extreme points are `rk_aug` and the extreme points of
  `P_0`. The set of values of `phi_V` is `{1}` if `P_0` is empty, and `[0, 1]` otherwise.
- **Abstract reduced quotient.** Every `rk != rk_aug` gives `rk_0` in `P_0`, which is detecting by
  `simple-group-rank-functions-are-augmentation-or-detecting`. This is the abstract form of [FR] Corollary 1.3(5),
  which [FR] Section 4 recorded as unknown. No idempotent of `R` generating the fixed ideal is needed.
- **Behaviour on `P_0`.** Odd clopen-cycle groups are regular ([FR] Corollary 1.3(4)), and `rk q([x]) = 1` for
  wandering `x` and `q != 0` ([FR] Theorem 2.3). By [CG] Theorem 1.1 (PASS by `w3-vf-linear`), `rk_0` is regular on every finite subgroup.

### 1.4 Calibration: splitting is not formal

- **Example.** Let `G = Z = <g>` over any field, `sigma(g) = [[1, 1], [0, 1]]`, `rk = rank sigma / 2`, and
  `y = 1 - [g]`. Then `phi_G = 1/2` and `rk_0 = 2 rk - rank eps`.
- **What breaks.** `rk_0(y) = 1`, `rk_0(y^2) = 0`, and for `B = [[y, 1], [0, y]]` we get `rk(B) = 1`,
  `rank eps(B) = 1`, so `rk_0(B) = 1 < rk_0(y) + rk_0(y) = 2`. The upper-triangular axiom fails on this 2 x 2 matrix.
- **Same numbers:** `Z/2` in characteristic two on its regular module, with `y = 1 + [g]`.
- **Why `V` is different.** A Jordan block coupling the trivial part to the rest would give
  `rk(e_P (1 - [g])) >= c > 0` for all `P`, against Lemma 1.2. The input that separates `V` from `Z` is the torsion
  constant being the fixed rank for both `rk` and `rk*`.

## 2. Models

**Corollary 2.1.** Let `M = prod_(k -> omega) M_(n_k)(F) / N_rk` and `sigma : V -> M^x` with `0 < phi_V < 1`. There
is an idempotent `f` in `M` with `sigma(g) f = f sigma(g) = f` for every `g` and `rk f = phi_V`. Then

```text
sigma(g) = f + (1 - f) sigma(g) (1 - f),
```

`sigma_0(g) = (1 - f) sigma(g)(1 - f)` is a model into the rank ultraproduct `(1 - f) M (1 - f)` with rank
`rk/(1 - phi_V)`, its rank function is `rk_0`, and `phi_V(sigma_0) = 0`.

*Proof.*
- **Cauchy.** Take nested `T_1 < T_2 < ...` from [FR] Theorem 1.2, and let `e_k = sigma(e_(T_k))`. Since
  `e_(k+1) = e_k e_(k+1) = e_(k+1) e_k`, `e_k - e_(k+1)` is an idempotent orthogonal to `e_(k+1)`, of rank
  `(1 - phi)(p^(-k) - p^(-k-1))`.
- **Limit.** Metric ultraproducts are complete, so `e_k -> f`. Rank continuity of products makes `f` idempotent with
  `rk f = phi`.
- **Invariance.** `rk(sigma(g) f - f) <= rk((1 - sigma(g)) e_k) + rk(f - e_k) -> 0` by Lemma 1.2, and the row bound
  gives `f sigma(g) = f`. So `f sigma(g)(1 - f) = 0 = (1 - f) sigma(g) f`, which is the displayed form, and `sigma_0`
  is multiplicative.
- **Corner.** `f` lifts to idempotents `f_k`. For a matrix `x`, let `E` project onto the generalized `1`-eigenspace
  `U` along the sum `W` of the other primary components. Then `rank(x - E) = rank((x - 1)|U) + rank(x|W) =
  rank(x^2 - x)`, since `x|U` and `(x - 1)|W` are invertible. So the corner is
  `prod_omega M_(rank(1 - f_k))(F) / N_rk`.
- **Rank function.** `sigma(A) = eps(A) f + (1 - f) sigma(A)(1 - f)`, so (S3') gives
  `rk(A) = phi rank eps(A) + rk((1 - f) sigma(A)(1 - f))`. ∎

**Corollary 2.2 (gates).**
- **Binary** (`thompson-v-has-no-nontrivial-f2-rank-model`). Equivalent to: no characteristic-two model has
  `phi_V = 0`. By [TS] and [FR] Theorem 1.2 that means `rk(e_P) = 1/|P|` on clopen-cycle groups, and with [CG]
  Corollary 1.2 it means `rk(1 + sigma(t)) = 1/2`. The gate node's "Reduced models" line loses its [matricial] caveat.
- **Ternary** (`thompson-v-ternary-rank-functions-are-augmentation`). Equivalent to: `P_0(F_3[V])` is empty.
- **Extension questions** (w6-v-extend, w7-hnn-cocycle). A question about extending `V`-detecting rank functions can
  be posed on `P_0` alone, since every detecting `rk` is `phi_V rk_aug + (1 - phi_V) rk_0` and `rk_aug` extends to
  any augmented algebra. Whether an extension of `rk_0` gives one of `rk` is not checked here.
- **What a counterexample is.** A characteristic-two model with `phi_V = 0` is injective (`V` is simple) and displaces
  every `g != 1` uniformly (`thompson-v-rank-models-displace-every-element-uniformly`). So it is an `F_2`-linear sofic
  approximation of `V`, and a counterexample never needs a trivial summand.

## 3. The configuration `<x_0, x_1, t>`

**Setting.**
- **Generators.** `x_0 : 00z -> 0z, 01z -> 10z, 1z -> 11z`. `x_1` is the identity on `[0]` and `x_0` transported to
  `[1]`: `100z -> 10z, 101z -> 110z, 11z -> 111z`.
- **Fixed points.** `F = <x_0, x_1>` fixes `0^inf` and `1^inf`.
- **Subgroups.** `V_c` is the union of the `V_O` over clopens `O` avoiding both points, and `V_(0,1)` is the stabilizer
  of both. The germ map `V_(0,1) -> Z^2` records the log-slopes at `0^inf` and `1^inf`, and its kernel is `V_c`.

**Proposition 3.1.** Let `t` be a clopen transposition and `H = <x_0, x_1, t>`.
1. If `t` fixes `0^inf` or `1^inf`, then `H` fixes it too, so `H != V`.
2. If `t = [a] <-> [b]` by prefix replacement, with neither cylinder containing `0^inf` or `1^inf`, then
   `H = V_(0,1) = F V_c`. It maps onto `Z^2` (`x_0 -> (1, -1)`, `x_1 -> (0, -1)`, `t -> (0, 0)`), and it contains
   `V_O ≅ V` for every clopen `O` avoiding both points.
3. For `pi_0 = [0] <-> [10]` (`0z <-> 10z`, fixing `[11]`), `V_c <= H <= Stab_V(1^inf)`.
4. For the half rotation `[0] <-> [1]`, `H <= T`.

*Proof.*
- **(1) and (4).** `F` fixes both points and preserves the cyclic order.
- **(2), conjugates.** Suppose `[c] < [d]` are interior cylinders with the same adjacency as `[a] < [b]`. Match the
  left, middle and right complements by order-preserving prefix bijections. This gives `f` in `F` equal to `a -> c` on
  `[a]` and `b -> d` on `[b]`, so `f t f^(-1) = [c] <-> [d]`.
- **(2), all interior transpositions.** For disjoint cylinders, `(c e)(e d)(c e) = (c d)` with prefix maps, and this
  converts between adjacency types. So `H` contains every interior cylinder transposition.
- **(2), `V_c`.** Clopen transpositions supported in `O` generate the simple group `V_O ≅ V` ([FR] Lemma 1.1), and each
  is a product of commuting cylinder transpositions. So `V_c <= H`.
- **(2), equality.** For `g` in `V_(0,1)`, choose `f` in `F` with the same germs, which is possible because
  `x_0, x_1 -> (1, -1), (0, -1)` is a basis. Then `f^(-1) g` lies in `V_c`.
- **(3).** `x_0^(-1) pi_0 x_0 = [00] <-> [01]` and `x_1^(-1) pi_0 x_1 = [0] <-> [100]`. Conjugating the latter by
  `pi_0` gives `[10] <-> [00]`, and conjugating that by `[00] <-> [01]` gives `[01] <-> [10]`, which is interior.
  Now argue as in (2). ∎

**Corollary 3.2 (firewall).**
- **Soficity.** In cases 2 and 3, `H` contains `V_O ≅ V` and lies in `V`, so `H` is sofic iff `V` is.
- **Consequence for identities.** An identity over `F_2[V]` forces `rk(1 + [t]) != 1/2` in every model only if the
  group generated by its support is not sofic. [FW] Theorem 1.2 builds permutation-module ranks on any sofic
  configuration, with `rk(1 + [t]) = 1 - 1/2`.
- **What `<x_0, x_1, t>` offers.** It is not known to be sofic because it contains `F` ([FW] Section 2.3) and `V_O`. The
  route is no smaller than `V` itself: finitely many conjugates of `t` already generate some `V_O`, because `V_O` is
  finitely generated and lies in the normal closure of `t` in `H`.

**Attempts at a forcing identity** (where each dies).
- **Self-similarity.** For non-adjacent interior `t = [a] <-> [b]`, `t = t_0 t_1` with `t_i = [ai] <-> [bi]` commuting
  and `F`-conjugate to `t`. In characteristic two, `1 + [t] = (1 + [t_0]) + [t_0](1 + [t_1])`. The Klein group
  `<t_0, t_1>` is pinned by `phi_V` ([CG] Theorem 1.1), and conjugation only gives `rk(1 + [t_i]) = rk(1 + [t])`.
  Values with `phi_V = 0` satisfy both.
- **Dilation.** If `t` is supported in a wandering clopen of `x_0`, then `<x_0, t> ≅ Z/2 wr Z` ([FW] Proposition 2.1),
  which is amenable and hence inert.
- **The live step is not reached.** No identity was found whose support generates a group containing `V_O` and that
  is not already implied by the finite-subgroup law, unit invariance and [FR] Theorem 2.3.

**No source of a `phi_V = 0` model** (Corollary 2.2 makes such a model an `F_2`-linear sofic approximation).
- **Leavitt algebra.** `L_(F_2)(1, 2)` contains `F_2[V]` but has no Sylvester rank function, because
  `1 = x_1 y_1 + x_2 y_2` with each summand equivalent to `1`.
- **Measures.** `V` preserves no probability measure on `X`. Proper clopens with nonempty complement are `V`-equivalent,
  so `mu[0] = mu[00] = mu[01]` forces `mu[0] = 0`. So there is no normalized permutation-module rank along `X`.
- **Standard closures.** `V` is finitely presented, simple and infinite, so it is not residually finite, not LEF
  (finitely presented LEF groups are residually finite) and not linear (Malcev). Soficity is open (`thompson-v-is-sofic`).
- **Endomorphism-invariant models.** The `E_infinity` model ([CG] Section 3) and the `p`-cycle tree models of
  w7-v-cycle-c3 (`2e8bf4f44`) fail the order-characteristic law, so they are not rank functions on `F[V]`.

## 4. Where it stops

- **Proved** (candidates, held open): Lemma 1.2, Theorem 1.4, Corollaries 1.5 and 2.1, Proposition 3.1.
- **Refuted:** nothing. Splitting was decided positively. No violating matrix exists over `F[V]`; for `Z` and `Z/2`
  the smallest violation is `[[y, 1], [0, y]]`.
- **Open:** both gates, now in the form "`P_0` is empty" or "no model with `phi_V = 0`". There is no forcing identity
  at `<x_0, x_1, t>` and no `phi_V = 0` model.
- **After a PASS:** route `v-rank-split-augmentation-plus-reduced-proof`, requiring
  `v-rank-torsion-constant-equals-global-fixed-rank` and `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`. It does
  not need `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`.
