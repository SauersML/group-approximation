# Sylvester rank functions on Leavitt unit group algebras: ideal quotients, compressions, and a class-(A) defect chain

Lane `w5-regular-rankfn`, 2026-09-12. Target: `sylvester-rank-functions-on-leavitt-units-are-regular`.

Sources on main:
- [AUD] = `research/artifacts/rank-gate-axiom-audit-2026-09-12.md` (classes A, A', B; Proposition 4.1; Remark 4.2);
- [DG] = `research/artifacts/two-root-defect-descent-gap-2026-09-12.md` (Facts 1.1–1.3, Lemma 3.0, Theorem 3.1,
  Proposition 4.1);
- [SYL] = `research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md`.

## 0. Summary

**Target status: not decided.** Whether every Sylvester matrix rank function on `F_2[R^x]` is regular stays OPEN.
- **Literature.** No local source decides whether every Sylvester matrix rank function on a ring is regular. I
  recall that this is posed as an open question in Jaikin-Zapirain's surveys, but I read no copy here, so that is
  UNVERIFIED and no node depends on it.
- **Classical facts I use only as remarks** (not re-read): on a von Neumann regular ring, Sylvester matrix rank
  functions are the pseudo-rank functions (Goodearl, *Von Neumann Regular Rings*, Ch. 16); rank functions through
  matrix algebras over division rings are regular.

**What this artifact does instead: it removes regularity from most of the defect chain.** The defect gap and the
two-sided geometric descent hold for EVERY Sylvester rank function on `F_2[R^x]` (Theorem 4.1), with the
descent's lower constant weakened from `c_*` to `c_0 / m_0`. Tools, all class (A):
1. **Ideal quotients** (Lemma 1.1): a finitely generated two-sided ideal `J` turns a rank function `rho` into a
   rank function `rho_J(A) = rho(X_J A) / rho(X_J)`.
2. **Commuting compressions** (Lemma 1.2): an element `d` commuting with a subring `C` gives a rank function
   `rho_d(A) = rho(A d) / rho(d)` on `C`.
3. **The augmentation quotient of a perfect group is fixed-point-free** (Corollary 2.3), because `omega = omega^2`.
   This is the class-(A) fixed-point-free normalization that [AUD] Remark 4.2 said had no analogue without principal
   right ideals.
4. **Quasi-globality** (Proposition 3.1): if a subgroup's compression semigroup generates `G` and it normally
   generates `G`, its fixed "kernel" is `1/m`-dense, with `m` from normal generation.

**What still needs regularity** (Section 5): exact globality (constant `1`, not `1/m_0`), and kernel corners.
Those are exactly the inputs of the exact lower descent and of near-minimal multiplicativity ([DG] Proposition 4.1),
which the submultiplicativity route needs. Both are opened as class-(A) claims.

## 1. Ideal quotients and commuting compressions

**Axioms.** A Sylvester matrix rank function `rho` on a unital ring `S` assigns `rho(A) >= 0` to every rectangular
matrix over `S`, with
- (S1) `rho(0) = 0`, `rho(1) = 1`;
- (S2) `rho(AB) <= min(rho(A), rho(B))`;
- (S3) `rho(A (+) B) = rho(A) + rho(B)`;
- (S4) `rho([[A, C], [0, B]]) >= rho(A) + rho(B)`.

**Consequences used below.**
- Invertible matrices and permutations on either side preserve `rho` (S2 both ways).
- *Stacking.* For `A` and `B` with the same number of columns `n`, `[A; B] = (A (+) B)·[I_n; I_n]`, so
  `rho([A; B]) <= rho(A) + rho(B)`.
- *Sylvester inequality.* For `A` of size `m x n` and `B` of size `n x p`, `rho(A) + rho(B) <= n + rho(AB)`.
  Proof: `[[A, 0], [I_n, B]]` is carried by invertible row and column operations to `[[0, -AB], [I_n, 0]]`, of rank
  `n + rho(AB)`; permuting blocks gives the upper triangular `[[B, I_n], [0, A]]`, of rank at least
  `rho(A) + rho(B)` by (S4). In particular a square-zero `1 x 1` element has `rho <= 1/2`.
- *Frobenius inequality.* `rho(AB) + rho(BC) <= rho(B) + rho(ABC)`. Proof: `[[B, BC], [AB, 0]]` is carried to
  `[[B, 0], [0, -ABC]]` by row and column operations, and permuting columns gives the upper triangular
  `[[BC, B], [0, AB]]`.

**Notation.** For a `k x 1` column `X` and a matrix `A` with `m` rows, write `X A := (X (x) I_m) A`, the
`km x n` matrix whose block `i` is `x_i A`.

**Lemma 1.1 (ideal quotients).** Let `J` be a two-sided ideal of `S` generated as a left ideal by `x_1, ..., x_k`,
`X = (x_1, ..., x_k)^T`, and `rho(X) > 0`. Put `rho_J(A) := rho(X A) / rho(X)`.
1. `rho_J` is a Sylvester matrix rank function on `S`.
2. `rho_J` does not depend on the chosen generators.
3. If `J = J^2`, then `rho_J(X Z) = rho_J(Z)` for every matrix `Z`.

*Proof.*
1. (S1) `rho_J(1) = rho(X)/rho(X) = 1`. Since `J` is a two-sided ideal, `x_i a` lies in `sum_j S x_j` for every
   `a` in `S`, so for every `m x n` matrix `A` there is a matrix `Y_A` with `X A = Y_A X` (as `km x kn` matrices,
   `X (x) I_m · A = Y_A · X (x) I_n`).
   - (S2) `rho(X AB) = rho(Y_A X B) <= rho(X B)`, and `rho(X AB) <= rho(X A)`.
   - (S3), (S4): `X (A (+) B)` and `X [[A, C], [0, B]]` are row permutations of `(X A) (+) (X B)` and of
     `[[X A, X C], [0, X B]]`.
2. Two generating columns satisfy `X' = Y X` and `X = Y' X'`, so `rho(X' A) <= rho(X A) <= rho(X' A)`.
3. `J = J^2` gives `x_l = sum_(i,j) b_(lij) x_i x_j`, that is `X = Y (X X)` where `X X` is the column of the
   `x_i x_j`. So `rho(X Z) <= rho(X X Z) <= rho(X Z)`, and `rho_J(X Z) = rho(X X Z)/rho(X) = rho(X Z)/rho(X)
   = rho_J(Z)`. QED

**Remark 1.1' (consistency with regular rings, sketch).** If `rho = rk_U o phi` with `U` faithful regular and
`eU` the right annihilator of `phi(J)`, then `phi(S) eU <= eU` (as `J S <= J`), so `(1-e) phi(a) e = 0`, and
`rho_J(A) = rk((1-e) phi(A) (1-e)) / rk(1-e)`: the model on the quotient by the `J`-annihilated part.

**Lemma 1.2 (commuting compressions).** Let `C` be a unital subring of `S` and `d` a `k x k` matrix over `S` such
that `(c I_k) d = d (c I_k)` for every `c` in `C`, with `rho(d) > 0`. For a matrix `A` over `C` of size `m x n`
put `rho_d(A) := rho((A (x) I_k)(I_n (x) d)) / rho(d)`. Then `rho_d` is a Sylvester matrix rank function on `C`.

*Proof.* Write `A^k = A (x) I_k` and `d_n = I_n (x) d`; commutation gives `A^k d_n = d_m A^k`.
- (S1) `rho_d(1) = 1`.
- (S2) `rho(A^k B^k d_p) = rho(A^k d_n B^k) <= rho(A^k d_n)`, and `rho(A^k B^k d_p) <= rho(B^k d_p)`.
- (S3), (S4): block computations as in Lemma 1.1. QED

**Remark 1.2'.** In a faithful regular rank ring, `rho_d` is the rank of the corner model on the image of `d`,
which [DG] Theorem 3.1 builds with an idempotent `q` with `qU = dU`. Lemma 1.2 needs no idempotent.

## 2. The augmentation quotient of a perfect group

Setting: `K` a field, `G` generated by `g_1, ..., g_r`, `B = K[G]`, `omega` the augmentation ideal,
`X = (g_1 - 1, ..., g_r - 1)^T`.

**Lemma 2.1.**
1. `omega` is generated as a left ideal by the `g_i - 1`.
2. `omega/omega^2` is a quotient of `K (x) G^ab`. So if `G` is perfect, `omega = omega^2`.
3. For a Sylvester rank function `rho` on `B`, `rho(X) = 0` iff `rho` is the augmentation rank.

*Proof.*
1. `gh - 1 = g(h-1) + (g-1)` and `g^-1 - 1 = -g^-1 (g - 1)`, so by induction on word length every `h - 1` lies in
   `sum_i B (g_i - 1)`.
2. `(g-1)(h-1)` lies in `omega^2`, so `h -> h - 1` is a homomorphism `G -> omega/omega^2` whose image spans it;
   it factors through `G^ab`.
3. Each `g_i - 1` is a row of `X`, so `rho(g_i - 1) <= rho(X) <= sum_i rho(g_i - 1)` (stacking). By 1 every
   `h - 1` is `Y X` for a row `Y`, so `rho(X) = 0` kills every `1 - [h]`. By
   `simple-group-rank-functions-are-augmentation-or-detecting` (its first part: the elements with
   `rho(1 - [x]) = 0` form a normal subgroup and `rho` factors through the quotient), `rho` is then the augmentation
   rank. Conversely the augmentation rank kills `X`. QED

**Definition 2.2.** For a non-augmentation `rho` on `K[G]`, `rho_omega := rho_J` with `J = omega` and the column
`X` (Lemma 1.1; it is independent of the generators).

**Corollary 2.3 (the fixed-point-free quotient).** Let `G` be perfect and `rho` non-augmentation. Then:
1. `rho_omega` is a Sylvester matrix rank function, and it is not the augmentation rank;
2. `rho_omega(X Z) = rho_omega(Z)` for every matrix `Z` ("fixed-point-free");
3. `max_i rho_omega(1 - [g_i]) >= 1/r`.

*Proof.* 1 and 2 are Lemma 1.1 with Lemma 2.1(2). In particular `rho_omega(X) = rho_omega(I_1) = 1`, so
`rho_omega` is not the augmentation rank, and stacking gives 3. QED

**Remark 2.4.** For `rho = rk_U o phi` with `U` faithful regular and `fU = Fix_r(phi(G))`, Remark 1.1' makes
`rho_omega` the normalized rank of `sigma_W = (1-f) sigma (1-f)`, the fixed-point-free quotient of [DG] Lemma 2.1.
Corollary 2.3(2) is the class-(A) shadow of "`sigma_W` has no fixed vectors", and its proof uses perfection through
`omega = omega^2`, as [DG] does through the abelian square-zero rest.

## 3. Quasi-globality from normal generation

Setting: `G`, `B = K[G]` as above; `Gamma <= G` generated by a finite set `S`, `X_S = (s - 1 : s in S)^T`;
`P_Gamma = { g in G : g Gamma g^-1 <= Gamma }`.

**Proposition 3.1.** Suppose `<P_Gamma> = G` and `Gamma` normally generates `G`.
1. There are `h_1, ..., h_m` in `G` and a matrix `Y` over `B` with `X = Y · [X_S h_1; ...; X_S h_m]`.
2. For every Sylvester rank function `psi` on `B`, every `h` in `G` and every matrix `Z`,
   `psi(X_S h Z) = psi(X_S Z)`.
3. If `psi(X Z) = psi(Z)` for every `Z`, then `psi(X_S Z) >= psi(Z)/m` for every `Z`.

*Proof.*
1. The two-sided ideal `B omega_Gamma B` contains `h(gamma - 1)h^-1 = h gamma h^-1 - 1`, and `ab - 1 =
   a(b-1) + (a-1)`, so it contains `n - 1` for every `n` in the normal closure of `Gamma`, which is `G`. Each
   `g_i - 1` is a finite sum of terms `b (s - 1) c` with `c` in `B`; expanding `c` over group elements gives
   finitely many right translates `h_j`.
2. Let `h` be in `P_Gamma`. Each `h s h^-1` lies in `Gamma`, so by Lemma 2.1(1) for `Gamma`,
   `X_(hSh^-1) = Y_h X_S` with `Y_h` over `K[Gamma]`. Also `X_(hSh^-1) = (h (x) I) X_S h^-1`, so
   `psi(Y_h X_S) = psi(X_S)`. The Frobenius inequality with `(A, B, C) = (Y_h, X_S, Z)` gives
   `psi(X_S Z) <= psi(Y_h X_S Z) <= psi(X_S Z)`. So
   `psi(X_S Z) = psi((h (x) I) X_S h^-1 Z) = psi(X_S h^-1 Z)` for all `Z`, and with `Z = hW`,
   `psi(X_S h W) = psi(X_S W)`. The set of `h` with this invariance is a group containing `P_Gamma`, hence all
   of `G`.
3. `psi(Z) = psi(X Z) <= psi([X_S h_1 Z; ...; X_S h_m Z]) <= sum_j psi(X_S h_j Z) = m psi(X_S Z)`. QED

**Remark 3.2.** In a faithful regular rank ring the same hypotheses give `psi(X_S Z) = psi(Z)` exactly
([AUD] Theorem 2.2(2)): the fixed right ideal of `Gamma` is principal, `P_Gamma`-invariant, and pointwise fixed by
the normal closure. The loss `1/m` is what principal right ideals buy back.

**Application.** For `G = R^x` with `R = L_(F_2)(1,2)` and `Gamma_0 = iota_0(R^x)`, which equals the nine-leaf
`EL_alpha(R)` as a set ([DG] Lemma 3.0): the compressors together with `Gamma_0` lie in the compression semigroup
of `Gamma_0` and generate `R^x` (`leavitt-unit-group-carries-nontrivial-rigid-defect` and
`leavitt-packet-linear-sofic-kills-kaplansky-target`, as used in `leavitt-rank-models-fixed-ideals-proof`), and
`Gamma_0` normally generates `R^x` (`binary-leavitt-unit-group-is-simple`). The invariance in Proposition 3.1(2)
holds for `h` and `h^-1` together, so either convention for the compression semigroup gives `<P_Gamma> = G`. Fix `m_0` from Proposition 3.1(1).
For a proper cylinder `A`, `Gamma_A = u Gamma_0 u^-1` for some `u` in `V` ([DG] Fact 1.2), with the same `m_0`.

## 4. The defect gap and geometric descent for every Sylvester rank function

Setting: `R = L_(F_2)(1,2)`, `G = R^x` generated by `g_1, ..., g_4` (`binary-leavitt-unit-group-four-generated`),
`R^x = EL_3(R)` through the three-leaf prefix code ([SYL] Section 0), `N_ab = [x_ab(1)] - 1` and
`D = N_23 N_12` in `F_2[R^x]`, and `N^A_ab = iota_A(N_ab)`, `D_A = iota_A(D)` for a proper prefix `A`.
`c_0 := c^Syl(1/4)` is the constant of `sylvester-rank-functions-have-a-uniform-two-root-defect-gap`, and `m_0` is
the constant of Section 3 for `Gamma_0 = iota_0(R^x)`.

**Theorem 4.1.** Let `rho` be a Sylvester matrix rank function on `F_2[R^x]` other than the augmentation rank.
1. **Gap.** `c_0 <= rho_omega(D_A) <= 1/2` for every proper prefix `A`.
2. **Descent.** For pairwise disjoint proper cylinders `A_1, ..., A_k` with proper union, put
   `f(k) = rho_omega(D_(A_1) ... D_(A_k))`. It depends only on `k`, because such tuples are conjugate by units of
   `V` ([DG] Fact 1.2) and unit conjugation preserves `rho_omega`. Then `(c_0/m_0) f(k) <= f(k+1) <= f(k)/2`, so
   `c_0 (c_0/m_0)^(k-1) <= f(k) <= 2^(-k)`.

*Proof.*
1. `R^x` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`). By Corollary 2.3, `rho_omega` is a Sylvester
   rank function, not the augmentation rank, with `max_i rho_omega(1 - [g_i]) >= 1/4`. The uniform gap, applied to
   `rho_omega`, gives `rho_omega(D_A) >= c_0`. For the upper bound, `x_12(1)` is an involution in characteristic two
   ([DG] Fact 1.3), so `(N^A_12)^2 = 0` in `F_2[R^x]`. The Sylvester inequality gives `rho_omega(N^A_12) <= 1/2`,
   and `D_A = N^A_23 N^A_12` gives `rho_omega(D_A) <= rho_omega(N^A_12)`.
2. Take a `(k+1)`-tuple as in the statement, put `P = D_(A_1) ... D_(A_k)` and `B = A_(k+1)`; by induction
   `f(k) > 0`. The subring `C = iota_B(F_2[R^x])` commutes with `P`, since units on disjoint cylinders commute
   ([DG] Fact 1.2). Lemma 1.2 gives the Sylvester rank function `tau(A) := rho_omega(iota_B(A) P) / rho_omega(P)`
   on `F_2[R^x]`. With `E := D_1000`, `iota_B(E) = D_(B1000)`, and `(A_1, ..., A_k, B1000)` is again a tuple of
   pairwise disjoint proper cylinders with proper union, so `tau(E) = f(k+1)/f(k)`.
   - **Upper.** `N^1000_12` is square-zero, so `tau(N^1000_12) <= 1/2` by the Sylvester inequality, and
     `tau(E) <= tau(N^1000_12)`.
   - **Lower.** `tau(X) = rho_omega(X_(S_B) P) / rho_omega(P)`, where `S_B = iota_B({g_i})` generates
     `Gamma_B = iota_B(R^x)`. `rho_omega` is fixed-point-free (Corollary 2.3(2)), so Proposition 3.1(3) gives
     `tau(X) >= 1/m_0`. Hence `tau` is not the augmentation rank (Lemma 2.1(3)), and part 1 for `tau` at the prefix
     `1000` gives `tau_omega(E) >= c_0`. By (S2), `tau(E) >= tau(X E) = tau(X) tau_omega(E) >= c_0/m_0`. QED

**Remark 4.2 (comparison).** [DG] Theorem 3.1, and its regular form [AUD] Theorem 3.1(3), have lower constant
`c_*` in place of `c_0/m_0`: there the corner model `tau` is fixed-point-free by exact globality, so `tau(X) = 1`.
Everything else in Theorem 4.1 is the regular argument with idempotent corners replaced by `rho_omega` and `rho_d`.
In particular the nested defect pieces decay geometrically in both directions for every Sylvester rank function,
not only for regular ones.

## 5. Where it stops

**5.1 Exact globality.** The class-(A) form of [DG] Lemma 3.0 is `rho_omega(iota_B(X) Z) = rho_omega(Z)` for
every `Z`. Proposition 3.1 gives invariance under `G` and the bound `>= rho_omega(Z)/m_0`. The regular proof ends
with "a principal right ideal containing a conjugate of equal rank equals it". Its class-(A) form would be: if
`psi(M_1 W) = psi(M_2 W)` for all `W`, then `psi([M_1; M_2] W) = psi(M_1 W)`. In a regular rank ring that is
"equal kernels", tested on the projection onto a kernel; for a bare Sylvester rank function there is no such
projection, and I found no proof. Open claim: `sylvester-leavitt-kazhdan-fixed-ideals-are-global`.

**5.2 Kernel corners.** [DG] Proposition 4.1 compresses to the right annihilator `K` of `P`. Lemma 1.1 compresses
to quotients by two-sided ideals and Lemma 1.2 to images of commuting elements. A right annihilator of a
non-central `P` is neither, and the triangular axiom only gives `rho(A) >= rho(A on K) + rho(A on U/K)`, an upper
bound on the kernel part. So near-minimal multiplicativity is not class (A) yet. Open claim:
`sylvester-near-minimal-leavitt-defects-are-multiplicative`.
- **Payoff.** Suppose strict submultiplicativity holds in Sylvester form:
  `rho_omega(D_A D_B) <= theta rho_omega(D_A) rho_omega(D_B)` with `theta < 1` for every non-augmentation `rho`
  and disjoint `A`, `B`. With the open claim, [AUD] Consequence 3.2's computation applies to a near-minimizer,
  which exists by compactness of the Sylvester rank functions ([AUD] Proposition 4.1). So every Sylvester rank
  function kills `D`, which is `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`, with no regularity.

**5.3 Envelopes: two calibrations.**
- **Completion is not an envelope.** On `K[t, t^-1] = K[Z]`, the rank through `K(t)` gives every nonzero element
  rank `1`. The rank metric is discrete, so the completion is `K[t, t^-1]` itself, which is not regular. Yet this
  rank function is regular, through `K(t)`. A regular envelope has to localize, not complete; the rank completion
  of `F_2[R^x] / I_rho` settles nothing by itself.
- **Universal regularization (sketch, no claim).** Let `Reg(A)` be the colimit of iterated free adjunctions of
  quasi-inverses (`a y a = a`, `y a y = y`) for all elements. It is regular, and every map `A -> U` into a regular
  ring extends to `Reg(A)` after choosing quasi-inverses in `U`. So `rho` is regular iff it extends to a Sylvester
  rank function on `Reg(A)` (then divide by the null ideal). This restates the target: the open point is whether a
  rank function always extends along one free adjunction of a quasi-inverse, which already asks for range
  idempotents of positive rank.

**5.4 What the Sylvester binary gate now needs**, by the submultiplicativity route: a Sylvester-form strict
submultiplicativity bound plus `sylvester-near-minimal-leavitt-defects-are-multiplicative`. The target claim
(regularity of every rank function) is a second way to supply the second input, through the regular chain.
