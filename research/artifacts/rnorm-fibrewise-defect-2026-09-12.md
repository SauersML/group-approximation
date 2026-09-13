# The unbounded-multiplicity defect sector is zero in every Koopman model

Date: 2026-09-12. Lane `rnorm-fibrewise-defect` (swarm 9).

- **Target:** the RNORM crux left by `rnorm-jones-index`
  (`jones-index-blind-on-unbounded-defect-sector`). Either prove `Q = P - P' = 0`
  on `H_inf` fibre by fibre over `A_rho`, or show that no argument that also works
  for amenable hosts can prove it.
- **Outcome:** `Q = 0` holds exactly, but for a simpler reason than the brief
  expected: `H_inf = 0` in every sofic model.
  - In the Koopman representation of any measure-preserving action, a
    `d`-dimensional type `rho` has multiplicity at most `d` over the algebra of
    invariant functions.
  - So `End_A(W_rho)` is a finite von Neumann algebra, and unitarily conjugate
    nested projections in it coincide.
  - No (T) enters on the fibres, and nothing is disintegrated. Property (T) and
    the nonsofic quotient enter only through type fixing and block invariance,
    which put `W_rho(u)` in `End_A(W_rho)`.
  - Landed as `unbounded-defect-sector-vanishes-in-koopman-models`.
- **Consequence for RNORM:** nothing positive.
  - `Q = 0` is automatic, so it cannot be the mechanism.
  - The surviving shape of `rnorm-kazhdan-projection-sizes-2026-09-12.md`
    Section 4 is empty.
  - Theorem B there now covers the whole finite-dimensional isotypic part of
    `sigma|_N`.
  - RNORM and `nonsofic-hyperbolic-group` stay OPEN.

## 0. Setting

This is the setting of `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`.

- **Cover and model.** `1 -> N -> G -> R^x -> 1` is the hyperbolic Leavitt cover,
  `Gamma_hat = pi^-1(EL_alpha(R))`, and `u` is the strict defect compressor.
  `sigma : G -> S_U` is a sofic representation, acting by Koopman unitaries on
  `H = L^2(X_U, mu_U)`.
- **Algebra.** `A = D^N` is the algebra of `sigma(N)`-invariant functions in
  `L^inf(X_U)`, acting by multiplication. Block invariance
  (`kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`) gives
  `D^N = D^G`.
- **Sectors.** For a `d`-dimensional irreducible `rho` of `N`, put
  `W_rho = Hom_N(V_rho, H)` and `H_rho = V_rho (x) W_rho`. Then
  `sigma(g)|_(H_rho) = U_rho(g) (x) W_rho(g)` and `A|_(H_rho) = 1 (x) A_rho`
  (`kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`).
- **Decomposition.** `H = H_b (+) H_wm (+) H_inf`.
  - `H_wm` is the orthocomplement of every finite-dimensional
    `sigma(N)`-subrepresentation.
  - `H_inf` is the part of the isotypic sectors with no nonzero invariant
    `A`-submodule of bounded multiplicity.
- **Defect data.** `P` is the fixed-space projection of `W_rho(Gamma_hat)`, and
  `P' = W_rho(u)^* P W_rho(u)`. The two are nested; relabel so that `P' <= P`, and
  put `Q = P - P'`.

Each `W_rho(g)` is fixed only up to a scalar. Everything below holds for every
choice of scalars, because it uses only that each `W_rho(g)` is a unitary
commuting with `A_rho`.

## 1. Gram densities

**Lemma 1.** Let `N` act on a probability space `(Y, mu)` by automorphisms of the
measure algebra, with Koopman representation `pi` on `L^2(Y)`. Let
`A = L^inf(Y)^N` act by multiplication, and let `rho` be `d`-dimensional
irreducible with orthonormal basis `e_1, ..., e_d`. For `T, S in W_rho` put

```text
g_(T,S) = sum_k (T e_k) . conj(S e_k)   in L^1(Y).
```

1. `g_(T,S)` is `N`-invariant, so it is measurable for the invariant sigma-algebra.
2. `<aT, S>_W = (1/d) int a g_(T,S) dmu` for `a in A`, where the inner product on
   `W_rho` is the one that makes `V_rho (x) W_rho -> H_rho` unitary. So `g_(T,S)`
   is the density of `a -> <aT, S>` and depends only on the `A`-module structure.
3. For `T_0, ..., T_d in W_rho`, `det [g_(T_i,T_j)] = 0` almost everywhere.

*Proof.*
1. Koopman operators are multiplicative and commute with complex conjugation on
   measurable functions. Intertwining gives `pi(n) T e_k = sum_j rho(n)_(jk) T e_j`.
   With the row vector `F_T = (T e_1, ..., T e_d)`, this reads
   `pi(n) F_T = F_T rho(n)`. So

   ```text
   pi(n) g_(T,S) = F_T rho(n) rho(n)^* F_S^* = F_T F_S^* = g_(T,S).
   ```

   The level sets of an invariant function are invariant.
2. By Schur, `S^* T = c . 1` on `V_rho`, with `c = (1/d) sum_k <T e_k, S e_k>`. So
   `<Tv, S v'> = c <v, v'>`, and `<T, S>_W = c = (1/d) int g_(T,S)`. For `a in A`,
   `aT` is again an intertwiner and `g_(aT,S) = a g_(T,S)`. Two invariant `L^1`
   functions with the same integral against every `a in A` agree almost everywhere.
3. Pointwise, `[g_(T_i,T_j)(y)]` is the Gram matrix of the `d+1` vectors
   `F_(T_i)(y)` in `C^d`. ∎

## 2. Multiplicity at most `dim rho`

**Lemma 2.** In the setting of Lemma 1, let `xi_0, ..., xi_d in W_rho` satisfy
`<a xi_i, xi_j> = delta_ij <a xi_0, xi_0>` for all `a in A_rho`. Then `xi_0 = 0`.
Consequently `A_rho` has multiplicity at most `d` on `W_rho`, and
`End_A(W_rho) = A_rho'` is a finite type I von Neumann algebra.

*Proof.*
1. By Lemma 1.2, `g_(xi_i,xi_j) = delta_ij g_(xi_0,xi_0)` almost everywhere, so the
   Gram determinant equals `g_(xi_0,xi_0)^(d+1)`.
2. By Lemma 1.3 it vanishes almost everywhere. But `g_(xi_0,xi_0) >= 0` and
   `int g_(xi_0,xi_0) = d ||xi_0||^2`, so `xi_0 = 0`.
3. **Multiplicity.** `A_rho'` is type I, with center `A_rho''`. Suppose it had a
   homogeneous summand of degree `k >= d+1`, possibly infinite.
   - Choose orthogonal abelian projections `p_0, ..., p_d` in it, and partial
     isometries `v_i in A_rho'` with `v_i^* v_i = p_0` and `v_i v_i^* = p_i`.
   - Take `xi != 0` in `p_0 W_rho` and put `xi_i = v_i xi`.
   - `A_rho` is central in `A_rho'`, so `<a xi_i, xi_j> = <a v_j^* v_i xi, xi> =
     delta_ij <a xi, xi>`.

   This contradicts the first part. ∎

This is the relative, matrix-valued form of the classical fact that the
eigenvalues of an ergodic measure-preserving transformation are simple.

## 3. Conjugate nested projections coincide

**Lemma 3.** Let `V` be a unitary on `W_rho` and `P` a projection, both commuting
with `A_rho`, with `V^* P V <= P`. Then `V^* P V = P`. The same holds if
`P <= V^* P V`.

*Proof.*
1. Put `P_k = V^(*k) P V^k`. This sequence is decreasing, so the differences
   `Q_k = P_k - P_(k+1) = V^(*k) Q V^k` are pairwise orthogonal, and each commutes
   with `A_rho`.
2. Take `xi in Q W_rho` and put `xi_k = V^(*k) xi in Q_k W_rho`.
   - For `i != j`, `<a xi_i, xi_j> = <Q_j Q_i a xi_i, xi_j> = 0`.
   - `<a xi_k, xi_k> = <V^k a V^(*k) xi, xi> = <a xi, xi>`.
3. Lemma 2 applied to `xi_0, ..., xi_d` gives `xi = 0`, so `Q = 0`.
4. If instead `P <= V^* P V`, then `V P V^* <= P`. Apply steps 1–3 to `V^*`. ∎

## 4. The cover

**Theorem.** In the setting of Section 0, for every sofic representation `sigma`:

1. `H_inf = 0`. Every finite-dimensional isotypic sector has bounded
   multiplicity, and `H_b = H (-) H_wm`.
2. `Q = 0` exactly, for every `rho` and every choice of scalars. In the notation of
   `jones-index-blind-on-unbounded-defect-sector`, `Ind(E_P) = 1`.
3. `W_rho(g)` is a scalar on all of `W_rho` for every `g in G`. So for every
   `rho`, `sigma(g)|_(H_rho)` lies in the strong closure of `T . sigma(N)|_(H_rho)`.
   The scalar may depend on `rho`.
4. `Gamma_hat`, `u^-1 Gamma_hat u`, `N` and `G` have the same closed invariant
   subspaces in `H (-) H_wm`. Every finite-dimensional subrepresentation of
   `sigma|_(Gamma_hat)` or of `sigma|_(u^-1 Gamma_hat u)` lies in `H (-) H_wm`.
5. Items 1–4 of `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`
   hold with `H_b = H (-) H_wm`.

*Proof.*
1. `sigma(N)` acts on the Loeb measure algebra. `D_U` is the tracial ultraproduct of
   the diagonals, which is `L^inf(X_U, mu_U)` because every Loeb set agrees almost
   everywhere with an internal set. So `A = D^N` is `L^inf` of the invariant
   sigma-algebra. By Lemma 2, `A_rho` has multiplicity at most `dim rho`
   on all of `W_rho`. So `E = W_rho` is admissible in the definition of `H_b`,
   since it is invariant under `A_rho` and `W_rho(G)`. Hence `H_inf = 0`.
2. Block invariance puts `A` in the commutant of `sigma(u)`. So `1 (x) A_rho`
   commutes with `U_rho(u) (x) W_rho(u)`, and `A_rho` commutes with `W_rho(u)`.
   Each `W_rho(gamma)` commutes with `A_rho`, so its fixed space reduces `A_rho`,
   and `P` commutes with `A_rho`. Lemma 3 with `V = W_rho(u)` gives `P' = P`.
3. Apply item 4 of `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`
   with `E = W_rho` and `m = dim rho`, then item 3 of the same claim.
4. A finite-dimensional `sigma(Gamma_hat)`-invariant subspace is
   `sigma(N)`-invariant, so it lies in `H (-) H_wm`.
   - Let `K` be a closed `sigma(N)`-invariant subspace of `H (-) H_wm`. Its
     projection lies in `sigma(N)'`, and each `P_rho` lies in `sigma(N)''`. So they
     commute, and `K` is the closed sum of the spaces `P_rho K`.
   - Each `P_rho K` is invariant under the strong closure of
     `T . sigma(N)|_(H_rho)`, which contains `sigma(g)|_(H_rho)` by item 3.
5. Items 1–4 there were proved for `H_b`, which item 1 identifies with
   `H (-) H_wm`. ∎

## 5. The brief's three lines

- **(a) Fibrewise (T).** Not needed.
  - Disintegrating over any countably generated part of `A_rho` gives fibres of
    dimension at most `dim rho`.
  - There `Q_omega = 0` is finite-dimensional linear algebra, and the uniform
    spectral gap plays no role.
- **(b) An amenable-host model with `Q != 0`.** No such model exists among Koopman
  models.
  - Lemmas 1–3 use no (T), no soficity and no property of `R^x`. In any
    measure-preserving model where the kernel's invariant algebra commutes with
    the compressor's multiplicity unitary, `Q = 0`.
  - The quasi-regular boundary example shows which hypothesis does the work. Take
    `W = l^2(R^x / EL_alpha(R)) (x) l^2(Nat)` with `A_rho = 1 (x) l^inf(Nat)`, where
    `Nat` is the set of natural numbers.
  - The base coset `delta_0` is fixed by `EL_alpha(R)`. It is not fixed by
    `u^-1 EL_alpha(R) u`, whose orbit through the base coset has at least `2`
    points, because the compression is strict. So `Q != 0` on every fibre.
  - The spectral gap is uniform in the fibre, since `EL_alpha(R)` is Kazhdan.
  - What fails is the Koopman hypothesis. Here `A_rho` has infinite multiplicity,
    which Lemma 2 rules out when `A_rho` comes from the kernel's invariant algebra.
- **(c) Direct-integral measurability.** No obstruction. Lemmas 1–3 read the Gram
  densities as `L^1` functions on the Loeb space. No direct integral, separability
  or standard Borel structure is used.

So (T) does not have to enter on the fibres: the fibres are finite-dimensional,
and a fibre argument has nothing left to prove.

## 6. What this means for RNORM

- **`Q = 0` is free.** It holds in every sofic model, at the cost of type fixing
  and block invariance only, and it is a statement about `sigma(G)` alone.
  - The proposal "force `Q = 0`, then deduce normalization" would therefore be a
    proof of RNORM from Theorem A and block invariance with no further input. No
    such deduction is known.
  - The defect concerns realizers `x in N_rel(sigma)` outside `sigma(G)`.
- **Realizers.** Theorem B already shows that realizer data on `H_b` is
  compressor invariant. By item 5, that now covers everything outside `H_wm`.
- **The Jones remark.** `jones-index-blind-on-unbounded-defect-sector` notes that
  `W_rho(R^x)''` has no evident finite trace. The finite algebra is
  `End_A(W_rho)`: it is finite type I and contains `P`, `P'` and `W_rho(u)`, and
  its center-valued trace gives `tr(P) = tr(P')`. The dimension-ratio reading
  exists, and it is `1`.
- **What survives.** Only `H_wm`, where `sigma|_N`, and hence `sigma|_(Gamma_hat)`
  and `sigma|_(u^-1 Gamma_hat u)`, has no finite-dimensional subrepresentation.
  - A spectral size that registers the defect has to be read there, from the
    infinite-dimensional representation theory of `Gamma_hat`, or directly from
    realizers.
  - None is constructed. **This is where it stops.**

## 7. Red-flag check

- **Inputs.** Lemmas 1–3 use no property (T), no soficity and no property of
  `R^x`. Property (T) of `N` and nonsoficity of `R^x` enter only through items 1–3 of
  `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure` and through block
  invariance.
- **Scope.** Nothing is claimed about soficity of `G`, about Thompson's `V`, or
  about any root. `relative-normalization-modulo-kazhdan-kernel`,
  `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels` and
  `nonsofic-hyperbolic-group` stay OPEN.
- **Novelty.** The multiplicity bound is standard: it is the matrix-valued relative
  form of simple spectrum for ergodic actions. It is proved in full here.
- **Review.** Not independently reviewed.
