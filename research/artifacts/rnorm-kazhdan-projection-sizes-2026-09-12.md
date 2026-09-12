# Kazhdan-projection sizes for RNORM on the hyperbolic Leavitt cover

Date: 2026-09-12. Lane `rnorm-kazhdan-projection-sizes` (swarm 6).
- **Target:** `relative-normalization-modulo-kazhdan-kernel` (RNORM) for
  `hyperbolic-kazhdan-cover-of-leavitt-unit-group`.
- **Candidate asked:** read a size from the Kazhdan projections of the kernel `N`
  in a sofic approximation: size and position of the fixed sector, how `sigma(G)`
  permutes the `N`-isotypic components, and the transport cost between them.
- **Outcome:** blind on every bounded-multiplicity sector. Theorems A and B below
  are landed as established claims. What survives is Section 4.

## 0. Setting

- **Cover:** `1 -> N -> G -> Q -> 1` with `Q = R^x`, `R = L_(F_2)(1,2)`. `N` is
  infinite and Kazhdan. `Q` is finitely presented
  (`leavitt-unit-group-finitely-presented`) and infinite simple
  (`binary-leavitt-unit-group-is-simple`), so it has no nontrivial finite quotient.
- **Model:** `sigma : G -> S_U` is a sofic representation (ultraproduct of a sofic
  approximation). `S_U` acts by Koopman unitaries on `H = L^2(X_U, mu_U)`, the
  Loeb space of the ultraproduct.
- **Algebras:**
  - `D_U` is the diagonal algebra acting by multiplication.
  - `D^N` is its `sigma(N)`-invariant part.
  - `A` is the weak closure of `D^N` on `H`.
- **Block invariance:** `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`
  gives `D^N = D^G`, so `A` commutes with `sigma(G)`.
- **Kazhdan-projection data:** for a finite-dimensional irreducible unitary
  representation `rho` of `N` on `V_rho`:
  - the Kazhdan projection of `rho-bar (x) sigma|_N` projects onto
    `W_rho = Hom_N(V_rho, H)`;
  - the `rho`-isotypic subspace is `H_rho = V_rho (x) W_rho`, with projection `P_rho`;
  - `rho = 1` gives the fixed sector `L^2(D^N)`.

  Every datum in the candidate list is read from the family `(P_rho, W_rho)` and
  the action of `sigma(G)` and realized twists on it.

## 1. Theorem A (representation theory; no sofic input)

Let `1 -> N -> G -> Q -> 1` with `N` Kazhdan and `Q` finitely generated with no
nontrivial finite quotient. Let `pi` be any unitary representation of `G` on a
Hilbert space `H`; no separability is needed.

- **(A1)** For each `d`, the set `Irr_d(N)` of classes of `d`-dimensional
  irreducible unitary representations is finite. Every `g in G` fixes every class:
  `rho o Ad(g) ~ rho`.
- **(A2)** `pi(G)` commutes with every isotypic projection `P_rho` of `pi|_N`.
- **(A3)** On `H_rho = V_rho (x) W_rho`, `pi(g) = U_rho(g) (x) W_rho(g)`. Here
  `U_rho(g)` lies in the norm closure of `T . rho(N)` in `U(V_rho)`, and `W_rho` is
  a projective unitary representation of `G`, trivial on `N`.
- **(A4)** Let `A` be an abelian von Neumann algebra on `H` commuting with
  `pi(G)`. Then `A|_(H_rho) = 1 (x) A_rho` with `A_rho <= W_rho(G)'`.
  - Suppose `E <= W_rho` is closed, invariant under `A_rho` and `W_rho(G)`, and
    `A_rho|_E` has multiplicity at most `m < infinity`. Then `W_rho(g)|_E` is a
    scalar for every `g`.
  - For every finite family of such sectors `S = (+)_i V_(rho_i) (x) E_i`,
    `pi(g)|_S` lies in the norm closure of `T . pi(N)|_S`.

### Proof

1. **Finitely many types.** This is Wang's theorem
   (`kazhdan-bounded-unitary-types-are-finite`). The elementary argument: take a
   Kazhdan pair `(S, kappa)` for `N`. If `max_s ||rho(s) - rho'(s)|| < kappa`,
   then `v = I/sqrt(d)` is `kappa`-almost invariant for `A -> rho(n) A rho'(n)^*` on
   `M_d(C)` with the Hilbert–Schmidt norm. A nonzero invariant `A` is an
   intertwiner, so Schur gives `rho ~ rho'`. Covering the compact `U(d)^S` by
   finitely many `kappa/2`-balls bounds the number of classes.
2. **Types are fixed.** `g . [rho] = [rho o Ad(g^-1)]` is an action of `G` on the
   finite set `Irr_d(N)`. `N` acts trivially, since `rho o Ad(n^-1)` is conjugate
   to `rho` by `rho(n)`. So this is an action of `Q` through a finite group, which
   is trivial. This is (A1).
3. **Sectors are invariant.** If `T : V_rho -> H` intertwines `rho` with `pi|_N`,
   then `pi(g) T` intertwines `rho o Ad(g^-1)` with `pi|_N`, and this is equivalent
   to `rho` by step 2. So `pi(g) H_rho = H_rho`. This is (A2).
4. **Splitting.** Schur gives `U(g) in U(V_rho)`, unique up to a scalar, with
   `rho(g n g^-1) = U(g) rho(n) U(g)^*`; for `n in N` take `U(n) = rho(n)`. Put
   `W(g) T = pi(g) T U(g)^*`. This is again an intertwiner, `W(g)` is unitary, and
   `pi(g)(T v) = (W(g) T)(U(g) v)`. So `pi(g)|_(H_rho) = U(g) (x) W(g)`. Both factors
   are projective representations of `G`, and `W(n) = 1` for `n in N`.
5. **The outer part is inner.** Let `K` be the closure of `[rho(N)]` in `PU(V_rho)`.
   `[U(G)]` normalizes `K`, so `G -> N(K)/K` is a homomorphism trivial on `N`.
   - `N(K)/K` is a compact Lie group, hence linear.
   - The image of `Q` is a finitely generated linear group, so it is residually
     finite (`finitely-generated-linear-groups-are-residually-finite`).
   - A nontrivial image would give a nontrivial finite quotient of `Q`, so the
     image is trivial and `[U(g)] in K`.
   - Lifting through `U(d) -> PU(d)` gives `U(g) = lim lambda_k rho(n_k)`. This
     is (A3).
6. **Bounded multiplicity forces scalars.** `A` commutes with `pi(N)|_(H_rho) = rho (x) 1`,
   so `A|_(H_rho) = 1 (x) A_rho`, and `A_rho` commutes with every `W(g)`.
   - On `E`, the commutant `(A_rho|_E)'` is type I with multiplicities at most
     `m`: `(A_rho|_E)' = (+)_(k <= m) M_k(Z_k)` with `Z_k` abelian. It contains
     `W(g)|_E`.
   - Evaluate at a character `chi` of `Z_k`. This gives a projective
     representation `Q -> PU(k)`, which is trivial by step 5's argument. So
     `W(g)|_E = lambda_g`, a unitary in the center `Z = (+) Z_k`.
   - For two characters `chi, chi'` the cocycle cancels, so
     `g -> lambda_g(chi)/lambda_g(chi')` is a character `Q -> T`. It is trivial,
     since `T` is compact Lie.
   - By Gelfand, `lambda_g` is a constant, so `W(g)|_E` is a scalar.
7. **Finite families.** On `S`, `pi(g)|_S` and `pi(N)|_S` both lie in the compact
   group `prod_i U(V_(rho_i)) (x) 1`.
   - Let `L` be the closure of `T . pi(N)|_S`. Then `G -> N(L)/L` is trivial on `N`
     and factors through a compact Lie group, so it is trivial as in step 5.
   - Hence `pi(g)|_S in L`, with one global scalar; no per-sector phases remain.
     This is (A4).

### Boundary examples

- **Finite quotients break (A1) and (A4).** Take `G = N x F` with `F` finite and
  nontrivial, `rho = 1`, and `pi = 1 (x) lambda_F`. Then `W = lambda_F` on `C^|F|`
  is not scalar at multiplicity `|F|`.
- **Unbounded multiplicity breaks (A4).** Take the quasi-regular `pi = l^2(G/N)`
  with `rho = 1` and `A = C`. Then `W = lambda_Q` on `l^2(Q)` is not scalar, with
  infinite multiplicity.

## 2. Theorem B (the cover)

Setting of Section 0. The **bounded-multiplicity Kazhdan sector** `H_b` is the
closed span of all `V_rho (x) E`, with `rho` finite-dimensional irreducible and
`E` as in (A4) for `A = weak closure of D^N`. Write `P_b` for its projection.

- **(B1)** `P_b` commutes with `sigma(G)`. For every `g in G`, `sigma(g)|_(H_b)` lies
  in the strong closure of `T . sigma(N)|_(H_b)`.
  - This comes from (A4) on finite sub-sums, together with a net over
    `(finite sub-sum, eps)`.
  - For unitaries, strong convergence gives strong* convergence.
  - In particular `sigma(Gamma_hat)`, `sigma(t Gamma_hat t^-1)`, `sigma(G)` and
    `sigma(N)` have the same strong closure times `T` on `H_b`.
- **(B2)** Notation as in `realized-relative-twists-embed-in-outer-twist-group`,
  with `M = N`, rigid pair `Gamma_hat <= G_hat` and realizer sets
  `R(q) = x M_s C_s`. Put `S_b(q)` = strong closure of `T . P_b R(q) P_b`.
  - `S_b(eps_t(q)) = S_b(q)` for every compressor `t`.
  - `S_b([sigma(z)]) = S_b(1)` for every host twist `z in G` with
    `[z, Gamma_hat] <= N`. On the cover this is all of
    `Q = C_(R^x)(EL_alpha(R))`, including the strict self-embedding
    `A = <eps_u^k(V_(1000))>`.
- **(B3)** **Consequence.** Any size read from `S_b`, together with the positions
  of `Gamma_hat` and its compressed images on `H_b`, the `A`-module structure of
  `H_b`, the isotypic projections and multiplicity functions, and transport costs
  of `sigma(G)` on `H_b`, satisfies:
  - it takes the same value on `B` and `eps_t(B)`;
  - it takes the same value on every subgroup of host twists as on the trivial
    group.

  So it cannot register the cover's relative defect.

### Proof

1. **Realizer sets are kernel-conjugation invariant.** For `n in N`,
   `sigma(n)^-1 x m c sigma(n) = x m' m c sigma(n)` with
   `m' = x^-1 sigma(n)^-1 x in M_s`, because `x` normalizes `M_s`.
   - `c in C_s` commutes with `sigma(Gamma_hat)`, which contains `sigma(N)`, so
     `c sigma(n) = sigma(n) c`.
   - Hence `sigma(n)^-1 R(q) sigma(n) = R(q)`.
   - `P_b` commutes with `sigma(N)`, since `sigma(n)|_(H_rho) = rho(n) (x) 1`
     preserves `V_rho (x) E`. So `P_b R(q) P_b` is invariant under conjugation by
     `T . sigma(N)|_(H_b)`, and its strong closure is invariant under the strong
     closure of that group.
2. **Compressors.** `R(eps_t(q)) = s^-1 R(q) s` with `s = sigma(t)`
   (`conjugation-invariant-sizes-miss-defect-proof`, step 1). `s` commutes with
   `P_b`, so `P_b R(eps_t q) P_b = s^-1 (P_b R(q) P_b) s`.
   - By (B1) `s|_(H_b)` is a strong limit of `lambda_alpha sigma(n_alpha)`.
   - Conjugating bounded operators along a strong* convergent net of unitaries
     converges strongly, so `S_b(eps_t q) <= S_b(q)` by step 1.
   - The reverse inclusion is the same argument with `s^-1`, using that
     `R(eps_t q)` is also kernel-conjugation invariant.
3. **Host twists.** For `z` as stated, `sigma(z) in R([sigma(z)])` and `sigma(z)`
   commutes with `P_b`.
   - So `P_b sigma(z) M_s C_s P_b = sigma(z) P_b M_s C_s P_b`.
   - By (B1) this lies in the strong closure of
     `T . sigma(N) P_b M_s C_s P_b = T . P_b R(1) P_b`, since `sigma(N) = M_s`.
   - The reverse inclusion uses `sigma(z)^-1`.
4. **Red-flag check.**
   - Property (T) of `N` enters through Wang finiteness, and nonsoficity of `R^x`
     through block invariance, which is what puts `A` in the commutant.
   - No soficity of `G` is used, and nothing is claimed about soficity or about
     Thompson's `V`.
   - The statement is an obstruction to a method. It holds whether or not the
     cover is sofic.

## 3. Relation to the recorded no-gos

- **`conjugation-invariant-sizes-miss-relative-defect`:** that claim leaves the
  position of `Gamma_s` as the only untransported datum. (B1) shows that on `H_b`
  that position is not a datum: `Gamma_s`, its compressed images and `N` have the
  same closure.
- **`component-space-sizes-miss-leavitt-cover-defect`:** that claim is the case
  `rho = 1` of the invariant sector of `Gamma`. Theorem B adds every
  finite-dimensional isotype of `N` at bounded multiplicity.
- **`finite-orbit-indices-miss-twists-without-finite-quotients`:** the isotypic
  permutation action of realized twists on `Irr_d(N)` is a finite-orbit datum, by
  Wang finiteness. By (A1), `sigma(t)` acts trivially on it, so the permutation
  of `eps_t(q)` equals that of `q`.
- **`leavitt-cover-regular-realizer-models-iff-residually-finite`:** in
  finite-quotient models the block algebra has an atom and every isotype has
  finite multiplicity, so the whole Kazhdan sector is `H_b`. Theorem B is
  consistent with that claim: exact models satisfy every transported identity.

## 4. What survives. **This is where it stops.**

`H = H_b (+) H_wm (+) H_inf`, where:

- **`H_wm`** is the weakly mixing part of `sigma|_N`, with no finite-dimensional
  isotype. Every Kazhdan projection of every `rho-bar (x) sigma|_N` vanishes there,
  so the candidate reads nothing on it.
- **`H_inf`** is the unbounded-multiplicity part of the finite-dimensional
  isotypic sectors. There `W_rho` is a projective unitary representation of
  `R^x` with no nonzero bounded-multiplicity invariant `A`-submodule, and it can
  be non-scalar (the quasi-regular boundary example).
  - The position of `Gamma_hat` is a real datum there: `W_rho(EL_alpha(R))`
    versus `W_rho(u^-1 EL_alpha(R) u)`.
  - Conjugation by `W_rho(u)` maps the fixed space of the first onto the fixed
    space of the second, which is contained in it.
  - At infinite multiplicity a strict inclusion of unitarily conjugate subspaces
    is allowed, so dimension counts give nothing.
  - The canonical trace is also no help: every Kazhdan and isotypic projection of
    an infinite group has trace `0` in a trace-zero model.

**Surviving shape.** A size on `H_inf` must be a *relative index* on
infinite-multiplicity modules over `A`, invariant under conjugation by `W_rho(u)`,
and quantized so that a strict inclusion forces a jump. For example:
- the von Neumann dimension over a finite algebra containing `W_rho(Q)`;
- a Jones index `[W^(EL_alpha) : W^(u^-1 EL_alpha u)]` in the quantized range
  `{4 cos^2(pi/n)} U [4, infinity)`. An almost-invariance bound below `2`, from a
  median argument with (T), would then force index `1`. That would be the
  analogue of Kun–Thom's integer index below `2`.

No such trace or index is constructed: `W_rho(R^x)''` has no evident finite trace
in a sofic model.
