# Two root identities decide the matrix-unit hypothesis for EL_3 rank models

Lane `gk-rk-unipotent` (family R), 2026-09-12. Supports the established claims
`el3-unit-root-matrix-units-iff-two-root-identities`,
`matrix-unit-rank-models-extract-ring-rank-models` and
`fd-represented-coefficients-violate-two-root-identities`, and the open claim
`rank-models-of-el3-satisfy-the-two-root-identities`. It builds on
`research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` (lane `gk-l-gate-neg`), cited below
as [RR].

## 0. Summary

Let `R` and `M` be unital rings and `sigma : EL_3(R) -> M^x` a homomorphism. For a root `ab`
(`a != b` in `{1,2,3}`) put `N_ab = sigma(x_ab(1)) - 1`.

* **Theorem A.** The six unit root elements act by a `3 x 3` system of matrix units on pairwise
  orthogonal idempotents (the hypothesis of [RR] Propositions 6 and 8) iff
  `N_12^2 = 0` and `N_23 N_12 = 0`. In characteristic two the first identity holds
  automatically, so a single identity decides.
* **Theorem D.** Under that hypothesis, if `p_1 != 0` then `R` has a unital ring homomorphism
  into the corner `p_1 M p_1`. When `M` is a rank ultraproduct over a field of characteristic
  `p` and `R` is an algebra of characteristic `p`, that corner is again a rank ultraproduct. If
  `p_1 = 0`, `sigma` is trivial.
* **Consequence.** `el3-rank-models-factor-through-ring-rank-models` holds iff every rank model
  satisfies the two identities.
* **Calibration C.** The identities fail in honest rank models of `EL_3(S)` whenever `S` has a
  unital homomorphism into some `M_n(F_p)`. A proof has to use coefficients that generate a
  subring with no finite-dimensional representation, or use the no-rank-model hypothesis in a
  way that is not a group relation.

## 1. Theorem A

**Matrix-unit hypothesis (MU).** There are pairwise orthogonal idempotents `p_1, p_2, p_3` in
`M` such that for all distinct `i, j, k`

```text
sigma(x_ij(1)) = 1 + u_ij,   u_ij in p_i M p_j,   u_ij u_jk = u_ik,   u_ij u_ji = p_i .
```

**Theorem A.** MU holds iff `N_ab N_cd = 0` for all roots `ab, cd` with `b != c`. By Weyl
symmetry this is equivalent to the two identities

```text
N_12^2 = 0      and      N_23 N_12 = 0 .
```

In characteristic two (`2 = 0` in both `R` and `M`) the first identity is automatic:
`(1 + N_12)^2 = 1 + N_12^2 = sigma(x_12(2)) = 1`.

*Proof that MU gives the identities.* `N_ab = u_ab` lies in `p_a M p_b`, so for `b != c`,
`N_ab N_cd` lies in `p_a M p_b p_c M p_d = 0`.

*Proof of the converse.* Assume `N_ab^2 = 0` for every root and `N_jk N_ij = 0` for all distinct
`i, j, k`. Only these identities are used below.

1. **Inverses.** `N_ab^2 = 0` gives `sigma(x_ab(1))^-1 = 1 - N_ab`.
2. **Composition.** For distinct `i, j, k`, `x_ik(1) = [x_ij(1), x_jk(1)]`, with
   `[g,h] = g h g^-1 h^-1`. Put `X = N_ij` and `Y = N_jk`, so `X^2 = Y^2 = YX = 0`. Then
   `(1+X)(1+Y) = 1 + X + Y + XY` and `(1-X)(1-Y) = 1 - X - Y + XY`, and their product
   expands to

   ```text
   (1 - X - Y + XY) + (X - XY) + Y + XY  =  1 + XY ,
   ```

   using `X^2 = Y^2 = 0`, `YX = 0`, `XYX = X(YX) = 0` and `YXY = (YX)Y = 0`. Hence

   ```text
   N_ik = N_ij N_jk        (i, j, k distinct).                               (*)
   ```

3. **Idempotents.** Put `p_i^(j) = N_ij N_ji`. For distinct `i, j, k`, (*) gives
   `N_ji N_ik = N_jk` and `N_ij N_jk = N_ik`, so `p_i^(j) N_ik = N_ij N_jk = N_ik`. Then
   `p_i^(j) N_ij = p_i^(j) N_ik N_kj = N_ik N_kj = N_ij`, hence `p_i^(j)` is idempotent.
   Symmetrically `N_ij N_jk N_kj = N_ik N_kj = N_ij`. So
   `p_i^(k) = N_ik N_ki = N_ij (N_jk N_kj) N_ji = N_ij N_ji = p_i^(j)`. Write `p_i` for this
   idempotent; it satisfies `p_i N_ij = N_ij = N_ij p_j`.
4. **Orthogonality.** `p_i p_j = (N_ij N_ji)(N_ji N_ij) = N_ij N_ji^2 N_ij = 0` for `i != j`.
5. **MU.** `u_ij = N_ij` lies in `p_i M p_j` by step 3. Also `u_ij u_jk = u_ik` by (*), and
   `u_ij u_ji = p_i` by definition. QED

The idempotents are forced: `p_i = N_ij N_ji`.

*Weyl symmetry.* The signed permutation matrices of `EL_3(Z)` lie in `EL_3(R)`, and conjugation
by them sends `x_ab(1)` to `x_(pi(a) pi(b))(+-1)` for every permutation `pi` of `{1,2,3}`. Also
`N_x(-1) = sigma(x(-1)) - 1 = -N_x (1+N_x)^-1`, a unit commuting with `N_x` times `-N_x`. So
`N_x N_y = 0` iff `N_x(-1) N_y(-1) = 0`: each product is a polynomial in `N_x` times `N_x N_y`
times a polynomial in `N_y`, and the units can be cancelled. The ordered pairs `(ab, cd)` with
`b != c` form four `S_3`-orbits:

* `(ab, ab)`, the squares;
* `(ab, ad)`, same row;
* `(ab, cb)`, same column;
* `(ab, ca)`, the reversed composable pair.

The proof above used only the squares and the last orbit, whose representative is
`N_23 N_12 = 0`. The same-row and same-column identities, for example `N_12 N_13 = 0` and
`N_12 N_32 = 0`, then follow from MU.

## 2. Theorem D (extraction)

**Theorem D.** Let `p` be a prime, `R` a unital algebra over a field of characteristic `p`, `M`
a rank ultraproduct `prod_omega M_(n_i)(k) / d_omega` with `char k = p`, and
`sigma : EL_3(R) -> M^x` a homomorphism satisfying MU.

1. If `p_1 != 0`, there is a unital ring homomorphism `C : R -> p_1 M p_1`, and `p_1 M p_1`,
   with rank renormalized by `rk(p_1)`, is a rank ultraproduct over `k`.
2. If `p_1 = 0`, `sigma` is trivial.

*Proof.*

* **The ring homomorphism.**
  * *Characteristic 2:* [RR] Proposition 6 gives `n_ij(a) = C(a) E_ij` with `C` a unital ring
    homomorphism into `p_1 M p_1`. Its proof uses neither simplicity nor non-direct-finiteness.
  * *Odd `p`:* [RR] Proposition 8 gives block support `n_ij(a)` in `p_i M p_j`. The
    computation in [RR] Corollary 9 (additivity, `[1+X, 1+Y] = 1 + XY` for block-supported
    `X`, `Y`, and `C(a) = psi_12(a) u_21`) gives the unital ring homomorphism, again without
    simplicity.
* **The corner is a rank ultraproduct.** Let `r = rk(p_1) > 0`. Represent `p_1` by matrices
  `A_i` with `rk(A_i^2 - A_i) / n_i -> 0`. Fitting decomposition of `A_i` gives idempotents
  `P_i` with `rk(A_i - P_i) <= 2 rk(A_i^2 - A_i)`, so `(P_i)` represents `p_1`. Then
  `P_i M_(n_i)(k) P_i ~= M_(r_i)(k)` with `r_i = rk P_i` and `r_i / n_i -> r`. So
  `p_1 M p_1 ~= prod_omega M_(r_i)(k) / d_omega`, whose normalized rank is `rk / r`.
* **The trivial case.** If `p_1 = 0`, then `u_1j = p_1 u_1j = 0` and `u_i1 = u_i1 p_1 = 0`. So
  `u_ij = u_i1 u_1j = 0` for all `i != j`, and `x_ij(1)` lies in `ker sigma`. The normal
  closure of `x_kj(1)` contains `[x_ik(a), x_kj(1)] = x_ij(a)` for every `a` in `R`. So it
  contains all root elements, which generate `EL_3(R)`, and `sigma` is trivial. QED

## 3. Consequence for the gate

Under the hypothesis of `el3-rank-models-factor-through-ring-rank-models` (`R` simple of
characteristic `p`, with no unital ring homomorphism into any rank ultraproduct over a field of
characteristic `p`):

* If a rank model `sigma` satisfies the two identities, Theorem A gives MU. Theorem D.1 rules out
  `p_1 != 0`, and Theorem D.2 then makes `sigma` trivial.
* If `sigma` is trivial, every `N_ab = 0` and the identities hold.

So the gate claim is equivalent to `rank-models-of-el3-satisfy-the-two-root-identities`. The two
routes `two-root-identities-give-el3-ring-rigidity` and
`el3-ring-rigidity-gives-the-two-root-identities` form an intended cycle. Simplicity of `R` is
not used in the forward route.

For the payoff `R = L_(F_2)(1,2)`, a nontrivial characteristic-two rank model of `R^x = EL_3(R)`
exists iff some model has `N_23 N_12 != 0`. That is, `x_23(1) - 1` and `x_12(1) - 1` compose to
something nonzero in the order opposite to the Steinberg commutator.

## 4. Calibration C: honest models violating the identity

**Claim C.** Let `S` be a unital ring with a unital ring homomorphism `phi : S -> M_n(F_p)`.
Then `EL_3(S)` has a rank model, into a rank ultraproduct over `F_p`, with `N_23 N_12 != 0`.

*Proof.*
* **The model.** Let `H` be the image of `EL_3(phi) : EL_3(S) -> GL_3(M_n(F_p)) = GL_(3n)(F_p)`,
  a finite group. Put `h_ab = 1 + I_n (x) E_ab`, the image of `x_ab(1)`. Let `lambda` be the left
  regular representation of `H` on `F_p[H]`, and embed `M_(|H|)(F_p)` into the constant rank
  ultraproduct by `a -> (a (x) I_m)_m`.
* **The product.** `N_23 N_12` is left multiplication by
  `(h_23 - 1)(h_12 - 1) = h_23 h_12 - h_23 - h_12 + 1`. The four group elements are distinct:
  `h_12, h_23 != 1`, `h_23 != h_12`, and `h_23 h_12` is none of `1, h_12, h_23`. So this is a
  nonzero element of `F_p[H]`, left multiplication by it has positive rank, and the constant
  sequence keeps that rank. QED

**Cross-check (lane `gk-l-gate-pos`, artifact
`leavitt-unit-rank-model-construction-audit-2026-09-12.md` Section 8).** The natural tensor dual
model of `EL_3(F_2[t])` has `N_ab = E_ab (x) 1 + 1 (x) E_ba + E_ab (x) E_ba`. There
`N_23 N_12 = E_23 (x) E_21 + E_12 (x) E_32 + 1 (x) E_31 + E_12 (x) E_31 + E_23 (x) E_31`, which
is nonzero.

**Consequence for any proof of the identity.**
* **Relations alone don't suffice.** Take finitely many relations among elements `x_ij(a_s)` of
  `EL_3(R)`, and let `S` be the subring generated by the `a_s`. Then `EL_3(S)` is a subgroup of
  `GL_3(R)`, so those relations hold in `EL_3(S)`. If `S` has a unital homomorphism into some
  `M_n(F_p)`, the model of Claim C satisfies all of them and violates the identity.
* **What a proof must use instead:**
  * coefficients generating a subring with no nonzero unital finite-dimensional
    representation over `F_p`, for example a subring containing a unital Leavitt family; or
  * the no-rank-model hypothesis in a way that is not a relation.
* **Even the Toeplitz subring isn't enough.** The subring generated by `s_0, t_0`, with
  `t_0 s_0 = 1`, maps onto `F_2`, so it does not suffice.

## 5. Where the identity resists (Attempts material, not claims)

* **Five terms.** In characteristic two, with `X = N_12` and `Y = N_23`,
  `N_13 = XY + YX + XYX + YXY + XYXY` ([RR] Lemma 3). The identity `YX = 0` kills every term
  except `XY`. No Steinberg relation among `x_12(1)`, `x_23(1)`, `x_13(1)` isolates `YX`,
  consistently with Claim C.
* **Self-similar factorization.** Put `iota_w(g) = s_w g t_w + (1 - e_w)`, where
  `e_w = s_w t_w`, for `w = 0, 1`.
  * `iota_0` and `iota_1` are commuting injective endomorphisms of `GL_3(R)`, and
    `iota_0(g) iota_1(g) = s_0 g t_0 + s_1 g t_1 = g` for `g` in `SL_3(F_2)`.
  * So on `SL_3(F_2)` the model is the diagonal restriction of the commuting pair
    `(sigma iota_0, sigma iota_1)`, a rank model of `SL_3(F_2) x SL_3(F_2)`.
  * Proposition 5 of [RR] makes the displacement ranks of `(x,1)`, `(1,x)` and `(x,x)` equal,
    for `x = x_12(1)`.
  * **Outer tensor components.** On `U_0 (x) U_1` with normalized displacements `a_0`, `a_1`
    in `[0, 1/2]`, `(x,x)` has displacement `a_0 + a_1 - 2 a_0 a_1`. Averaging the equalities
    over a mixture of such components forces every component to be either free-type
    (`a_0 = a_1 = 1/2`) or trivial.
  * **Free-type components violate the identity**, as in Claim C.
  * **Where it stops.** Indecomposable `F_2[SL_3(F_2) x SL_3(F_2)]`-modules that are not outer
    tensor products escape this counting. For example, three Klein-four modules, in each of
    which one of `a`, `b`, `ab` acts trivially, average to equal displacement `1/3`. So
    uniform displacement does not force the identity.
* **Same-row and same-column identities.** From squares alone they do not give the
  reversed-composable one. Writing `N_31` through `[x_32(1), x_21(1)]` and using
  `N_12 N_32 = 0` leaves the residual `N_12 N_21 N_32 (1 + N_21)`. That residual vanishes under
  MU but is not forced by these two identities.

## 6. Leavitt relations proposed to force `N_23 N_12 = 0`, and why finite subgroups cannot

Lane `gk-rk-unipotent`, follow-up for the family lead. Characteristic two,
`R = L_(F_2)(1,2)`, `e_i = s_i t_i`, `n_ab(c) = sigma(x_ab(c)) - 1`, `X = N_12`, `Y = N_23`.
Supports the established claims `shifted-root-pair-conjugates-to-idempotent-root-pair` and
`finite-subgroup-rank-data-cannot-force-two-root-identity`.

### 6.1 The shifted root pair is conjugate to the idempotent pair, not to the unit pair

The proposal: `x_13(1) = [x_12(t_0), x_23(s_0)] = [x_12(1), x_23(1)]`. If the two pairs were
simultaneously conjugate in `GL_3(R)`, then `rk(n_23(s_0) n_12(t_0)) = rk(YX)`.

**Invariant.** For operators `N`, `M` on `R^3` put
`T(N, M) = (ker N ∩ ker M) / ((ker N ∩ ker M) ∩ (Im N + Im M))`. Simultaneous conjugation carries
kernels to kernels and images to images, so the isomorphism type of `T` is a conjugacy
invariant. Matrices act on columns, and `R^3` is a right `R`-module.

* **Unit pair `(E_12, E_23)`.** `ker E_12 ∩ ker E_23 = e_1 R`, and `Im E_12 + Im E_23 = e_1 R (+) e_2 R`.
  So `T = 0`.
* **Shifted pair `(t_0 E_12, s_0 E_23)`.**
  * `t_0 v = 0` iff `v` lies in `s_1 R`, and left multiplication by `s_0` is injective.
  * So the common kernel is `e_1 R (+) e_2 s_1 R`.
  * `Im(t_0 E_12) = e_1 t_0 R = e_1 R` and `Im(s_0 E_23) = e_2 s_0 R`.
  * So `T ~= s_1 R ~= R`, which is nonzero.
* **Idempotent pair `(e_0 E_12, e_0 E_23)`.**
  * The common kernel is `e_1 R (+) e_2 e_1 R (+) e_3 e_1 R`.
  * The image sum is `e_1 e_0 R (+) e_2 e_0 R`.
  * So `T ~= (e_1 R)^3 ~= R`, which is nonzero.

So the shifted pair is not conjugate to the unit pair, although both have commutator `x_13(1)`.

**Explicit conjugacy with the idempotent pair.** Both modules are
`(natural (x) R) (+) (trivial (x) R)`. The intertwiner

```text
g = [ t_0        0                           0            ]
    [ s_1s_0t_1  s_0t_0 + s_1s_1s_0t_1       s_1s_1s_1t_1 ]
    [ 0          0                           t_0          ]
```

does the following.
* **Chain.** It maps `e_3 e_0 R -> e_2 e_0 R -> e_1 e_0 R` onto `e_3 R -> e_2 s_0 R -> e_1 R`, by
  `t_0`, the identity and `t_0`.
* **Trivial part.** It maps `(e_1 R)^3` onto `e_2 s_1 R`, through
  `1 = s_0 t_0 + s_1 s_0 t_0 t_1 + s_1 s_1 t_1 t_1`.
* **Entrywise check.**
  * `g (e_0 E_12)` has column `2` equal to `(t_0 e_0, s_1 s_0 t_1 e_0, 0) = (t_0, 0, 0)`.
  * `(t_0 E_12) g` has row `1` equal to `t_0` times row `2` of `g`, which is `(0, t_0, 0)`.
  * `g (e_0 E_23)` has entry `(2,3)` equal to `(s_0 t_0 + s_1 s_1 s_0 t_1) e_0 = e_0`, and so does
    `(s_0 E_23) g`.
* **Invertibility.**
  * *Injective:* `g v = 0` forces `e_0 v_1 = e_0 v_3 = 0` from rows `1` and `3`. Row `2` then
    forces `e_0 v_2 = 0` and `t_1 v_i = 0` for each `i`.
  * *Surjective:* the same decomposition of `1` solves `g v = w`.
* **Scope.** `GL_3(R) = EL_3(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`), so `g` lies in
  the group on which `sigma` is defined.

**Where the proposal dies.** Conjugacy yields only
`rk(n_23(s_0) n_12(t_0)) = rk(n_23(e_0) n_12(e_0))`, a statement about the type
`natural (+) trivial`. The unit pair is a different type. Even if the pairs had been conjugate,
the conjugacy would relate two finite subgroups (`D_8 = <x_12(t_0), x_23(s_0)>` and
`<x_12(1), x_23(1)>`), which Section 6.3 shows is never enough.

### 6.2 The orthogonal splitting

Put `a' = sigma(x_12(e_0))`, `a'' = sigma(x_12(e_1))`, `b' = sigma(x_23(e_0))` and
`b'' = sigma(x_23(e_1))`, with `X' = a' - 1` and so on.
* **Commutation.** `a'` commutes with `a''` and `b'` with `b''` (abelian root subgroups). `a'`
  commutes with `b''` and `a''` with `b'`, since `[x_12(e_i), x_23(e_j)] = x_13(e_i e_j) = 1` for
  `i != j`.
* **Expansion.** `Y = Y' b'' + Y''` and `X = X' a'' + X''`, so

  ```text
  YX = Y'X' b''a''  +  b'' X''Y'  +  X' Y''a''  +  Y''X'' .
  ```

* **Block models.** There the cross terms vanish and `YX = Y'X' + Y''X''`, which gives the
  counting `f(nat) = 2 f(nat (+) triv)`.
* **General models.** No term is forced to vanish. Everything lives in the finite group
  `EL_3(F_2 e_0) x EL_3(F_2 e_1) ~= SL_3(F_2)^2`, so Section 6.3 applies.

### 6.3 Finite-subgroup rank data is consistent with free behaviour

**Theorem F.** Let `G` contain `D = <g, h> ~= D_8`, with `g`, `h` involutions and `gh` of order `4`.
For each finite subgroup `K` of `G` put `r_K(alpha) = rank(lambda_K(alpha)) / |K|` for
`alpha` in `F_2[K]`.
* **Realizable.** Each `r_K` is the rank function of the regular representation, placed in the
  constant rank ultraproduct.
* **Restriction.** `r_L` restricted to `F_2[K]` is `r_K`.
* **Conjugation.** `r_K` is invariant under every isomorphism of finite subgroups, in particular
  under conjugation by `G`.
* **Value.** `r_D((h - 1)(g - 1)) = 3/8`.

*Proof.*
* **Restriction.** `F_2[L] ~= F_2[K]^([L:K])` as a left `F_2[K]`-module, so the ranks scale by
  `[L:K]` and the normalized ranks agree.
* **Conjugation.** An isomorphism of groups induces an isomorphism of regular modules.
* **Value.** With `x = g - 1` and `y = h - 1`, `F_2[D_8] = F_2<x,y>/(x^2, y^2, xyxy - yxyx)`, with
  basis `1, x, y, xy, yx, xyx, yxy, xyxy`. Left multiplication by `yx` sends `1, y, yx` to
  `yx, yxy, yxyx`, and kills `x`, `xy`, `xyx`, `yxy` and `xyxy`. For example
  `yx·yxy = (yxyx) y = xyx y^2 = 0`. So the rank is `3`.
QED

For `G = EL_3(R)`, `g = x_12(1)` and `h = x_23(1)` generate `UT_3(F_2) ~= D_8`.

**Consequence.** Take an argument deriving `N_23 N_12 = 0` for all rank models from:
* relations inside finite subgroups;
* inclusions among finite subgroups;
* conjugacy between finite subgroups;
* the rank data of `sigma` on each finite subgroup separately.

The free profile satisfies all of these and violates the conclusion, so no such argument exists.
The following are covered:

* **Steinberg relations, with any coefficients.** `<x_ij(a), x_jk(b)>` lies in the finite
  Heisenberg group over the additive spans. That includes gk-ri-nofd's isometry commutator
  identities (`leavitt-isometry-commutators-constrain-el3-rank-models`) and the bridge from
  coefficient `1` to `t_0, s_0`: `<x_12(1), x_12(t_0), x_23(1), x_23(s_0)>` has order `128`.
* **The splitting `x_12(1) = x_12(e_0) x_12(e_1)`**, and branch expansions under `diag(w,w,w)`
  for an involutive unit `w` such as `s_0 t_1 + s_1 t_0`. `<x_ij(e_0), x_ij(e_1), diag(w,w,w)>`
  is finite.
* **Conjugacy by Leavitt and Thompson units**, including Section 6.1 and [RR] Proposition 5.
* **Involution-class and displacement counting on level groups** ([RR] Propositions 2 and 12).
* **Isometry pairs across opposite roots.** `x_12(t_0) x_21(s_0) = [[0, t_0],[s_0, 1]]` has cube
  `1`, because `e_1 s_0 = 0`. Likewise `x_12(s_0) x_21(t_0) = [[e_1, s_0],[t_0, 1]]` has cube `1`.
  So both pairs generate `S_3`.

**What a proof must use.** It must use `sigma` on a subgroup of `EL_3(R)` contained in no finite
subgroup, or joint rank relations between elements of finite subgroups that together generate
an infinite group. A concrete example is `<diag(u, u^-1, 1), x_12(1)>` with `u` a Thompson unit of
infinite order, such as `s_00 t_0 + s_01 t_10 + s_1 t_11`. It contains `x_12(u^(2k))` for every
`k`. The one input known to reach such subgroups is direct finiteness of `M`, applied to products
across them. That is how the matrix-unit collapse of [RR] Corollary 7 ends, once the identity is
known.

**Untested idea, recorded only.** If tensor-power amplification of an `F_2`-linear sofic
approximation drove every finite subgroup toward free behaviour, the free profile would be the
generic profile. Then the gate would be exactly the question of whether the free profile extends
to infinite subgroups of `R^x`. I have not checked this against the literature on non-projective
parts of tensor powers, and nothing rests on it.
