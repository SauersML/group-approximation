---
rg: 2
id: deligne-parameter-tori-corestrict-only-through-maslov-line-proof
kind: route
title: Tensor-induce norm models, compute the transfer identities with exact twisted regular representations, then differentiate
target: deligne-parameter-tori-corestrict-only-through-maslov-line
requires: [deligne-sep7-norm-parameter-closed-subgroup, sp4-fd-projective-multiplier-is-finite, deligne-covers-of-sp2g-z-have-finite-residual-2z]
---

Notation of the target. All cocycles are normalized and `T`-valued. `k = [Gamma:H]`. Fix left-coset
representatives `t_1 = e, ..., t_k` and write `g t_j = t_(sigma_g j) h_j(g)` with `h_j(g) in H`. Then
`h_j(g g') = h_(sigma_(g') j)(g) h_j(g')`, and `g -> sigma_g` is a homomorphism to `Sym(k)`.

**Fact E (exact projective representations determine their multiplier).** If `V : L -> GL(X)` satisfies
`V(g)V(h) = mu(g,h) V(gh)` with invertible `V(gh)` and scalar `mu`, then `mu` is determined by `V`. Associativity
of operator composition makes `mu` a 2-cocycle. Conjugating by a fixed invertible `S`, or multiplying by a scalar
function `nu(g)`, changes `mu` to `mu` or to `mu . delta nu`. Every `omega` in `Z^2(L,T)` is the multiplier of the
twisted left regular representation `lambda_omega(g) delta_x = omega(g,x) delta_(gx)` on `l^2(L)`.

**(T1) Structure.**
- *Classes.* Rephasing `U_n -> nu U_n`, with `nu : L -> T` and `nu(e) = 1`, turns an `omega`-model into an
  `omega . delta nu`-model with the same defects. So `P(L)` and `R(L)` are unions of classes.
- *Subgroup.* `U_n (x) U'_n` is an `omega omega'`-model, with defect at most the sum of the defects. `conj(U_n)` is
  an `omega^(-1)`-model.
- *Closedness.* This is the diagonal argument of `deligne-sep7-norm-parameter-closed-subgroup`, run on each coset of
  `T_0(L)` in `H^2(L,T)`.
  - `H_2(L)` is finitely generated, since `L` is finitely presented, so there are finitely many cosets.
  - On the coset of `[omega_0]`, parametrize by `omega_0 . e(sum_i s_i z_i)`, where the `z_i` are real cocycles
    spanning `H^2(L,R)`.
  - This is continuous pointwise in `s`. A convergent sequence of parameters in `P(L)` gives models whose defects,
    on each finite window, differ from those of the limit by `o(1)`.
- *Exact points.* `R(L) <= P(L)`: take the constant sequence. For normalized `omega`, `U(e)^2 = U(e)` forces
  `U(e) = I`.
- *Conjugation.* For `H` normal and `g in Gamma`, `U_n o Ad(g^(-1))` is a model for `(c_g^(-1))^* omega`.
- *Restriction.* Restriction of models gives `res P(Gamma) <= P(H)`.
- *The Maslov circle.* By the definition of `P_op` and rephasing, `P(Gamma) cap {e(theta b)} = {e(theta b) : theta in P_op}`.
- *`T_0(Gamma)` is the Maslov circle.*
  - `H_2(Gamma,Z)` has rank one, by `sp4-fd-projective-multiplier-is-finite` ("rank one"). So `H^2(Gamma,R)` is a line.
  - `[b]_R != 0`. Otherwise `N[b] = 0` in `H^2(Gamma,Z)` for some `N >= 1`. For a prime `q > 2` with `q not | N`,
    Bezout gives `[b] in q H^2(Gamma,Z)`. Then `b mod q` is a coboundary, and the Deligne cover `E_q` is
    `Gamma x Z/q`, which is residually finite.
  - That contradicts `deligne-covers-of-sp2g-z-have-finite-residual-2z`: the finite residual of `E_q` is the image
    of `2Z`, which is nonzero for odd `q >= 3`.
  - So `T_0(Gamma) = exp(R[b]) = { e(theta b) }`.

**Tensor induction (the cochain map and the defect).** For `omega` in `Z^2(H,T)` put

```text
TI(omega)(g,g') = prod_j omega( h_(sigma_(g') j)(g), h_j(g') ).
```

Given `U : H -> U(d)`, let `TI(U)(g) = P_(sigma_g) o (U(h_1(g)) (x) ... (x) U(h_k(g)))` on `(C^d)^(x k)`. Here
`P_sigma` moves tensor slot `j` to slot `sigma(j)`. Then `TI(U)(g) TI(U)(g')` moves the slot-`j` vector `v` to slot
`sigma_(g g') j` and applies `U(h_(sigma_(g') j)(g)) U(h_j(g'))` to it.

- *Exact case.* If `U` is exact, this equals `TI(omega)(g,g') TI(U)(g g')`. With `U = lambda_omega` and Fact E,
  `TI(omega)` is a cocycle.
- *Defect.* For a model `U_n`, the telescoping bound
  `||(x)_j A_j - (x)_j B_j||_op <= sum_j ||A_j - B_j||_op` for unitaries gives
  `||TI(U_n)(g)TI(U_n)(g') - TI(omega)(g,g') TI(U_n)(g g')|| <= sum_j eps_n(h_(sigma_(g') j)(g), h_j(g')) -> 0`.
- *Normalization.* `TI(U_n)(e) = I`.
- So `TI(P(H)) <= P(Gamma)`, and by the exact case `TI(R(H)) <= R(Gamma)`.
- *Descent to classes.* Replacing `omega` by `omega . delta nu` replaces `TI(U)` by `(prod_j nu(h_j(g))) TI(U)`. By
  Fact E this changes `TI(omega)` by a coboundary. Changing the transversal replaces `TI(U)` by a fixed unitary conjugate times a scalar function of `g`, so by
  Fact E the class is unchanged.
- So `TI` is a well-defined homomorphism `H^2(H,T) -> H^2(Gamma,T)`. It is continuous (a finite product of
  evaluations) and multiplicative in `omega`.
- On `T_0(H)` it is `e(x) -> e(tau x)`, with `tau(x)(g,g') = sum_j x(h_(sigma_(g') j)(g), h_j(g'))`, the
  differential of `TI`.

**(T2) Transfer identities.**
- *`TI o res = k`.* Let `y` be in `Z^2(Gamma,T)` and `U = lambda_y`, exact on `l^2(Gamma)`.
  - Put `S = U(t_1) (x) ... (x) U(t_k)`, slot by slot.
  - `S TI(U|H)(g) S^(-1)` moves the slot-`j` vector `v` to slot `sigma_g j` and applies
    `U(t_(sigma_g j)) U(t_(sigma_g j)^(-1) g t_j) U(t_j)^(-1) = lambda_j(g) U(g)`, with `lambda_j(g)` in `T` by
    exactness.
  - So `S TI(U|H)(g) S^(-1) = mu(g) P_(sigma_g) U(g)^(x k)`, where `mu = prod_j lambda_j`.
  - `P_(sigma_g)` commutes with `U(g)^(x k)`, and `g -> P_(sigma_g)` is a homomorphism. So
    `g -> P_(sigma_g) U(g)^(x k)` has multiplier `y^k`.
  - By Fact E, `TI(res y) = y^k . delta mu`, hence `TI o res = k` on `H^2(Gamma,T)`.
- *`res o TI = sum of conjugates` (`H` normal).* For `h in H`, `h t_j = t_j (t_j^(-1) h t_j)`, so
  `sigma_h = id` and `h_j(h) = t_j^(-1) h t_j`. The cochain formula gives
  `TI(omega)(h,h') = prod_j omega(t_j^(-1) h t_j, t_j^(-1) h' t_j)`. Inner automorphisms of `H` act trivially on
  `H^2(H,T)`, so this is `sum_(g in G) g^* [omega]`.
- *Real version.* Both identities are identities of continuous homomorphisms of compact Lie groups. Differentiating
  at `0` gives `tau o res_R = k` and `res_R o tau = sum_(g in G) g^*` on real cohomology.
- *Consequences.*
  - `res_R` is injective.
  - For `H` normal, `H^2(H,R)^G = res_R H^2(Gamma,R) = R res[b]`: if `v` is invariant then `v = res_R(tau v / k)`.
  - `tau` vanishes on every nontrivial `G`-isotypic component `X`: for `v` in `X`, `res_R tau v = sum_g g v = 0`,
    and `res_R` is injective.

**(T3) Dichotomy.**
- *`P_op = R/Z` implies `res[b] in W(H)`.* `res e(theta b)` lies in `P(H)` for every `theta`. These points form a
  connected subgroup containing `0`, so they lie in `P(H)^0`, and `res[b] in W(H)`.
- *`res[b] in W(H)` implies `P_op = R/Z`.* Then `e(t res b) in P(H)` for all real `t`. By (T1) and (T2),
  `TI(res e(t b)) = e(k t b)` lies in `P(Gamma)` for all `t`, so `P_op = R/Z`.
- *Normal `H`.* `P(H)` is `G`-stable, so `P(H)^0` is `G`-stable, and `W(H)` is a `G`-subrepresentation. Then
  `W(H)^G <= H^2(H,R)^G = R res[b]`. So `W(H)^G != 0` iff `res[b] in W(H)`.
- *Finite branch.* Suppose `P_op` is finite.
  - `TI(P(H)^0)` is a connected subgroup of `P(Gamma)` containing `0`. So it lies in
    `P(Gamma) cap T_0(Gamma)`, which is the finite set `{e(theta b) : theta in P_op}` by (T1). Hence it is `0`, and
    `tau(W(H)) = 0`.
  - For normal `H` this gives `W(H)^G = 0`. A `G`-subrepresentation with no invariant vectors lies in the sum of the
    nontrivial isotypic components (Maschke).
  - `TI` is a homomorphism killing `P(H)^0`, so on `P(H)` it factors through `P(H)/P(H)^0`, which is finite: a
    closed subgroup of a compact Lie group has finitely many components.

**(T4) Exact points.** Let `e(theta b) in R(Gamma)`, realized by an exact `V : Gamma -> U(d)` with multiplier
`e(theta b)`.
- `(g, n) -> e(theta n) V(g)` is an honest unitary representation of the universal extension
  `E_infinity = Gamma x_b Z`, with central generator `z -> e(theta) I`.
- Its image is a finitely generated linear group, hence residually finite (Mal'cev). So if `e(2 theta) != 1`, some
  finite quotient of `E_infinity` does not kill `z^2`.
- That quotient kills some `z^q`, `q >= 1`, and so factors through `E_q`. There `z^2` survives, contradicting
  `deligne-covers-of-sp2g-z-have-finite-residual-2z`: the image of `2Z` dies in every finite quotient of `E_q`.
- Hence `2 theta in Z`.
- On the finite branch, `TI(y + p) = TI(y)` for `p in P(H)^0` by (T3), and `TI(y) in R(Gamma)` by (T1). So a value
  on the Maslov circle lies in `{0, e(b/2)}`.

**Corollary.** Every Hecke correspondence `TI o c_g^* o res` is a composite of the maps above. So on the finite
branch the class killed in the target dies either at `tau`, with invariant `W(H)^G`, or at (T4).

**Imports.** Nothing is imported beyond the three `requires` and Mal'cev's theorem that finitely generated linear
groups are residually finite.
