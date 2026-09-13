---
rg: 2
id: sp4-finite-index-scalar-data-hyperlinear-covers-proof
kind: route
title: Compact multiplier topology, central Fourier summands, multiplier finiteness and corners
target: sp4-finite-index-scalar-data-iff-hyperlinear-covers
requires:
  - sp4-finite-index-fd-projective-multiplier-is-finite
  - maslov-ce-parameter-set-is-a-closed-subgroup
---

Notation as in the target.  "CE" means Connes embeddable.  Cohomologous
cocycles give isomorphic twisted group algebras (`u_g -> b(g) u_g`), so CE
depends only on the class.  CE passes to von Neumann subalgebras, corners,
finite direct sums, tensor products, complex conjugates and ultraproducts.

**Step 0 (topology).**  `Z^2(Gamma',T)` is closed in the compact metrizable
`T^(Gamma' x Gamma')`, and `B^2 = d(T^Gamma')` is compact, hence closed.  So
`H^2(Gamma',T) = Z^2/B^2` is compact metrizable.  Since `T` is divisible,
`H^2(Gamma',T) = Hom(H_2(Gamma'),T)` (universal coefficients; the Ext term
vanishes, as Fournier-Facio--Willett note, arXiv:2603.18456v2, p. 25).
Evaluation on 2-cycles is continuous, and a continuous bijection from a
compact space is a homeomorphism.  `Gamma'` is finitely presented, so
`H_2(Gamma') = Z^b + F` with `F` finite and `b = b_2(Gamma')`, and
`H^2(Gamma',T) = T^b x F^`.  Its identity component `T_0` is the torus
`Hom(H_2(Gamma'),R)/Hom(H_2(Gamma'),Z)`.

**Step 1 (`E_CE(Gamma')` is a closed subgroup).**
- Products: `u_g -> u_g (x) v_g` is a trace-preserving embedding of
  `L_(omega eta)` into `L_omega (x) L_eta`.
- Inverses: `L_(omega-bar)` is the complex conjugate algebra of `L_omega`.
- Unit: `L(Gamma')` is CE, since `Gamma'` is residually finite.
- Closedness: the quotient map `Z^2 -> H^2` is open, so `omega_k -> omega`
  lifts to cocycles `c_k -> c` pointwise.  The unitaries
  `U_g = (u_g^(k))_k` in the ultraproduct of the `L_(c_k)(Gamma')` satisfy
  `U_g U_h = c(g,h) U_(gh)` and `tau(U_g) = delta_(g,e)`, so they give a
  trace-preserving copy of `L_c(Gamma')`.

**Step 2 (1 => 2).**  Pointwise convergence gives `[c_n] -> 0`, evaluating
on 2-cycles, and the classes are nonzero.  So `0` is not isolated in the
closed subgroup `E_CE(Gamma')` of a compact Lie group, which therefore has
positive dimension.

**Step 3 (2 => 3).**
- The identity component `S` of `E_CE(Gamma')` is a torus of positive
  dimension in `T_0`.  Subtori correspond to rational subspaces, so `S`
  contains a circle `t -> t.v` (`t in R/Z`) with
  `0 != v in Hom(H_2(Gamma'),Z)`.
- The universal coefficient surjection `H^2(Gamma',Z) -> Hom(H_2(Gamma'),Z)`
  lifts `v` to `x`, of infinite order.  Evaluating the integral cocycle on
  cycles gives `[e(t x)] = t.v`.
- Fourier decomposition along the central `Z/n`:

  ```text
  L(E_x^(n)) = direct_sum_(j=0)^(n-1) L_(e(jx/n))(Gamma').      (FIC4)
  ```

  Every summand lies in `S`, so `L(E_x^(n))` is CE and `E_x^(n)` is
  hyperlinear.

**Step 4 (3 => 1).**
- `t -> [e(tx)]` has kernel `(1/d)Z/Z`, where `dZ = v(H_2(Gamma'))`.
- For primes `p` not dividing `d`, `c_p = e(x/p)` is not a coboundary, and
  `c_p(g,h) -> 1` pointwise as `p -> infinity` because `x` is a fixed integral
  cocycle.
- `L_(c_p)(Gamma')` is the `j = 1` summand of `(FIC4)` at `n = p`, hence CE.

**Step 5 (`E_x` hyperlinear under 3).**  The regular trace of `E_x^(p)`
pulls back to the trace on `E_x` that is `1` on the central subgroup `pZ`
and `0` off the centre.  As `p -> infinity` through primes this converges
pointwise to `delta_e`.  So `L(E_x)` embeds trace-preservingly in the
ultraproduct of the `L(E_x^(p))`.

**Step 6 (FIC2).**
- `E_x^(n)` has property (T), as a finite central extension of the Kazhdan
  group `Gamma'`.  An amenable Kazhdan group is finite, so residual
  amenability forces residual finiteness.
- If `E_x^(n)` is residually finite, finitely many finite quotients separate
  the nonzero elements of the central `Z/n`.  So some finite quotient `Q` is
  injective on the centre.
- The regular representation of `Q` contains every central character.  An
  irreducible summand with generating character `chi_j` (`gcd(j,n) = 1`),
  composed with a section `Gamma' -> E_x^(n)`, is a finite-dimensional
  projective representation of `Gamma'` with class `[e(jx/n)]`.  So
  `[e(jx/n)]` lies in `R(Gamma')`, which is finite by
  `sp4-finite-index-fd-projective-multiplier-is-finite`.
- The class `[e(jx/n)] = (j/n).v` has order `n/gcd(n,d)`, because
  `gcd(j,n) = 1`.  A finite set has bounded orders, so only finitely many `n`
  qualify.

**Step 7 (FIC3).**
- **Restriction on identity components.**  Corestriction after restriction
  is multiplication by `m` on real cohomology, so restriction
  `H^2(Gamma,R) -> H^2(Gamma',R)` is injective.  `H_2(Sp_4(Z))` has rank one
  (`sp4-fd-projective-multiplier-is-finite`, cited on the required
  multiplier node).  With `b = 1`, restriction maps the Maslov circle onto
  `T_0(Gamma')` by a finite covering.
- **Induction.**  Take coset representatives `s_i`.  Twisted right
  translations `rho(k) delta_h = c(h,k) delta_(hk)` commute with the twisted
  left regular representation, by the cocycle identity.
  `V_i delta_k = c(s_i,k) delta_(s_i k)` identifies `l^2(Gamma)` with
  `l^2(Gamma') (x) C^m`, intertwining `rho|Gamma'` with `rho' (x) 1`.  Hence
  `L_c(Gamma) <= L_(c|)(Gamma') (x) M_m`, and the trace is preserved:
  `<lambda_c(g) delta_(s_i), delta_(s_i)> = 0` for `g != e`.
- **Conclusion.**  `L_c(Gamma)` is CE iff `L_(c|Gamma')(Gamma')` is: one
  direction is the embedding just built, the other the twisted group
  subalgebra.  So positive dimension at `Gamma'` is equivalent to
  `E_CE(Gamma) = R/Z`.  That is the second alternative of
  `maslov-ce-parameter-set-is-a-closed-subgroup`, equivalent there to the
  null-sequence claim `sp4-small-maslov-twisted-group-factors-are-ce`.

**Step 8 (FLA1).**
- **Setup.**  Let `x_0 = Gamma'` in `X = Gamma/Gamma'`, with
  `(sigma_g f)(x) = f(g^(-1) x)`.
- **Restriction to the base point.**  Define `c_n'(h,k) = c_n(h,k)(x_0)` for
  `h, k in Gamma'`.  Every `sigma_h` with `h in Gamma'` fixes `x_0`, so the
  twisted cocycle identity at `x_0` makes `c_n'` a 2-cocycle of `Gamma'`, and
  `|c_n'(h,k) - 1| <= sqrt(m) ||c_n(h,k) - 1||_2 -> 0`.
- **Non-coboundary (Shapiro).**
  - `F(gamma) = f(gamma^(-1) x_0)` identifies `U(A)` with the coinduced
    module `Map_(Gamma')(Gamma,T)`, and `f(x_0)` with `F(e)`.
  - The Eckmann--Shapiro adjunction
    `Hom_(ZGamma)(P, Map_(Gamma')(Gamma,T)) = Hom_(ZGamma')(P,T)`,
    `phi -> phi(.)(e)`, applied to the bar resolution `P` of `Gamma` (a free
    `ZGamma'`-resolution), then compared with the bar resolution of `Gamma'`
    by inclusion, gives an isomorphism `H^2(Gamma,U(A)) -> H^2(Gamma',T)`.
  - This isomorphism is `[c] -> [c']`, so `c_n'` is not a coboundary.
- **Corner.**  Let `p = 1_(x_0)` in `A x|_(c_n) Gamma`.
  - `u_g^* p u_g = 1_(g^(-1) x_0)`, so `p u_g p = 0` unless `g in Gamma'`.
    For `h in Gamma'`, `p u_h` commutes with `p`.
  - `(p u_h)(p u_k) = c_n'(h,k) p u_(hk)`, and the renormalized trace is
    `m tau(p u_h) = delta_(h,e)`.
  - So `p (A x|_(c_n) Gamma) p` is `L_(c_n')(Gamma')`, trace-preservingly.
    A corner of a CE algebra is CE.  QED.
