---
rg: 2
id: central-extension-residual-is-schur-obstruction-image-proof
kind: route
title: Traces on the free group algebra, central Fourier sectors, a split transgression and the five-term sequence of the residual
target: central-extension-residual-is-schur-obstruction-image
requires:
  - hyperlinear-shadow-schur-cokernel-criterion
---

## Why sufficient

All groups are countable. "CE" means Connes embeddable. `Res(K)` is the
hyperlinear residual; we use (P0)(i)-(iii) of
`hyperlinear-shadow-schur-cokernel-criterion-proof`: `K/Res(K)` is
hyperlinear, `K/C` hyperlinear implies `Res(K) <= C`, and surjections map
residuals into residuals. A countable group `K = F/S` is hyperlinear iff the
trace `w -> 1_S(w)` on `C*(F)` is CE, because its GNS algebra is `L(K)`.

Standard facts used without proof:
- (T1) A tracial state on a separable C*-algebra is CE iff it has matricial
  microstates. CE traces form a weak*-closed convex set: closed by a diagonal
  choice of microstates, convex because direct sums with rational weights are
  realized in matrix algebras and closure handles real weights.
- (T2) CE passes to von Neumann subalgebras, direct summands `M z` with `z`
  a central projection, tensor products and complex conjugate algebras.
- (T3) Positive trigonometric polynomials `p >= 0` with `integral p = 1` are
  weak*-dense in the probability measures on a compact metrizable abelian
  group.

**(S0) Twists and their classes.** Fix `Q = F/R`, `A = H_2(Q) =
(R cap [F,F])/[F,R]` (Hopf). Since `R/(R cap [F,F]) = R[F,F]/[F,F]` is a
subgroup of the free abelian group `F^ab`, it is free, so

```text
R/[F,R] = A (+) Tbar,   Tbar free abelian.                     (SP0)
```

For an `F`-invariant homomorphism `lambda : R -> T` (it kills `[F,R]`
automatically), `tau_lambda(w) = lambda(w) 1_R(w)` is a tracial state on
`C*(F)`: it is the canonical trace of the twisted group algebra of `Q` for a
cocycle representing `lambda` (choose a set-theoretic section `Q -> F`). If
`lambda, lambda'` agree on `R cap [F,F]`, then `lambda'/lambda` factors
through `R/(R cap [F,F]) <= F^ab`. Since `T` is divisible it extends to a
character `psi` of `F`, and the automorphism `u_x -> psi(x) u_x` of `C*(F)`
carries `tau_lambda` to `tau_lambda'`. So CE of `tau_lambda` depends only on
`chi = lambda|_(R cap [F,F]) in Hom(A,T)`, and by (SP0) every `chi` arises.

**(S1) Item 1.**
- *Unit.* `chi = 0` comes from `lambda = 1`, whose GNS algebra is `L(Q)`, CE
  since `Q` is hyperlinear.
- *Products.* `u_x -> u_x (x) v_x` defines a `*`-homomorphism
  `C*(F) -> L_lambda (x) L_mu` with `tau_lambda (x) tau_mu` pulling back to
  `tau_(lambda mu)`, since for `w in R` both factors are scalars and for
  `w notin R` both traces vanish. So `L_(lambda mu)` is a von Neumann
  subalgebra of `L_lambda (x) L_mu` (T2).
- *Inverses.* `tau_(lambda-bar)` is the complex conjugate trace; its GNS
  algebra is the conjugate algebra (T2).
- *Closedness.* If `chi_n -> chi` pointwise on `A`, extend all of them by the
  same homomorphism on `Tbar` (SP0). The resulting `lambda_n -> lambda`
  pointwise on `R`, so `tau_(lambda_n) -> tau_lambda` pointwise on `F`,
  hence weak* on `C*(F)`. By (T1) the limit of CE traces is CE.

So `W(Q)` is a closed subgroup of the compact group `Hom(A,T) = A^`, and by
Pontryagin duality `W(Q) = ann(ann W(Q)) = ann B(Q)`.

**(S2) Fibre criterion.** Let `1 -> C -> E -> Q -> 1` be central. Write
`E = F/K` with `[F,R] <= K <= R` and `C = R/K`. For `psi in C^` put
`lambda_psi = psi o (R -> R/K)`. Its class is `psi o delta_E`, where
`delta_E : A -> C` is induced by `R cap [F,F] -> R/K`; this is the
five-term transgression (Hopf's description). *Claim:* `E` is hyperlinear
iff `psi o delta_E in W(Q)` for every `psi in C^`.
- For `w in F`, `1_K(w) = integral_(C^) tau_(lambda_psi)(w) d psi`, by
  orthogonality of characters for `w in R` and because both sides vanish for
  `w notin R`. The map `psi -> tau_(lambda_psi)(w)` is continuous.
- (<=) `tau_E = w -> 1_K(w)` is the barycenter of a probability measure
  carried by CE traces. By (T1) it is CE, so `E` is hyperlinear.
- (=>) Fix `psi_0`. By (T3) choose trigonometric polynomials `p_n >= 0` on
  `C^`, `integral p_n = 1`, with `p_n d psi -> delta_(psi_0)`. The element
  `f_n = sum_c phat_n(c) u_c in L(C) <= L(E)` is central (C is central) and
  positive. `tau_n(x) = tau_E(x f_n)` is a normal tracial state on `L(E)`,
  so its GNS algebra is a direct summand `L(E) z_n` of `L(E)`, CE by (T2).
  On `F`, `tau_n(w) = integral tau_(lambda_psi)(w) p_n(psi) d psi ->
  tau_(lambda_(psi_0))(w)`. By (T1) `tau_(lambda_(psi_0))` is CE.

**(S3) Item 2, (SO1).** For `C' <= C`, `E/C'` is a central extension of `Q`
by `C/C'` with transgression `delta_E` followed by `C -> C/C'` (naturality of
(S2)'s description). By (S2) and item 1, `E/C'` is hyperlinear iff
`psi(delta_E B(Q)) = 1` for every character `psi` of `C` trivial on `C'`,
iff `delta_E(B(Q)) <= C'` (characters of `C/C'` separate points).
- `Q` is hyperlinear, so `Res(E) <= C`, and `E/Res(E)` is hyperlinear.
  Taking `C' = Res(E)` gives `delta_E(B(Q)) <= Res(E)`.
- Taking `C' = delta_E(B(Q))`, `E/C'` is hyperlinear, so `Res(E) <= C'`.

Hence `Res(E) = delta_E(B(Q))`, and `E` is hyperlinear iff it is `0`.

**(S4) Item 3, (SO2).** Let `G = F/S` with `N = Res(G) = R/S` and
`Q = F/R`. Then `[N,G] = S[F,R]/S` and `E(G) = G/[N,G] = F/S[F,R]`, a central
extension of `Q` by `D(G) = R/S[F,R]` with transgression
`delta_G : A -> D(G)` induced by inclusion. By
`hyperlinear-shadow-schur-cokernel-criterion` items 1-2, `delta_G` is onto,
its kernel is the image of `H_2(G)` (five-term sequence), and
`Res(E(G)) = D(G)`. By (S3), `Res(E(G)) = delta_G(B(Q))`. So
`delta_G(B(Q)) = D(G) = delta_G(A)`, which is `A = B(Q) + ker delta_G`,
i.e. (SO2).

**(S5) Item 4.** With (SP0), let `K <= R` be the preimage of `Tbar`. Every
subgroup between `[F,R]` and `R` is normal in `F`, since `R/[F,R]` is
central in `F/[F,R]`. Put `E_Q = F/K`: a central extension of `Q` by
`R/K = A`, whose transgression `A -> R/K` is the identity. By (S3),
`Res(E_Q) = B(Q)`. It is central, so `D(E_Q) = Res/[Res,E_Q] = B(Q)`, and
the shadow is `E_Q/B(Q)`.

**(S6) Item 5.**
- (C) => `B(Q) != 0`: a non-hyperlinear central extension `E` of `Q` has
  `delta_E(B(Q)) = Res(E) != 0` (S3).
- `B(Q) != 0` => (C): `E_Q` has `Res(E_Q) = B(Q) != 0`.
- (F) => `B(Q)` not in `R_fin(A)`: a non-hyperlinear extension by `Z/p` has
  `delta_E(B(Q)) != 0`. But `delta_E(pA) = p delta_E(A) = 0`, so
  `B(Q) not<= pA`, hence `B(Q) not<= R_fin(A)`.
- `B(Q)` not in `R_fin(A)` => `B(Q)` not divisible: a divisible subgroup
  `B` satisfies `B = mB <= mA` for all `m`.
- `B(Q)` not divisible => (F): choose a prime `p` with `pB != B` and
  `B' <= B` with `B/B' = Z/p` (a quotient of the `F_p`-vector space
  `B/pB`). `B'` is central in `E_Q`. The group `H_Q = E_Q/B(Q)` is
  hyperlinear, and `E_Q/B'` is a central extension of `H_Q` by `B/B' = Z/p`.
  By (P0)(iii) its residual contains the image `B/B'` of
  `Res(E_Q) = B`, so it is non-hyperlinear.

**(S7) Item 6.** If `Q` is perfect, `F = [F,F]R`. From (SP0),
`R = (R cap [F,F])K`, so `F = [F,F]K`, and `[F,F]/[F,R] -> F/K` is onto with
kernel `([F,F] cap K)/[F,R] = A cap Tbar = 0`. So `E_Q = [F,F]/[F,R]` is the
universal central extension, with `H_1(E_Q) = H_2(E_Q) = 0`. The five-term
sequence for `1 -> B -> E_Q -> H_Q -> 1` (central `B = B(Q)`) reads
`0 -> H_2(H_Q) -> B -> 0`, so `H_2(H_Q) = B`, and `H_Q` is perfect. The
shadow of `E_Q` is `H_Q`, and (SO2) with `im H_2(E_Q) = 0` gives
`B(H_Q) = H_2(H_Q)`.

**(S8) Item 7.** For `w notin R`, `w notin R_n`, so both traces vanish. For
`w in R`, Chabauty convergence gives `w in R_n` for large `n`, and then
`tau_(lambda|R_n)(w) = lambda(w)`. So `tau_(lambda|R_n) -> tau_lambda`
pointwise. The CE traces are closed (T1), so the non-CE ones are open, and
`lambda|R_n` is non-CE for large `n`. `Q_n` is hyperlinear, so
`B(Q_n) != 0` by item 1.
- If `lambda(R_n)` is finite, it is a finite cyclic subgroup of `T`, and
  `F/ker(lambda|R_n)` is a central extension of `Q_n` by it. Its fibre at the
  inclusion character is `tau_(lambda|R_n)`, which is non-CE, so the extension
  is non-hyperlinear by (S2). By (S3), `B(Q_n)` has a nonzero finite image,
  so it is not divisible, and (S6) gives (F).
- If `H_2(Q_n)` is residually finite, its divisible subgroups are `0`, so
  `B(Q_n) != 0` is not divisible, and (S6) gives (F). Finitely presented
  groups have finitely generated `H_2`.

The biography follows: under (C) and not (F), item 5 makes every `B(Q)`
divisible, and item 7 forces the stated properties of hyperlinear covers.
The finitely presented covers `F/<<R cap Ball_k>>` converge to `Q`, and they
are eventually non-hyperlinear because (F) fails.

**(S9) Killed routes.** For `omega in Hom(A,R)`, `t -> e(t omega)` is a
continuous homomorphism `R -> Hom(A,T)`, so `{t : e(t omega) in W(Q)}` is a
closed subgroup of `R`, either `R` or `aZ`. It is proper iff some
`t omega(b) notin Z` with `b in B(Q)`, iff `omega(B(Q)) != 0`. For
`Q <= Q'`, restriction of twists gives trace-preserving inclusions
`L_(chi' o i_*)(Q) <= L_(chi')(Q')`, so `chi' in W(Q')` implies
`chi' o i_* in W(Q)`, hence `i_* B(Q) <= B(Q')`. Homomorphic images of
divisible groups are divisible.

**Calibration.** On a finitely presented `Q`, `A` is finitely generated, has
no nonzero divisible subgroup, and item 5 says `W(Q) != Hom(A,T)` gives a
finite witness, as the torsion-density node also gives. On amenable `Q`,
every `L_lambda(Q)` is injective, so `B(Q) = 0` and (SO1) says every central
extension of an amenable group is hyperlinear, which is true.
