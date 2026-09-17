---
rg: 2
id: identity-phantom-forces-e-contractibility-proof
kind: route
title: Shift-three argument killing the lim^1 representative of a phantom identity
target: identity-phantom-forces-e-contractibility
requires:
  - carrion-shape-milnor-detects-kk-hausdorffness
  - kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras
---

## Setting and imported facts

`A` is separable and `P = SA (x) K`. `(C_n, gamma_n)` is a shape system for `P`:
the `C_n` are separable, the `gamma_n: C_n -> C_{n+1}` are semiprojective
*-homomorphisms (Blackadar 1985, Def. 2.10), and `P = lim (C_n, gamma_n)`. We write
`gamma_{m,n} = gamma_{m-1} ... gamma_n` and `gamma_{inf,n}: C_n -> P`.
`E(A,A) = [[P,P]]`. `H(C,D)` is the set of *-homomorphisms modulo asymptotic
homotopy, with the quotient of the point-norm topology. `[C,D]` is genuine
homotopy classes. We import the following.

- **(M) Carrion, arXiv:2608.06496, Thm 1.1.** There is a natural exact sequence
  `0 -> lim^1 [C_n, S^2A (x) K] --d--> E(A,A) --Theta--> lim [C_n, SA (x) K] -> 0`
  with `im d = ker Theta = closure{0}`. The tower maps are `gamma_n^*`, and
  `lim^1 G_n = coker(1 - sh)` on `prod_n G_n`, where `sh(x)_n = gamma_n^* x_{n+1}`.
- **(Z) Carrion, Cor. 4.2.** `x` lies in `closure{0}` iff `gamma_{inf,n}^*(x) = 0`
  in `H(C_n, SA (x) K)` for all `n`.
- **(D) CS24 via Carrion Thm 2.2(ii).** `gamma_n^*: H(C_{n+1},D) -> H(C_n,D)`
  factors through a discrete space.
- **(R) CS24 via Carrion Thm 2.2(v).** Let `alpha: C_0 -> C_1` be a
  semiprojective *-homomorphism and `phi, psi: C_1 -> D` *-homomorphisms with
  `[[phi]] = [[psi]]`. Then `phi alpha` is homotopic to `psi alpha` through
  *-homomorphisms.
- **(S) Blackadar, Def. 2.10.** Let `alpha: C_0 -> C_1` be semiprojective,
  `B` a C*-algebra, `J_1 <= J_2 <= ...` ideals with `J` the closure of their
  union, and `phi: C_1 -> B/J` a *-homomorphism. Then for some `n` there is a
  *-homomorphism `C_0 -> B/J_n` lifting `phi alpha`.

**Elementary fact (L).** In `lim^1 = coker(1 - sh)`, the classes of `eta` and
`sh(eta)` agree, because `eta - sh(eta) = (1 - sh)(eta)`. So `class(eta) =
class(sh^k eta)` for every `k`, and `class(eta) = 0` whenever `sh^k eta = 0`
for some `k`.

## Step 1: (b) <=> (c), and (a) => (b)

(a) => (b) is trivial.

`gamma_{inf,n}^*(id_A) = [[id_P circ gamma_{inf,n}]] = [[gamma_{inf,n}]]`.

(c) => (b): if every `gamma_{inf,n}` is null-homotopic, then
`[[gamma_{inf,n}]] = 0`, so `id_A` lies in `closure{0}` by (Z).

(b) => (c): by (Z), `[[gamma_{inf,n+1}]] = [[0]]` in `H(C_{n+1}, P)`. Now
`gamma_{inf,n} = gamma_{inf,n+1} gamma_n`, and `gamma_n` is semiprojective. So
(R) with `phi = gamma_{inf,n+1}` and `psi = 0` shows that `gamma_{inf,n}` is
homotopic to `0` through *-homomorphisms, for every `n`.

Since `S = C_0(R) (x) -` is a functor that carries homotopies to homotopies,
(c) also gives the following.

**(c')** Every `S gamma_{inf,k}: SC_k -> SP` is null-homotopic.

Note that `SP = S^2A (x) K = lim (SC_k, S gamma_k)`, with canonical maps
`S gamma_{inf,k}`, because `C_0(R) (x) -` commutes with inductive limits.

## Step 2: (b) => (a), the shift-three argument

Assume (b). By (M) there is `eta = (eta_n)_n`, with `eta_n: C_n -> SP` a
*-homomorphism representing a class in `[C_n, S^2A (x) K]`, such that
`id_A = d(class eta)`. Fix `m >= 0`. We show `(sh^3 eta)_m = [eta_{m+3} gamma_{m+3,m}] = 0`.

**2a. Lifting into the tower.** Let `iota: SP -> prod_k SC_k / (+)_k SC_k` be the
isometric *-homomorphism that sends `S gamma_{inf,j}(y)` to the class of
`(S gamma_{k,j}(y))_{k >= j}` (zeros for `k < j`). Isometry holds because
`||S gamma_{inf,j} y|| = lim_k ||S gamma_{k,j} y||`; extend by continuity. Let
`B` be the preimage of `iota(SP)` in `prod_k SC_k`, and
`J_N = (+)_{k <= N} SC_k`. Then the closure of the union of the `J_N` is
`(+)_k SC_k`, and `B/J = SP`. Apply (S) with `alpha = gamma_{m+2}: C_{m+2} -> C_{m+3}` and
`phi = eta_{m+3}`. For some `N` we get *-homomorphisms `psi_k: C_{m+2} -> SC_k`
(`k > N`) such that `(psi_k(c))_k` represents `iota(eta_{m+3} gamma_{m+2}(c))`
for all `c`.

**Claim.** If `(b_k)` represents `iota(x)`, then `||S gamma_{inf,k}(b_k) - x|| -> 0`.
Given `eps`, choose `y` in `SC_j` with `||S gamma_{inf,j} y - x|| < eps`. Then
`(b_k - S gamma_{k,j} y)_k` represents `iota(x - S gamma_{inf,j} y)`, which has
norm `< eps`. So `||b_k - S gamma_{k,j} y|| < eps` for large `k`, and
`||S gamma_{inf,k} b_k - x|| <= ||b_k - S gamma_{k,j} y|| + ||S gamma_{inf,j} y - x|| < 2 eps`.

So `rho_k := S gamma_{inf,k} psi_k -> eta_{m+3} gamma_{m+2}` point-norm, as
*-homomorphisms `C_{m+2} -> SP`.

**2b. Discreteness.** Point-norm convergence implies convergence in
`H(C_{m+2}, SP)`, which carries the quotient topology. By (D), `gamma_{m+1}^*`
factors continuously through a discrete space, so the images become constant.
There is `k` such that
`[[rho_k gamma_{m+1}]] = [[eta_{m+3} gamma_{m+2} gamma_{m+1}]]` in `H(C_{m+1}, SP)`.
(The factorization in (D) is by continuous maps, which is the content of the
topological statement in CS24. Without it one can also argue directly:
`gamma_{m+1}` is semiprojective, so point-norm close *-homomorphisms become
homotopic after precomposition with it, which is Blackadar's standard
consequence of Def. 2.10. That gives the same equality, even in `[C_{m+1}, SP]`.)

**2c. Rigidification.** Apply (R) with `alpha = gamma_m`. Then
`rho_k gamma_{m+2,m}` is homotopic to `eta_{m+3} gamma_{m+3,m}` through
*-homomorphisms. Now `rho_k gamma_{m+2,m} = S gamma_{inf,k} circ (psi_k gamma_{m+2,m})`,
and this is null-homotopic by (c'). Hence `[eta_{m+3} gamma_{m+3,m}] = 0` in
`[C_m, S^2A (x) K]`.

**2d. Conclusion.** `m` was arbitrary, so `sh^3 eta = 0`. By (L),
`class eta = 0`, so `id_A = d(0) = 0` in `E(A,A)`. For any `B`, every
`x in E(A,B)` equals `x circ id_A = 0`, and every `x in E(B,A)` equals
`id_A circ x = 0`. So `A` is E-contractible. If `A` is nuclear then
`E(A, -) = KK(A, -)` (Connes–Higson), so `A` is KK-contractible. QED.

**Where the identity is used.** Step 2c needs the canonical maps of the
*target* shape tower to be null (c'). For `id_A` this comes from (b) itself.
For a general phantom `x in E(A,B)` the target tower is that of `SB (x) K`, and
nothing kills it. That is why this argument does not give the general statement
that phantoms square to zero.

## Step 3: calibration

- **UCT case.** For `A` in the UCT class, `closure{0} = Pext(K_*A, K_{*+1}A)`
  (Dadarlat 2005). If `id_A` lies there, its image in `Hom(K_*A, K_*A)` is `id = 0`,
  so `K_* A = 0` and `KK(A,A) = 0`. This agrees with the theorem.
- **Stable homotopy.** For a spectrum `X` whose identity is phantom,
  `id = id^2` is a composite of phantoms, hence zero (Christensen–Strickland
  1998). So `X` is contractible. This is the same shape of statement.
- **No false statement.** The theorem does not claim `KL(A,A) = 0` when
  `K_*A = 0`. That is exactly the open content of Problem II.

## Step 4: the reduction of STW Problem II

**Proposition.** The following are equivalent.

1. Every separable nuclear C*-algebra satisfies the UCT.
2. For every unital Kirchberg algebra `A` with `K_*A = 0`, and a shape system
   of `SA (x) K`, all canonical maps `gamma_{inf,n}` are null-homotopic.

**Proof.**

(1) => (2). UCT with `K_* = 0` gives `KK(A,A) = 0`, which gives (b), which gives (c).

(2) => (1). By the theorem, such `A` is KK-contractible, so it is
KK-equivalent to `O_2`. The classes of the unit are both `0`, so Kirchberg–Phillips
gives `A = O_2`, which satisfies the UCT. Problem II follows from this for all
such `A`, by the existing reduction
`kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras`
(`trivial-k-theory-kirchberg-algebras-are-o2`).

Condition (2) does not depend on the choice of shape system, because (c)
is equivalent to (a).

The contrapositive is the obstruction: a counterexample `A` has
`KL(A,A) != 0`. It is detected at one finite stage `n`, by an essential canonical
map `C_n -> SA (x) K` from a semiprojective algebra. It is never a pure
lim^1 (phantom) phenomenon.
