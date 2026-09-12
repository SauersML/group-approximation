# Anti-central cylinder defects in characteristic three: the independence firewall

Lane `w5-c3-submult`, 2026-09-12. Supports `anti-central-sofic-data-cannot-force-defect-submultiplicativity`
and the open `ternary-disjoint-cylinder-defects-strictly-submultiplicative`. This is the characteristic-three,
anti-central counterpart of:
- `finite-subgroup-data-cannot-force-defect-submultiplicativity`;
- `locally-finite-hnn-data-allow-independent-cylinder-defects`;
- `sofic-subgroups-carry-rank-models-violating-two-root-identity`.

## 0. Setting and scope markers

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `eps_- = (1 - [z])/2 = 2(1 - [z])`, a central idempotent of `F_3[G]`.
- Through the code `(0, 10, 11)`, `G = EL_3(R)`. For a proper cylinder `A`,
  `iota_A(g) = S[A] g T[A] + (1 - S[A]T[A])`.
- An *abstract rank algebra* `(B, rho)` is an `F_3`-algebra with a Sylvester matrix rank function positive on
  nonzero idempotents (Section 7 of `ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`). An
  *anti-central model* is a homomorphism `sigma : G -> B^x` with `sigma(z) = -1`. Rank ultraproducts over fields
  of characteristic three are abstract rank algebras.
- `N^A_ab = sigma(iota_A(x_ab(1))) - 1` and `D_A = N^A_23 N^A_12`.

**Markers.**
- [ring]: an identity valid in every `F_3`-algebra.
- [Sylv]: uses only the Sylvester axioms.
- [mat]: a matricial step (finite-dimensional linear algebra, dimension counts, ultraproducts of matrices).

Sections 1 and 2 are [mat] throughout, but they only *build* counter-models. A counter-model is itself an
anti-central model in an abstract rank algebra. So the firewall of Corollary 2.3 holds for abstract rank
functions, which is the form `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` needs.

**Lemma 0.1 (anti-central models have no fixed vectors) [ring].** If `b` in `B` satisfies `sigma(g) b = b` for
every `g`, then `b = sigma(z) b = -b`, so `2b = 0` and `b = 0`.

So Lemma 2.1 of `two-root-defect-descent-gap-2026-09-12.md`, passing to the fixed-point-free quotient, is
automatic here. By Proposition 7.1(a) of the characteristic-three gate artifact, a nontrivial abstract model
compresses to an anti-central one.

**Remark 0.2 (one defect) [ring].** By `reversed-root-pair-identity-forces-root-squares-to-vanish`,
`N_23 N_12 = 0` forces every `N_ab^2 = 0` in every characteristic. So `D_A` is the only defect to track, as in
characteristic two. The scope of that node is ring identities; it is not re-audited here.

## 1. The anti-central regular profile

**Definition 1.1.** For `alpha` in `F_3[G]` whose support, together with `z`, generates a finite subgroup `K`,
put

```text
rk^-(alpha) = dim_(F_3)( alpha F_3[K] eps_- ) / ( |K| / 2 ) ,
```

the normalized rank of left multiplication by `alpha` on the `|K|/2`-dimensional module `F_3[K] eps_-`.

**Lemma 1.2 [mat].**
- (a) **Well defined.** For finite `K <= K'` containing `z`,
  `F_3[K'] eps_- = (+)_(c in K\K') F_3[K] eps_- c` as left `F_3[K]`-modules. So left multiplication by `alpha`
  has `[K' : K]` times the rank, and the normalized ranks agree.
- (b) **Conjugation invariance.** For every unit `u` of `G`, `alpha -> u alpha u^-1` is an algebra isomorphism
  `F_3[K] -> F_3[uKu^-1]` fixing `eps_-`. So `rk^-(u alpha u^-1) = rk^-(alpha)`.
- (c) **Anti-central.** `(1 - [z]) eps_- = 2 eps_-`, so `rk^-(1 - [z]) = 1`.

**Proposition 1.3 (values).** Let `A_1, ..., A_k` be pairwise disjoint proper cylinders, and put
`H_i = <iota_(A_i)(x_12(1)), iota_(A_i)(x_23(1))>`.
- (a) Each `H_i` is `UT_3(F_3)`, the Heisenberg group of order `27`. The `H_i` commute pairwise, and
  `K = H_1 x ... x H_k x <z>` is a finite subgroup of order `2 · 27^k`.
- (b) `rk^-(N^A_12) = 2/3` and `rk^-((N^A_12)^2) = 1/3`.
- (c) `rk^-(D_A) = 5/9`.
- (d) `rk^-(D_(A_1) ... D_(A_k)) = (5/9)^k`. So the profile has `theta = 1` exactly.

*Proof.*
- (a) The elements `x_ab(r)`, `r` in `F_3`, form `UT_3(F_3)` inside `EL_3(R)`, and `iota_A` is injective.
  Elements of `iota_A(G)` equal `1` on the corner `1 - S[A]T[A]`. For disjoint `A, B`,
  `S[A] a T[A] · S[B] b T[B] = 0`, so the cylinder groups commute, and an element of both is `1` on both
  complementary corners, hence `1`. The product `H_1 x ... x H_k` is a `3`-group, so it does not contain `z`.
- (b) `F_3[H]` is free over `F_3[<x>]` with `9` summands, and `x - 1` acts on `F_3[C_3] = F_3[t]/(t^3)` as `t`,
  of rank `2`; `t^2` has rank `1`. Normalize by `27`.
- (c) Write `x = x_12(1)`, `y = x_23(1)`, `c = [x, y]`, which is central, so `yx = c^-1 xy`.
  - **Basis.** `e_(i,j,k) = x^i y^j c^k`, `i, j, k` in `Z/3`. Left multiplication:
    `L_x e_(i,j,k) = e_(i+1,j,k)` and `L_y e_(i,j,k) = e_(i,j+1,k-i)`.
  - **Reduction.** Put `X = L_x - 1`, `Y = L_y - 1` on `M = F_3[H]`. Then
    `rank(YX) = rank(X) - dim(XM cap ker Y) = 18 - dim(XM cap ker Y)`.
    On free `F_3[t]/(t^3)`-modules `XM = ker X^2`, and `ker Y` is the space of `L_y`-fixed vectors.
  - **Fixed vectors.** `L_y`-orbits of basis vectors are labelled by `(i, w)` with `w = k + ij`. Let `f_(i,w)` be
    the orbit sum. Then `X^2 = 1 + L_x + L_x^2` sends `f_(i,w)` to the indicator of `{(a, b, d) : d + ib = w}`.
  - **The kernel.** `sum a_(i,w) f_(i,w)` lies in `ker X^2` iff `sum_i p_i(d + ib) = 0` on `F_3^2`, where
    `p_i(t) = a_(i,t)`. Write `p_i(t) = alpha_i + beta_i t + gamma_i t^2`. The monomials `1, d, b, d^2, db, b^2`
    are independent functions on `F_3^2`, so the conditions are:
    - `sum alpha_i = 0`, two dimensions;
    - `sum beta_i = sum i beta_i = 0`, one dimension;
    - `sum gamma_i = sum i gamma_i = sum i^2 gamma_i = 0`, a Vandermonde system at `i = 0, 1, 2`, so `gamma = 0`.
  - **Count.** `dim(XM cap ker Y) = 3`, `rank(YX) = 15`, and `rk^-(D_A) = 15/27 = 5/9`.
  - **Calibration.** The same count on `F_2[D_8]` gives `4 - 1 = 3`, the landed `3/8`.
- (d) `F_3[K] eps_- = F_3[H_1] (x) ... (x) F_3[H_k]`, since the `<z>` factor contributes `F_3 eps_-`. `D_(A_i)`
  acts on the `i`-th factor, and the rank of a tensor product of linear maps is the product of the ranks:
  `15^k / 27^k`. QED

**Remark 1.4 (the characteristic-three inputs hold in the profile).**
- **Anti-central sign:** Lemma 1.2(c).
- **Haar law on the signed diagonal:** on every finite torus the profile is the twisted regular representation,
  which is the Haar law (Remark 2.2 of `char-three-level-factoring-and-hnn-models-2026-09-12.md`).
- **Torus normal form** `N = A - A^2`, `A^3 = 0`, `N^2 = A^2`: an identity in every `F_3`-algebra
  (Proposition 7.1(d) of the gate artifact), so it holds in any model realizing the profile. Here
  `rk^-(N^2) = 1/3 > 0`, the projective content of Remark 5.2 there.
- **Weight spaces:** `F_3[T_3] eps_-` is the algebra of functions on the four odd weights, each of rank `1/4`.
- **Reflections inverting roots:** `tau_0 x_12(1) tau_0 = x_12(-1)` is a relation inside a finite subgroup.

## 2. Models realizing the profile

**Theorem 2.1 (locally finite bases and single conjugations) [mat].** Let `L' <= G` be a countable locally finite
subgroup containing `z`, let `U ⊆ G` be countable, and let

```text
Lambda = < L', t_u (u in U) | relations of L', t_u a t_u^-1 = u a u^-1 for a in L' cap u^-1 L' u > .
```

There is a homomorphism `sigma : Lambda -> M^x` into a rank ultraproduct over `F_3`, with `sigma(z) = -1`,
`rho(sigma(alpha)) = rk^-(alpha)` for every `alpha` supported in a finite subgroup of `L'`, and no fixed vectors.

*Proof.* This is Section 2 of `char-three-level-factoring-and-hnn-models-2026-09-12.md` (Theorems 2.1 and 2.3,
Corollary 2.4), with the level unit group replaced by an exhaustion `L' = union K_n` by finite subgroups
containing `z`.
- **Tower.** `V_n = F_3[K_n] eps_-` with left multiplication. Lemma 1.2(a) gives compatibility and the values.
- **Letters.** `B_u = L' cap u^-1 L' u` is exhausted by finite `Gamma_i` containing `z`, and
  `phi_u(Gamma_i) = u Gamma_i u^-1` has the same order and contains `z`. At a stage `n` containing both, `V_n` is
  free over `F_3[Gamma_i] eps_-` through `a -> sigma_n(a)` and through `a -> sigma_n(phi_u(a))`, with the same rank
  `[K_n : Gamma_i]`. Free modules of equal rank are isomorphic, so an exact intertwiner exists at every stage, with
  the moving index of Theorem 2.3 there.
- **No fixed vectors:** Lemma 0.1. QED

**Theorem 2.2 (sofic subgroups) [mat].** Let `S <= G` be a sofic subgroup containing `z`. Then `S` has an
anti-central rank model over `F_3` with `rho(sigma(alpha)) = rk^-(alpha)` for every `alpha` supported in a finite
subgroup of `S`.

*Proof.*
- **Linearize.** Take a sofic approximation `phi_i : S -> Sym(n_i)`; for `g != 1` the proportion of fixed points
  of `phi_i(g)` tends to `0`. The permutation matrices `P_i(g)` over `F_3` give a homomorphism
  `tau : S -> M^x`, since `P_i(g)P_i(h) - P_i(gh)` has rank at most the proportion of points where the
  approximation is not multiplicative.
- **Compress.** `f = 2(1 - tau(z))` is an idempotent, because `tau(z)^2 = 1`, and it commutes with `tau(S)`
  because `z` is central. Put `sigma(g) = tau(g) f` on `fMf`, renormalized.
- **Values.** A finite `K <= S` containing `z` acts freely on all but `o(n_i)` points, so `F_3^(n_i)` is, up to
  `o(n_i)` coordinates, a free `F_3[K]`-module of rank `n_i/|K|`. Its `eps_-`-part is free over `F_3[K] eps_-`
  of the same rank and has dimension `n_i/2 + o(n_i)`. So `rho(f) = 1/2` and `rho(sigma(alpha)) = rk^-(alpha)`. QED

This is the anti-central form of `sofic-subgroups-carry-rank-models-violating-two-root-identity`.

**Corollary 2.3 (the firewall).** Let `A_1, ..., A_k` be pairwise disjoint proper cylinders whose frames `H_i` lie
in `L'`, or in `S`. In the models of Theorems 2.1 and 2.2:

```text
rho(N^A_12) = 2/3 ,     rho(D_A) = 5/9 ,     rho(D_(A_1) ... D_(A_k)) = (5/9)^k .
```

So no inequality `rho(D_A D_B) <= theta rho(D_A) rho(D_B)` with `theta < 1`, for anti-central models of `G`,
follows only from:
- identities among elements of one sofic subgroup containing `z` and the frames;
- identities of one locally finite subgroup containing `z`, together with single conjugations by arbitrary units;
- the anti-central sign, the Haar law, the torus normal form, the weight-space ranks, and reflections inverting
  roots;
- rank calculus in abstract rank algebras, nontriviality, and absence of fixed vectors.

Because the models are abstract rank algebra models, the same holds for rank functions. In particular, a proof of
`sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` that uses `F_3[S]` for a sofic `S` containing
`z` fails on Theorem 2.2, where `rk(1 - [z]) = 1`.
