---
rg: 2
id: dkkms-near-perfect-labellings-are-outer-honest-proof
kind: route
title: Prove a spectral gap 1/2 for the Grassmann down-up walk, deduce 20-delta rigidity of linear subspace tables by plurality on vector links and BLR, apply it per k-tuple through two extensions of one B-vertex and the covering lemma, let folding force the equations, and glue over V by the 2^(1-l) agreement bound
target: dkkms-near-perfect-labellings-are-outer-honest
requires: [dkkms-2to1-instances-satisfy-selector-decoding-hypotheses]
artifacts:
  - experiments/dkkms-rigidity-2026-09-17/check_grassmann_rigidity.py
---

The notation is that of the target claim and of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, whose item 4
(the law of `U` under `G_multi` is uniform) is the only result of that node
used here. Quotations are from Dinur, Khot, Kindler, Minzer and Safra, ECCC
TR16-198. The construction and the covering lemma are theirs; they credit
Lemma 4.9 to Khot, Minzer and Safra ([18] there). Superscripts are restored
where the text extraction lost them (`2^𝓁` for "2𝓁", `2^(𝓁+4)` for "2𝓁+4").

## Quoted inputs

* **(Q1) Parameters.** "The veriﬁer has parameters k≫𝓁 and
  β = log logk/k >0."
* **(Q2) Edges.** "1. Choose a k-tupleU = (e1,...,e k)∈U uniformly at random
  and then construct a k-tupleV such that independently for 1 ⩽i ⩽k, theith
  element ofV is the equationei with probability 1−β and is a variable in the
  equationei with probabilityβ. 2. Choose a random L′∈Gr(XV,𝓁− 1) and a
  randomL∈Gr(XU,𝓁 ) such thatL′⊆L. 3. Output (U,L ), (V,L′)."
  Also "A ={(U,L )|U∈U , L∈Gr(XU,𝓁 ), L∩HU ={0}}".
* **(Q3) Labels and constraint.** "σ ∈ ΣA is interpreted as a linear function
  σ :L→ F2 andσ∈ ΣB is interpreted as a linear functionσ :L′→ F2 ... The
  constraint between (U,L ) and (V,L′) accepts pairs (σ,σ′) iff σ|L′ =σ′."
* **(Q4) Unfolding.** "ifL∩H =φ then any linear functionf :L→ F2 has a unique
  (H,h )-extension, ˜f :L +H→ F2, where ˜f(z) =f(x) +h(y) and wherez =x +y is
  the unique way to writez as a sum ofx∈L andy∈H." Definition 4.2: "For every
  (U,L )∈C we unfold σ = ˜A(C) by deﬁning,A(U,L ) = ˜σU|L, where ˜σU is the
  (HU,hU) extension ofσ".
* **(Q5) Invariance.** "For each U ∈U , let FU[·] be an assignment for
  Gr(XU,𝓁 ) deﬁned by FU[L] = A(U,L ). ... It is clear by unpacking the
  deﬁnitions that the tableFU[·] is invariant under (HU,hU) (explicitly: If
  L1 +HU =L2 +HU then both are equal to R +HU and ˜σ : R +HU→ F2 must equal
  the (HU,hU) extension ofA(U,L 1) as well as the (HU,hU) extension
  ofA(U,L 2).)."
* **(Q6) Covering.** Definition 4.8: "LetU∈U . Let𝓁 > 1 be an integer.
  LetL,L′ be distributions over𝓁-dimensional subspaces ofXU sampled as
  follows. • L: Choose a uniformly random𝓁-dimensional subspace ofXU.
  • L′: Choose a random V ⊆ U as in the edge distribution of Gunfolded, and
  then choose a uniformly random𝓁-dimensional subspace ofXV ." Lemma 4.9:
  "Suppose 2^𝓁β ⩽ 1/8. LetL,L′ be distributions over𝓁-dimensional subspaces
  overXU sampled as in Deﬁnition 4.8. Then the statistical distance betweenL,L′
  is bounded as SD(L,L′) ⩽β√k· 2^(𝓁+4)."

We apply (Q6) with `𝓁 := l - 1`. This is allowed because `l >= 3` gives
`l - 1 > 1`, and `2^(l-1) beta <= 1/8` is a hypothesis of Theorem R. The
bound is then `beta sqrt(k) 2^(l+3)`.

Standard facts used without citation, with a proof or a one-line reason:
* `GL_N(F_2)` acts transitively on flags of each fixed type, and so on pairs
  of `j`-spaces with a given intersection dimension.
* `AB` and `BA` have the same nonzero eigenvalues with multiplicities.
* Parseval.

## Step 1: spectral gap of the Grassmann down-up walk

Fix `n` and write `G_j = Gr(F_2^n, j)` with the uniform measure `pi_j`. For
`1 <= j <= n` define the averaging operators, where `M` ranges over
`(j-1)`-spaces:

```text
(Up_j f)(L)   = E_(M < L, dim M = j-1) f(M)     functions on G_(j-1) -> on G_j
(Dn_j f)(M)   = E_(L > M, dim L = j)   f(L)     functions on G_j -> on G_(j-1)
```

The uniform flag `(M < L)` has both marginals uniform, by transitivity. Both
`<Up_j f, F>_(pi_j)` and `<f, Dn_j F>_(pi_(j-1))` equal `E_flag f(M) F(L)`, so
`Up_j` and `Dn_j` are adjoint.

The **down-up walk** on `G_d` is `W_d := Up_d Dn_d`. From `L_1` it picks a
uniform hyperplane `M` of `L_1` and then a uniform `d`-space `L_2 > M`. It
equals `Dn_d^* Dn_d`, so it is self-adjoint and positive semidefinite. Its
top eigenvalue is `1` on constants. Let `lambda(d)` be its largest eigenvalue
on functions orthogonal to constants.

**Lemma 1.** `lambda(d) <= u_d := (2^(d-1) - 1)/(2^d - 1) < 1/2` for every
`1 <= d <= n`, and `lambda(1) = 0`.

*Proof.* `W_1` picks `M = {0}` and then a uniform point, so `W_1` is the
projection on constants and `lambda(1) = 0 = u_1`.

Let `d >= 2`. Let `J` be the operator on `G_(d-1)` that averages over the
`(d-1)`-spaces `M_2` with `dim(M_1 meet M_2) = d - 2`.

* **Up-down.** `Dn_d Up_d` goes `M_1 -> L > M_1 -> M_2 < L`. Then `M_2 = M_1`
  with probability `p_d = 1/(2^d - 1)`, since `L` has `2^d - 1` hyperplanes.
  Otherwise `M_1, M_2` are distinct hyperplanes of `L`, so
  `dim(M_1 meet M_2) = d - 2`. The process is equivariant under the stabiliser
  of `M_1`, which is transitive on such `M_2`. So, conditioned on
  `M_2 != M_1`, `M_2` is uniform on them. Hence
  `Dn_d Up_d = p_d I + (1 - p_d) J`.
* **Down-up.** `W_(d-1) = Up_(d-1) Dn_(d-1)` goes `M_1 -> K < M_1 -> M_2 > K`.
  Then `M_2 = M_1` with probability `q_d = 1/(2^(n-d+2) - 1)`, since a
  `(d-2)`-space lies in `2^(n-d+2) - 1` spaces of dimension `d-1`. Otherwise
  `M_1 meet M_2 = K`, and `M_2` is uniform on the same orbit. Hence
  `W_(d-1) = q_d I + (1 - q_d) J`.

Eliminating `J` gives

```text
Dn_d Up_d = p_d I + (1 - p_d) (W_(d-1) - q_d I) / (1 - q_d).
```

On the orthogonal complement of the constants, which both operators preserve,
the eigenvalues of `Dn_d Up_d` are therefore at most

```text
p_d + (1 - p_d) max(0, (lambda(d-1) - q_d)/(1 - q_d))
    <= 1 - (1 - p_d) (1 - lambda(d-1)),
```

using `1 - (lambda - q)/(1 - q) = (1 - lambda)/(1 - q) >= 1 - lambda`.

`W_d = Up_d Dn_d` and `Dn_d Up_d` have the same nonzero eigenvalues with
multiplicities. Both have eigenvalue `1` exactly once: for `Dn_d Up_d` this is
the bound above, and for `W_d` it follows from the equality of spectra.
Therefore `1 - lambda(d) >= (1 - p_d)(1 - lambda(d-1))`. Iterating from
`lambda(1) = 0`,

```text
1 - lambda(d) >= prod_(j=2..d) (2^j - 2)/(2^j - 1) = 2^(d-1)/(2^d - 1),
```

because the product telescopes:
`prod 2 (2^(j-1) - 1)/(2^j - 1) = 2^(d-1) (2^1 - 1)/(2^d - 1)`. This is the
claim. []

**Poincare form.** Let `L_1` be uniform and `L_2 ~ W_d(L_1, .)`. For
`f : G_d -> {0,1}` with `a = E f`,

```text
Pr[f(L_1) != f(L_2)] = 2 <f, (I - W_d) f> >= 2 (1 - lambda(d)) a (1 - a) >= (1 - lambda(d)) min(a, 1 - a).    (1)
```

The artifact computes `lambda(d)` exactly for `n <= 7`, `d <= 3`. It finds
`0.2222, 0.2857, 0.3111, 0.3226, 0.3280` at `d = 2` and `n = 3..7`, against
`u_2 = 1/3`. It finds `0.2857, 0.3673, 0.4000` at `d = 3` and `n = 4..6`,
against `u_3 = 3/7`. So the bound is approached as `n` grows.

## Step 2: 99 percent rigidity of linear subspace tables

Let `N >= 3` and `2 <= l <= N`. A *linear table* on `Gr(F_2^N, l)` is a map
`F` that gives every `l`-space `L` a linear functional `F[L] : L -> F_2`. The
*test* `T` picks a uniform `(l-1)`-space `L'`, then two independent uniform
`l`-spaces `L_1, L_2 > L'`, and rejects iff `F[L_1]|_(L') != F[L_2]|_(L')`.
Write `delta = rej_T(F)`.

**Lemma 2.** Some linear `g* : F_2^N -> F_2` has
`Pr_(L uniform) [F[L] != g*|_L] <= C_l delta`, where

```text
C_l = (8 + 12 * 2^(-N)) / kappa_l,     kappa_l = 1 - u_(l-1) = 2^(l-2)/(2^(l-1) - 1).
```

Since `kappa_2 = 1` and `kappa_l > 1/2`, one has `C_l <= 16 + 24 * 2^(-N) <= 19
<= 20` for every `l >= 2` and `N >= 3`. The same bound holds for every
minimiser of `g -> Pr_L[F[L] != g|_L]`, and in what follows `g*` denotes such a
minimiser.

*Proof.* Throughout, "`(z, L)` in the flag law" means that `z` is a uniform
nonzero vector and `L` a uniform `l`-space containing `z`. Equivalently, `L`
is uniform and `z` is a uniform nonzero vector of `L`, by transitivity.

**(a) Plurality on vector links.** For `z != 0` let `g(z)` be the more
frequent value of `F[L](z)` over `L > z`, and put `g(0) = 0`. Put

```text
delta_1 := Pr_((z,L) flag law) [F[L](z) != g(z)].
```

In the test `T`, let `z` be a uniform nonzero vector of `L'`. Rejection
happens whenever `F[L_1](z) != F[L_2](z)`. The triple `(z, L_1, L_2)` has
this law:

* `z` is uniform nonzero;
* given `z`, the images of `L_1, L', L_2` in `F_2^N / <z>` are a uniform
  `(l-1)`-space, a uniform hyperplane of it, and a uniform `(l-1)`-space
  containing that hyperplane.

So given `z` this is the down-up walk `W_(l-1)` on `Gr(F_2^(N-1), l-1)`
started at stationarity, applied to the Boolean function
`f_z(L) = F[L](z)`. By (1) and Lemma 1 (with `l - 1 <= N - 1`),

```text
delta >= E_z Pr[f_z(L_1) != f_z(L_2)] >= kappa_l E_z min(a_z, 1 - a_z) = kappa_l delta_1,
```

because `min(a_z, 1 - a_z) = Pr_(L > z)[F[L](z) != g(z)]` for the plurality
`g(z)`. Hence `delta_1 <= delta / kappa_l`.

**(b) BLR.** Let `x, y` be uniform in `F_2^N`.

* If `x = 0`, `y = 0` or `x = y`, then `g(x) + g(y) = g(x+y)` holds trivially,
  since `g(0) = 0`.
* Otherwise `x, y` are independent. Let `L` be a uniform `l`-space containing
  `span(x, y)`, which exists since `l >= 2`. If `F[L]` agrees with `g` at
  `x`, `y` and `x + y`, then the equation holds by linearity of `F[L]`.
  Conditioned on independence, `L` is uniform and `(x, y)` is a uniform
  independent pair in `L`. So each of `(x, L)`, `(y, L)` and `(x + y, L)` is in
  the flag law.

Therefore

```text
eps := Pr_(x,y) [g(x) + g(y) != g(x + y)] <= 3 delta_1.
```

With `G = (-1)^g` one has `1 - 2 eps = sum_a G^(a)^3 <= max_a G^(a)`, by
Parseval. So some `a` has `Pr_x [g(x) != a.x] <= eps` over uniform `x`. Call
this linear functional `g^`. Over uniform nonzero `z`,

```text
mu := Pr_(z != 0) [g(z) != g^(z)] <= eps 2^N/(2^N - 1) <= 3 delta_1 (1 + 2^(1-N)).
```

**(c) Back to subspaces.** If `F[L] != g^|_L`, the two distinct linear
functionals on `L` disagree on `2^(l-1)` of the `2^l - 1` nonzero vectors of
`L`, which is at least half. At each such `z`, either `F[L](z) != g(z)` or
`g(z) != g^(z)`. Averaging over `(z, L)` in the flag law,

```text
Pr_L [F[L] != g^|_L] <= 2 (delta_1 + mu) <= delta_1 (8 + 12 * 2^(-N)) <= C_l delta.
```

A minimiser `g*` does at least as well as `g^`. []

The artifact exhausts 140 corrupted tables with `(N, l)` in
`{(4,2), (5,2), (5,3), (6,2), (6,3)}`. The worst ratio `dist/delta` it finds
is `2.28`, against the proved `C_l <= 19`, and the decoder of (a)-(c) attains
the same distance.

## Step 3: the per-tuple test

Fix a labelling `(A, B)` of value `1 - eta`. Fix `U`, and let `eta_U` be the
rejection probability of `G_multi` conditioned on `U`. The law of `U` under
`G_multi` is uniform (item 4 of the required node), so `E_U eta_U = eta`.
Call `L` *valid* if `L meet H_U = {0}`.

**Geometry of `U` and `V`.** By the notation of the required node,
`X_U = F_2^(3k)` has one coordinate per variable of `U`, so the `k` equations
of `U` have disjoint variable sets, and `dim H_U = k`. Suppose `V` keeps `j`
equations and replaces `k - j` equations by one of their variables. Then
`m := dim X_V = k + 2j`. Since the vectors `x_e` have disjoint supports,
`H_U meet X_V = span(x_e : e kept)`, of dimension `j`.

**Invalid mass.** Let `P_0` be the unconditioned DKKMS edge process (Q2).
Fix `U` and `V`, let `L'` be uniform in `Gr(X_V, l-1)`, and let `L > L'` be
uniform in `Gr(X_U, l)`. Put
`q_UV := Pr[L invalid]`. The inequality `(2^a - 1)/(2^b - 1) <= 2^(a-b)` for
`a <= b` gives two bounds.

* `Pr[L' meet H_U != 0] <= (2^j - 1)(2^(l-1) - 1)/(2^m - 1) <= 2^(l-1+j-m) <= 2^(l-1-k)`,
  by a union bound over the nonzero vectors of `H_U meet X_V`.
* If `L' meet H_U = 0`, then `L` is invalid iff the uniform point `L/L'` of
  `X_U / L'` lies in the `k`-dimensional image of `H_U`. This has probability
  `<= 2^(k - (3k - l + 1)) = 2^(l-1-2k)`.

So `q_UV <= 2^(l-1-k) + 2^(l-1-2k) <= 2^(l-k)`, uniformly in `(U, V)`. The
same bound holds for `q_0(U) := Pr_(P_0 | U)[L invalid]`. Also, a uniform
`l`-space of `X_U` is invalid with probability
`q_1 <= (2^l - 1)(2^k - 1)/(2^(3k) - 1) <= 2^(l-2k)`.

**The two tests on the table of `U`.** Define the linear table `F_U` on
`Gr(X_U, l)` by `F_U[L] := A(U, L)` for valid `L` and `F_U[L] := 0` otherwise.

* **`P` (two extensions of one B-vertex).** Draw `(V, L', L_1)` from `G_multi`
  conditioned on `U`. Draw `L_2` from the conditional law of `L` given
  `(U, V, L')` in `G_multi`, independently of `L_1`. Reject iff
  `F_U[L_1]|_(L') != F_U[L_2]|_(L')`.
* **`Q` (the ideal test).** The test `T` of Step 2 on `Gr(X_U, l)`, with
  `N = 3k`.

In `P` both `(V, L', L_1)` and `(V, L', L_2)` have the law of `G_multi` given
`U`, and both `L_i` are valid. A rejection forces
`A(U, L_i)|_(L') != B(V, L')` for some `i`, so `rej_P <= 2 eta_U`. This is
the 99 percent form of the two-extensions argument of DKKMS Claim 5.5.

**Distance between `P` and `Q`.** Both rejection events are the same function
of the triple `(L', L_1, L_2)`. Given `L'`, the conditional law of `L` in
`P_0` is uniform over `L > L'`, whatever `V` is. Put
`w(L') := Pr_(L > L')[L valid]`.

* **`P` versus `P_0`.** In `P`, `L'` has law `P_0(L') w(L') / Z` with
  `Z = 1 - q_0`, and `L_1, L_2` are independent uniform valid extensions. In
  `P_0`-with-two-extensions, `L'` has law `P_0(L')` and the extensions are
  independent and uniform. For `w` in `[0,1]` the first marginals differ by
  `(1/2) E_(P_0) |w/Z - 1| <= q_0 / Z`. Given `L'`, the pairs of extensions
  differ by at most `2 (1 - w(L'))`, whose `P`-expectation is
  `2 E_(P_0)[w (1 - w)] / Z <= 2 q_0 / Z`. So the distance is
  `<= 3 q_0/(1 - q_0)`. This is `<= 3 * 2^(l-k)`, because
  `q_0 <= 2^(l-k)(1/2 + 2^(-k))` and `2^(-k) + 2^(l-k) <= 1/2`.
* **`P_0` versus `Q`.** The two use the same kernel from `L'` to
  `(L_1, L_2)`. The law of `L'` in `P_0` given `U` is the law `L'` of
  Definition 4.8 at dimension `l - 1`, and in `Q` it is uniform. By (Q6)
  applied at `l - 1`, their distance is `<= beta sqrt(k) 2^(l+3)`.

Hence `SD(P, Q) <= SD*`, and

```text
delta_U := rej_Q(F_U) <= 2 eta_U + SD*.                                        (2)
```

**Consequences for `U`.** Let `lambda_U` be a minimiser of
`g -> Pr_(L uniform)[F_U[L] != g|_L]` over linear `g` on `X_U`. By Lemma 2
(`N = 3k >= 3`), `Pr_(L unif)[F_U[L] != lambda_U|_L] <= 20 delta_U`. Put

```text
omega_U := Pr_(L uniform valid) [A(U,L) != lambda_U|_L] <= 20 delta_U/(1 - q_1) <= 21 delta_U,
tau_U   := Pr_(G_multi | U)      [A(U,L) != lambda_U|_L] <= 20 delta_U + SD*.
```

For `tau_U`: the law of `L` under `G_multi | U` is within `q_0` of its law
under `P_0 | U`. That law is within `beta sqrt(k) 2^(l+3)` of uniform, since
the kernel from `L'` is the same. Also `A = F_U` on valid `L`.

## Step 4: folding forces the equations

**Claim.** If `omega_U < 3/8`, then `lambda_U|_(H_U) = h_U`, that is,
`lambda_U` satisfies every equation of `U`.

*Proof.* Let `L_1` be uniform valid and let `phi : L_1 -> H_U` be a uniform
linear map, independent of `L_1`. Put `L_2 := {z + phi(z) : z in L_1}`.

* **`L_2` is valid and in the same class.** If `z + phi z` lies in `H_U`, then
  `z` does, so `z = 0`. Also `L_2 + H_U = L_1 + H_U`.
* **`L_2` is uniform valid.** Given `M = L_1 + H_U`, the valid `l`-spaces
  with `L + H_U = M` are exactly the complements of `H_U` in `M`, and these are
  in bijection with the graphs of linear maps `L_1 -> H_U`. So given `M`, `L_2`
  is a uniform complement, just as `L_1` is.
* **Values.** By (Q4) and (Q5), both `A(U, L_1)` and `A(U, L_2)` are
  restrictions of the `(H_U, h_U)`-extension of `A(U, L_1)`. So
  `A(U, L_2)(z + phi z) = A(U, L_1)(z) + h_U(phi z)`.

Let `g = lambda_U` and suppose `g|_(H_U) != h_U`. If `A(U, L_i) = g|_(L_i)`
for both `i`, then `g(z + phi z) = g(z) + h_U(phi z)`, so
`(g - h_U)(phi z) = 0` for all `z` in `L_1`. Given `L_1`, the map
`(g - h_U) o phi` is a uniform linear functional on `L_1`, because
`g - h_U != 0` on `H_U`. So it vanishes with probability `2^(-l)`. Hence

```text
1 - 2 omega_U <= Pr[both agree] <= 2^(-l) <= 1/8,
```

which gives `omega_U >= 7/16 > 3/8`. []

By Markov, (2) and `E_U eta_U = eta`,

```text
Pr_U [lambda_U violates U] <= Pr_U [omega_U >= 3/8] <= (8/3) 21 (2 eta + SD*) = 112 eta + 56 SD*.   (3)
```

The artifact checks the claim on `F_2^6` with two equations and random
invariant tables. Every functional violating `h` is at least
`(1 - 2^(-l))/2`-far from the table, and in all 23 decisive trials the nearest
functional satisfies `h`.

## Step 5: gluing over `V`

Extend `B` by `0` to the `(l-1)`-spaces of `X_V` that are not B-vertices. For
each `V` let `lambda_V` be a minimiser of
`mu -> Pr_(L' unif in Gr(X_V, l-1)) [B(V,L') != mu|_(L')]` over linear `mu`
on `X_V`. Let `rho'` be the law of `(U, V)` under `G_multi`, and `rho` its
law in the outer game. For an edge `(U, V)` put

```text
theta_UV  := Pr_(G_multi | U,V)       [B(V,L') != lambda_U|_(L')],
theta'_UV := Pr_(L' unif in X_V)      [B(V,L') != lambda_U|_(L')].
```

* **Agreement.** If `theta'_UV < 1/4`, then `lambda_V = lambda_U|_(X_V)`.
  The minimiser has error `< 1/4` too, so `lambda_V` and `lambda_U|_(X_V)`
  agree on a uniform `L'` with probability `> 1/2`. Two distinct functionals
  on `X_V` agree on `L'` iff `L'` lies in the kernel of their difference, which
  has probability `<= 2^(-(l-1)) <= 1/4`.
* **From `theta` to `theta'`.** In `P_0` given `(U, V)`, `L'` is uniform in
  `Gr(X_V, l-1)`. `G_multi` reweights it by `w(L')/(1 - q_UV)`, and
  `SD(nu, nu w / Z) = E_nu (1 - w/Z)_+ <= E_nu (1 - w) = q_UV`. So
  `theta' <= theta + q_UV <= theta + SD*/3`.
* **Average of `theta`.** Under `rho'`,
  `E theta_UV <= Pr[B != A(U,L)|_(L')] + E_U tau_U <= eta + zeta_A`, where
  `zeta_A := E_U tau_U <= 20(2 eta + SD*) + SD* = 40 eta + 21 SD*`. So
  `E_(rho') theta <= 41 eta + 21 SD*`.
* **Reweighting.** `rho(U, V)` is proportional to `rho'(U, V)/(1 - q_UV)`,
  so `rho <= r rho'` with `r = 1/(1 - 2^(l-k)) <= 200/199`.

By Markov,

```text
Pr_(rho') [lambda_V != lambda_U|_(X_V)] <= 4 (41 eta + 21 SD* + SD*/3) <= 164 eta + 86 SD*,
Pr_(rho)  [lambda_V != lambda_U|_(X_V)] <= r (164 eta + 86 SD*) <= 165 eta + 87 SD*.       (4)
```

## Step 6: collecting the bounds

The outer labelling is `lambda = (lambda_U, lambda_V)` from Steps 3 and 5.

1. **Local honesty.** This is (3).
2. **Outer value.** An outer edge `(U, V)` is satisfied when `lambda_U`
   satisfies `U` and `lambda_U|_(X_V) = lambda_V`. The `U`-marginal of `rho` is
   uniform, so (3) and (4) give a loss of at most
   `277 eta + 143 SD* <= 300 (eta + SD*)`.
3. **A-side.** `Pr_edge [A(U,L) != lambda_U|_L] = E_U tau_U = zeta_A <= 40 eta + 21 SD*`.
   This is `<= 160 (eta + SD*)`.
4. **B-side.** If `A(U,L)|_(L') = B(V,L')`, `A(U,L) = lambda_U|_L` and
   `lambda_U|_(X_V) = lambda_V`, then `B(V,L') = lambda_V|_(L')`. So, with the
   first line of (4),
   `zeta_B <= eta + zeta_A + 164 eta + 86 SD* <= 205 eta + 107 SD* <= 210 (eta + SD*)`.

This proves Theorem R. The constants in items 2 to 4 of the target are weaker
than these, and so they hold.

**Corollary P.** Choose `kappa(C)` among the members `(U, L)` of `C` with
`A(U,L) = lambda_U|_L` when there is one.

* **The class label.** Unfolding `Fun(R_C) -> Fun(L)` is a bijection (Q4), and
  both `sigma_C` and `hon_kappa(lambda)_C` unfold at `kappa(C)` to
  `lambda_(U_C)|_(L_C)`. So they are equal.
* **Dirt.** Let an edge sit at a member `(U, L)` with `A(U,L) = lambda_U|_L`.
  Its class has such a member, so `hon_kappa(lambda)_C = sigma_C`, and its
  unfolding at `(U, L)` is `A(U, L) = lambda_U|_L`. So the edge is clean, and
  the dirt is `<= zeta_A <= 160 (eta + SD*)`.
* **Agreement.** On the same edges the A-labels of `(A, B)` and of
  `hon_kappa(lambda)` agree. The B-labels agree outside `zeta_B`. So the total
  disagreement is `<= zeta_A + zeta_B <= 245 eta + 128 SD* <= 370 (eta + SD*)`.

The patchwork of `high-advantage-selector-witnesses-decode-good-outer-labellings`
(a sibling lease node, not in this worktree) lets `kappa` be any choice of one
member per class, and leaves the right bits `b` free. So the choice above is
allowed there.

**Corollary N.** Put `eta, SD* <= 10^(-5)`, so `eta + SD* <= 2 * 10^(-5)`.
Then:

* the outer value loss is `<= 300 * 2 * 10^(-5) = 0.006`, so the outer value
  is `>= 0.994 >= 15/16`;
* the dirt is `<= 0.0032 <= 1/64`;
* the disagreement is `<= 0.0074 <= 1/128`.

`SD* <= 10^(-5)` holds when `beta sqrt(k) 2^(l+3) <= 5 * 10^(-6)` and
`3 * 2^(l-k) <= 5 * 10^(-6)`. Since `beta sqrt(k) = log log k / sqrt(k)`, the
first condition asks for `sqrt(k) / log log k >= 2^(l+4) 10^5`. This
holds for all `k >= k_0(l)` with `k_0(l) = O(4^l (log l)^2)`. Then
`2^(l-1) beta <= 1/8`, `2^(l-k) <= 1/200` and `3k >= l + 2` hold as well.
