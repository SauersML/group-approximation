---
rg: 2
id: p22-head-survival-forces-regular-weak-containment-proof
kind: route
title: Levi-stable ideals give head-faithfulness, the socle gives topological freeness, tensor powers fill the spectrum, and Archbold-Spielberg gives weak containment of the regular representation
target: p22-head-survival-forces-regular-weak-containment
requires: []
artifacts:
  - experiments/p22-regular-weak-containment-2026-09-17/check_p22_regular.py
---

Notation is as in the target. Everything is proved here. Only textbook
facts are cited: C*-crossed products, conditional expectations,
Pontryagin duality, and the lifting of projections from ultraproducts.
Char 2 is used freely, so `-1 = 1`. The artifact `check_p22_regular.py`
exits 0 and machine-checks:
* the ring identities of Steps 1-2;
* the rank growth of Step 3 on windows;
* the tensor spectral identity of Step 5;
* the compression identity of Step 6.

## Step 1. Levi-stable subgroups of `M_2(J)` are `M_2(I)`

**Lemma 1.** Let `K` be an additive subgroup of `N = M_2(J)` with
`A K B^{-1} = K` for all `(A,B)` in `L`. Then `K = M_2(I)` for a two-sided
ideal `I` of `J`.

*Proof.* For `b` in `J`, `x_12(b) = 1 + E_12 b` and `x_21(b) = 1 + E_21 b`
lie in `EL_2(J)`. Each is an involution in char 2. For `Y` in `K`:

```text
x_12(b) Y - Y = E_12 b Y  in K,        Y x_12(b)^{-1} - Y = Y E_12 b  in K,
x_21(b) Y - Y = E_21 b Y  in K,        Y x_21(b)^{-1} - Y = Y E_21 b  in K.
```

So `K` is closed under left and right multiplication by every `E_12 b` and
`E_21 c`. It is then closed under products of these, among them
`(E_12 b)(E_21 c) = E_11 bc` and `(E_21 b)(E_12 c) = E_22 bc`. Take `c = 1`.
Additively, the elements `E_12 b`, `E_21 b`, `E_11 b`, `E_22 b` span
`M_2(J)`. So `K` is closed under left and right multiplication by
`M_2(J)`, which makes it a two-sided ideal of `M_2(J)`. Every two-sided
ideal of a matrix ring `M_2(J)` has the form `M_2(I)` with `I` the ideal of
`(1,1)`-entries. The standard argument: `E_1r Y E_s1` moves any entry
`Y_rs` to the `(1,1)` place. `QED`

(The artifact checks all these identities on random samples, Part B.)

## Step 2. Every nonzero ideal of `J` contains `Q`

The monomials `S^i T^j` (`i, j >= 0`) form an `F_2`-basis of `J`, and
`T^j S^k = T^(j-k)` or `S^(k-j)`. So:
* `QS = S - S(TS) = 0`;
* `TQ = T - (TS)T = 0`;
* `Q^2 = Q`.

Put `e_ij = S^i Q T^j`. Then `e_ij e_kl = delta_jk e_il`, because
`Q T^j S^k Q` equals:
* `Q T^(j-k) Q = 0` when `j > k`;
* `Q S^(k-j) Q = 0` when `k > j`;
* `Q` when `j = k`.

**Lemma 2.** For every `a = sum a_{pq} S^p T^q` in `J` and `i, j >= 0`,

```text
Q T^i a S^j Q = lambda_ij(a) Q,   lambda_ij(a) = a_{ij} + sum_{k>=1} a_{i-k, j-k}.
```

If `a != 0`, pick a support point `(i,j)` of `a` whose `i` is minimal. Then
`lambda_ij(a) = 1`, so `Q = Q T^i a S^j Q` lies in `JaJ`.

*Proof.* Look at a single monomial `a = S^p T^q`.
* If `p > i`, then `T^i S^p = S^(p-i)` with `p - i >= 1`, and
  `Q S^(p-i) = 0`.
* If `p <= i`, then `T^i S^p T^q S^j = T^(i-p+q) S^j`. Between two `Q`s this
  survives only when `i - p + q = j`, because `Q T^m Q = Q S^m Q = 0` for
  `m >= 1`. It then equals `Q`.

So the sandwich of `S^p T^q` is `Q` exactly when
`(p,q) = (i-k, j-k)` for some `k >= 0`, and `0` otherwise. Summing over the
support gives the formula.

At a support point with minimal `i`, every point `(i-k, j-k)` with `k >= 1`
lies outside the support. `QED`

(The artifact checks the formula for all `i, j < 8` on 300 random `a`, and
checks the extraction, Part A.)

**Corollary 2.1 (faithful socle).** Let `(Q) = JQJ`, which is the span of the
`e_ij`. If `a (Q) = 0` or `(Q) a = 0`, then `a = 0`.

*Proof.* Suppose `a (Q) = 0` and `a != 0`. By Lemma 2, `Q` lies in `JaJ`.
Then `Q = Q Q` lies in `J a J Q`, and `J a J Q` is contained in
`J a (Q) = 0`, which is a contradiction. The case `(Q) a = 0` is symmetric.
`QED`

The same holds entrywise for `M_2(J)` acting on `M_2((Q))`.

## Step 3. The Levi acts faithfully and topologically freely on `N^`

Let `X = Hom(N, Z/2)`, the Pontryagin dual of the countable elementary
abelian 2-group `N`; it is a Cantor set. `L` acts on `N` by
`l.Y = A Y B^{-1}` and on `X` by `(l.chi)(Y) = chi(l^{-1}.Y)`.

**Fixed sets.** Put `D_l = (l-1)N = {l.Y - Y}`. Then `chi` is fixed by `l`
iff `chi` vanishes on `(l^{-1}-1)N = l^{-1}.D_l`. Replacing `l` by `l^{-1}`
(both are `!= 1` together), it suffices to study `Fix(l^{-1}) = D_l^perp`.
This is a closed subgroup of `X`, and by duality `X / D_l^perp` is the dual
of `D_l`. Hence `Fix(l)` is open
(equivalently, has nonempty interior; a subgroup with interior is open) iff
it has finite index iff `D_l` is finite.

**Lemma 3.** For every `l = (A,B) != 1` in `L`, `D_l` is infinite. In
particular `L` acts faithfully on `N`, and topologically freely on `X`.

*Proof.* Let `f = E_11 Q`. Put `W = M_2(J) f`, the "columns", and
`W' = f M_2(J)`, the "rows". Both are infinite-dimensional over `F_2`:
`W` contains the `E_11 S^i Q`. Multiplication `(w, phi) -> w phi` induces
an isomorphism of `M_2((Q))` onto the finitary operators `W (x) W'`. Indeed
`{E_r1 e_i0 : r, i}` and `{E_1s e_0j : s, j}` are bases of `W` and `W'`,
and their products `E_rs e_ij` form a basis of `M_2((Q))`. The subgroup
`M_2((Q))` of `N` is `L`-stable, and there `l.(w phi) = (Aw)(phi B^{-1})`.
* **Case 1: `A` is not the identity on `W`.** Over `F_2` the only nonzero
  scalar is 1, and `A` is invertible. So pick `w` with `Aw` not in
  `F_2 w`; then `w` and `Aw` are linearly independent. In `W (x) W'`, the
  element `Aw (x) phi B^{-1} - w (x) phi` vanishes only when both
  `phi B^{-1}` and `phi` vanish. So `phi -> l.(w phi) - w phi` is an
  injective map from the infinite `W'` into `D_l`.
* **Case 2: `A` is the identity on `W`.** Then `(A-1) W = 0`. Entrywise
  this says `(A-1)_{rc} J Q = 0`, hence `(A-1)_{rc} (Q) = 0`. By
  Corollary 2.1, `A = 1`. Since `l != 1`, `B != 1`. Symmetrically (use
  `(Q)(B^{-1}-1) != 0`), some `phi` has `phi B^{-1} != phi`. Then
  `w -> w (phi B^{-1} - phi)` is injective on the infinite `W` and lands
  in `D_l`.

So `D_l` is infinite and `Fix(l)` has empty interior. `QED`

(Part C of the artifact computes the `F_2`-rank of `Y -> AYB^{-1} - Y` on
the windows `M_2(J_{<=n})`, `n = 2, 4, 6, 8`, for random `l != 1` built
from root words. The rank is strictly increasing in every sample.)

**Corollary 3.1.** `C_P(N) = N`. An element `Y l` of `P` centralizes the
abelian group `N` iff `l` acts trivially on `N`, iff `l = 1`.

## Step 4. Head-faithfulness of `P_{2,2}(J)`

**Lemma 4.** Let `phi : P -> H` be a homomorphism with `phi(h) != 1`. Then
`phi` is injective. Consequently `Rad_MF(P)` is `1` or contains `h`, and
`h` not in `Rad_MF(P)` iff `P` is MF.

*Proof.* Let `K = ker phi`, a normal subgroup of `P`.
* `K cap N` is a normal subgroup of `P` inside `N`. So it is an additive
  subgroup of `M_2(J)`, stable under conjugation by `L`, i.e. under
  `Y -> A Y B^{-1}`.
* By Lemma 1, `K cap N = M_2(I)` for a two-sided ideal `I`. Since `h` is
  not in `K`, `E_11 Q` is not in `M_2(I)`, so `Q` is not in `I`. By Lemma 2,
  `I = 0`, so `K cap N = 1`.
* `K` and `N` are both normal, so `[K, N] <= K cap N = 1`. Then
  `K <= C_P(N) = N` by Corollary 3.1, so `K = K cap N = 1`.

For the consequence: if some MF model keeps `h`, it is injective, so
`Rad_MF(P) = 1`. Otherwise every MF model kills `h`, and `h` lies in
`Rad_MF(P)`. `QED`

This lemma is the `P_{2,2}` analogue of
`binary-jacobson-head-retaining-homomorphisms-are-faithful`. The mechanism
is different: `N` is abelian and far from simple, and the ideal lattice of
`J`, through Lemma 2, does the work that simplicity of the finitary kernel
does there. The w11 lemma `gamma-trap-degree-one-layer-is-a-matrix-ring-module`
proves the matching statement for Levi-stable quotients of the trap
group's degree-one layer.

## Step 5. Tensor upgrade: a head-keeping MF model with full spectrum

**Conventions.** Write an MF model of a countable group `G` as a sequence
`sigma_k : G -> U(d_k)` with
`delta_k(g,g') = ||sigma_k(gg') - sigma_k(g) sigma_k(g')|| -> 0` for every
pair. It induces a homomorphism into the unitaries of the corona
`C = prod M_{d_k} / (+) M_{d_k}`, and a representation of `C*(G)` there.

Fix a free ultrafilter `omega` and let `A_omega = prod_omega M_{d_k}` be the
norm ultraproduct. `A_omega` is a quotient of `C`. So the kernel in `C*(G)`
of the corona representation lies inside the kernel of the
`A_omega`-representation.

If `sigma(h) != 1` in `C`, then `||sigma_k(h) - 1|| >= c > 0` along an
infinite set of `k`. Choose `omega` on that set; then `sigma(h) != 1` in
`A_omega`.

**Spectrum.** For a unitary representation `sigma` of `N` in a C*-algebra,
`C*(N) = C(X)` maps onto `C*(sigma(N))`. Its kernel is `C_0(X \ Omega)`
for a closed set `Omega = Omega_sigma`, the spectrum. For a finite subgroup
`F <= N` and a character `psi` of `F`, put

```text
E_psi(sigma) = |F|^{-1} sum_{Y in F} psi(Y) sigma(Y),
```

a projection. The restriction of `Omega` to `F` is
`Omega_F = {psi : E_psi(sigma) != 0}`. A closed subset of the profinite `X`
is the inverse limit of its restrictions to the finite subgroups `F`.

**Lemma 5.** Let `sigma_k` be an MF model of `P` with `sigma(h) != 1` in
`A_omega`, where `omega` is chosen as above. Enumerate `P` and choose
`J_k -> infinity` so slowly that `J_k delta_k(g,g') -> 0` for every pair;
this is possible by a diagonal choice. Put

```text
tau_k = (+)_{j=1..J_k} sigma_k^{(x) j}.
```

Then `tau_k` is an MF model of `P`. Moreover `Omega_{tau|N} = X` in
`A'_omega`, the ultraproduct over the same `omega` of the dimensions of
`tau_k`.

*Proof.* **Defect.** For a fixed pair, `sigma^{(x) j}` has defect at most
`j delta_k`, by telescoping unitaries. The direct sum has defect at most
`J_k delta_k -> 0`, so `tau_k` is an MF model.

**Genuine finite pieces.** Fix a finite `F <= N`. In `A_omega` the
`E_psi(sigma)`, `psi in F^`, are orthogonal projections summing to 1.
Lift them to orthogonal projections `P_{psi,k}` in `M_{d_k}` summing to 1
(projections lift from ultraproducts, and a finite orthogonal family lifts
by successive functional calculus). Put
`rho_k(Y) = sum_psi psi(Y) P_{psi,k}`. This is a genuine representation of
`F` with `eps_k = max_{Y in F} ||rho_k(Y) - sigma_k(Y)||` tending to 0 along
`omega`.

For fixed `j`, `sigma_k^{(x) j}|_F` is within `j eps_k` of
`rho_k^{(x) j}`, pointwise on `F`. For genuine representations of the
abelian group `F`,

```text
E_chi(rho^{(x) j}) = sum_{psi_1 ... psi_j = chi} P_{psi_1} (x) ... (x) P_{psi_j}
                 >= P_{chi_1} (x) ... (x) P_{chi_j}
```

for any factorization `chi = chi_1 ... chi_j`. (Part D of the artifact
checks this identity and the product-set spectrum.)

**Product set.** Take `chi_1, ..., chi_j` in `Omega_F(sigma)` and put
`chi = chi_1 ... chi_j`. For `omega`-almost every `k`:
* each `P_{chi_i,k} != 0`, so `E_chi(rho_k^{(x) j})` is a nonzero
  projection of norm 1;
* the `j`-th block of `tau_k` exists, since `J_k -> infinity`.

On that block, `E_chi(tau_k)` equals `E_chi(sigma_k^{(x) j})`, which is
within `j eps_k` of that projection. So `||E_chi(tau)|| = 1` in `A'_omega`.
Hence `Omega_F(tau)` contains `Omega_F(sigma)^j` for every `j`, and so

```text
Omega_tau  contains  H := closure( union_j Omega_sigma^j ).
```

**Fullness.** `X` has exponent 2 and `Omega_sigma` is nonempty, so `H` is
the closed subgroup generated by `Omega_sigma`. It is `L`-invariant,
because `sigma(l)` conjugates `sigma(N)` by the action. Its annihilator in
`N` is

```text
{Y : chi(Y) = 1 for all chi in Omega_sigma} = ker(sigma|_N)  (in A_omega).
```

The homomorphism `P -> U(A_omega)` keeps `h`, so it is injective by
Lemma 4. So the annihilator is 0, and `H = X` by duality. Therefore
`Omega_tau = X`, and `C(X) -> C*(tau(N))` is injective. `QED`

Remark: the same `tau` is formed for an MF model of any group containing `P`
(for instance `EL_5(J)`), and restriction to `P` commutes with the
construction. This is what the corollary for (HC) uses.

## Step 6. Archbold-Spielberg for `C*(P) = C(X) x| L`

**Identifications (textbook).** For a semidirect product `N x| L` with `N`
abelian:
* `C*(N x| L) = C*(N) x| L = C(X) x| L`, the full crossed product;
* `C*_r(N x| L) = C(X) x|_r L`, the reduced one.

The left regular representation `lambda_P` is the map
`C*(P) -> C(X) x|_r L`; see e.g. Williams, *Crossed products of
C*-algebras*, Prop. 3.11, and Brown-Ozawa, Ch. 4. Let
`E : C(X) x| L -> C(X)` be the canonical conditional expectation, with
`E(f u_g) = delta_{g,e} f`. It factors as `E = E_r o lambda_P`, where `E_r`
is the expectation on the reduced crossed product. `E_r` is faithful
(Brown-Ozawa, Prop. 4.1.9).

**Lemma 6.** Let the discrete group `L` act topologically freely on the
compact space `X`. Let `pi` be a representation of `C(X) x| L` that is
injective on `C(X)`. Then `||E(a)|| <= ||pi(a)||` for all `a`, and
`ker pi` is contained in `ker lambda_P`.

*Proof.* Let `a = sum_{g in F} f_g u_g` be a finite sum and `eps > 0`.
1. The set `U = {x : |f_e(x)| > ||f_e|| - eps}` is open and nonempty.
2. Each `Fix(g)`, `g in F \ {e}`, is closed with empty interior, and so is
   their finite union. Pick `x_0` in `U` outside that union.
3. `X` is Hausdorff and `g x_0 != x_0` for the finitely many `g`. So there
   is an open `V` with `x_0 in V`, `V` contained in `U`, and `gV` disjoint
   from `V` for all `g in F \ {e}`.
4. Pick `k` in `C(X)` with `0 <= k <= 1`, `k(x_0) = 1` and support in `V`.
   Then `k f_g u_g k = f_g k (g.k) u_g`, and `g.k` is supported in `gV`, so
   this term is 0 for `g != e`. Hence `k a k = k^2 f_e`.
5. `pi` is an injective *-homomorphism on `C(X)`, hence isometric there.
   So

```text
||pi(a)|| >= ||pi(k a k)|| = ||k^2 f_e|| >= |f_e(x_0)| > ||f_e|| - eps.
```

Both sides of `||E(a)|| <= ||pi(a)||` are continuous in `a`, so the
inequality extends from the dense algebraic crossed product to all of
`C(X) x| L`.

Now let `pi(a) = 0`. Then `pi(a* a) = 0`, so
`E_r(lambda_P(a)* lambda_P(a)) = E(a* a) = 0`. Faithfulness of `E_r` gives
`lambda_P(a) = 0`. `QED`

(Part E of the artifact checks the compression `k f u_g k = 0` for disjoint
supports in a finite model.)

## Step 7. Proof of the theorem

* **(b) => (a).** If `Rad_MF(P) = 1`, it does not contain `h != 1`.
* **(a) => (b).** This is Lemma 4.
* **(c) => (a).** `lambda_P(1-h) != 0` because `h != 1`. If `ker pi` lies
  inside `ker lambda_P`, then `pi(1-h) != 0`, so `pi` keeps `h`.
* **(a) => (c).** Let `sigma` keep `h`, and choose `omega` as in Step 5.
  - The model `tau` of Lemma 5 gives, in `A'_omega`, a representation of
    `C*(P) = C(X) x| L` that is injective on `C(X)`.
  - By Lemma 3 the action is topologically free. So Lemma 6 says the
    `A'_omega`-representation has kernel inside `ker lambda_P`.
  - The corona representation of `tau` has an even smaller kernel, because
    `A'_omega` is a quotient of the corona. So `tau` is an MF model weakly
    containing `lambda_P`.

**Dichotomy.** If some MF model keeps `h`, the `tau` above is an MF model,
so `I_MF` lies in `ker tau`, which lies in `ker lambda_P`. Otherwise every
MF model kills `h`, and `1-h` lies in `I_MF`.

**Corollary for (HC).** `P` is the block parabolic inside the upper-left
`EL_4(J) <= EL_5(J)`, and `h = x_13(Q) = w`.
* If an MF model `rho` of `EL_5(J)` has `rho|_P` weakly containing
  `lambda_P`, then `rho(w) != 1`, by (c) => (a) applied to `rho|_P`. So
  (HC) fails.
* Conversely, suppose (HC) fails, so some `rho` has `rho(w) != 1`. The
  tensor upgrade `tau` of `rho`, as an `EL_5(J)`-model, is an MF model of
  `EL_5(J)`. Its restriction `tau|_P` is the tensor upgrade of `rho|_P`,
  which keeps `h`. By Step 7, (a) => (c), `tau|_P` weakly contains
  `lambda_P`.

The local statement `h in Rad_MF(P)` implies (HC), because MF models of
`EL_5(J)` restrict to MF models of `P`. By Lemma 4 the local statement is
equivalent to "`P_{2,2}(J)` is not MF".

## Step 8. The class kill, and what is left

**Invariant.** The spectrum `Omega_sigma`, a closed subset of `X`, of the
radical in an MF model `sigma`. It is closed and `L`-invariant, and it
generates `X` as a closed group whenever `sigma` keeps `h` (Step 5).

**Where the class dies.** The tensor upgrade replaces `sigma` by `tau`
with `Omega_tau = X`, keeping MF-ness and head survival. So the following
kinds of `P_{2,2}`-local obstruction to head survival cannot exist:
1. **Support obstructions.** These have the form "head survives implies
   `Omega` avoids a nonempty open set", or "`Omega` lies in a proper
   Levi-invariant closed subset".
2. **Window-support obstructions.** Examples: "for some finite `F`, some
   character of `F` has zero eigenspace", or any rank-profile condition that
   the full spectrum violates.
   The w11 break (`p22` RF-action certificates, recorded DEAD) found that the
   Haar rank profile gives no restriction; this explains why. WLOG the
   model is spectrally full and weakly contains `lambda_P`, so every window
   eigenspace is present.
3. **C*-relational obstructions.** These use only relations of `C*(P)`
   together with `h != 1`, and derive a proper isometry, a nonzero Fredholm
   index, or an infinite projection. They would apply to `lambda_P`, which
   keeps `h`. But `C*_r(P)` carries the faithful trace `<. delta_e,
   delta_e>`, so it is stably finite and has none of these.

   Such arguments must therefore use the finite-dimensional provenance
   essentially. The w11 Fredholm-index kill of root-preserving seams does:
   it applies to partial models, not to `C*(P)`.

**What is left.** By the theorem, a (T)-free proof of the local statement
is exactly a proof that `lambda_{P_{2,2}(J)}` is weakly contained in no MF
representation. This is the MF/quasidiagonality question for the regular
representation of one explicit group.

If `C*_r(P_{2,2}(J))` is an MF algebra, then `P` is MF: the unitaries
`lambda(g)` embed `P` into a corona. Then the local route to (HC) is dead,
and (HC) must use root subgroups outside `P_{2,2}(J)`. This is not decided
here.
