# Six uses of the restriction test on one GL-equivariant gadget make every seed prediction function an approximate homomorphism, BLR turns each into a linear functional, and the one-half spectral gap of the Grassmann graph glues all of them into a single global functional

*Attempt artifact (2026-09-18, wave `swarm-0917`, lane `e2-w2-ugc-selector-kill`),
written as route `grassmann-restriction-99-percent-rigidity-proof` into
`grassmann-restriction-test-is-99-percent-rigid` with `requires: []`, artifact
`experiments/grassmann-99-rigidity-2026-09-18/check_grassmann_99_rigidity.py`.
It is recorded here as an attempt, not as a compiled route, because the wave's
three-lens referee stage returned a refutation (lens 2) against this lane's
results; the lane therefore lands demoted as a whole. **No referee found an
error in Theorem R itself.** All three lenses walked this proof step by step
and reported that it holds; lens 2, which refuted the companion node, wrote
"What holds: Theorem R itself survives the check." The two arithmetic
shortcuts the referees did flag — the unstated derivation of `s <= 1.3e-4` in
Lemma 4.2 and the `1/(1-lam) <= 2.001` factor it forces — are filled in below,
and the final budget is stated as `784.4 eta` rather than `784 eta`. Promote
this back to a `kind: route` node with
`target: grassmann-restriction-test-is-99-percent-rigid` and `requires: []`
once a clean referee pass survives.*

Notation is that of the target claim: `X = F_2^D`, `2 <= l <= D-2`, labels
`sigma_L in L^*` for `L in Gr(X,l)` and `tau_Q in Q^*` for `Q in Gr(X,l-1)`, a
*flag* is a pair `Q < L` with `dim Q = l-1`, `dim L = l`, the flag distribution
`Flag` is uniform on flags, and

```text
eps := Pr_(Q<L ~ Flag) [ sigma_L|_Q != tau_Q ]  <=  eta,     eta <= 1/2000,
theta := 2^(l-D)  <=  eta.
```

Throughout, `GL := GL(X)` acts on everything by change of basis, and we use
repeatedly:

> **(Sym)** `GL` is transitive on flags. Hence the only `GL`-invariant
> probability distribution on flags is `Flag`. Consequently, if a random
> configuration is sampled `GL`-equivariantly and `Psi` is a `GL`-equivariant
> map from configurations to flags defined on a `GL`-invariant event `E` of
> positive probability, then the law of `Psi` conditioned on `E` is exactly
> `Flag`, so `Pr[ Psi is a rejecting flag | E ] = eps`.

Transitivity on flags is the standard fact that `GL(X)` is transitive on
ordered bases, hence on nested pairs of subspaces of fixed dimensions.

Also record the two sampling identities used below, both instances of (Sym):

* the law of `(L, Q)` with `L` uniform in `Gr(X,l)` and `Q` a uniform hyperplane
  of `L` is `Flag`;
* for `Q` uniform in `Gr(X,l-1)` and `x` uniform in `X \ Q`, the pair
  `(L, x) = (Q + <x>, x)` has `L` uniform in `Gr(X,l)` and, given `L`, `x`
  uniform in `L \ {0}`. (Given `L`, each `x in L\{0}` lies outside exactly
  `2^(l-1)` of the `2^l - 1` hyperplanes of `L`, the same number for every `x`.)

## Step 0. Prediction functions

For `Q in Gr(X,l-1)` define

```text
F_Q(x) := sigma_(Q + <x>)(x)   for x in X \ Q,      F_Q(w) := tau_Q(w)  for w in Q.
```

`F_Q : X -> F_2` is a total function. Note `F_Q(0) = 0`.

## Step 1. The gadget and the additive defect

**Sampling `S`.** Draw `Q` uniform in `Gr(X,l-1)`, then `P` a uniform hyperplane
of `Q` (so `dim P = l-2 >= 0`), then `x, y` uniform and independent in `X`. Let

```text
G := { x notin Q,  y notin Q,  x+y notin Q }.
```

`Pr[not G] <= 3 * 2^(l-1)/2^D = 1.5 theta`.

**Lemma 1.1.** On `G`, `dim(P + <x,y>) = l`.

*Proof.* `x notin Q` and `P < Q`, so `x notin P` and `dim(P + <x>) = l-1`.
Suppose `y in P + <x>`. Since `y notin Q` and `P < Q`, we must have `y = p + x`
with `p in P`, and then `x + y = p in P < Q`, contradicting `x+y notin Q`. So
`y notin P + <x>` and `dim(P + <x,y>) = l`. QED

On `G` put, for `u in {x, y, x+y}`,

```text
N   := P + <x,y>   in Gr(X,l),
Q_u := P + <u>     in Gr(X,l-1),
L_u := Q + <u>     in Gr(X,l).
```

These are the right dimensions: `dim Q_u = l-1` because `u notin Q >= P`, and
`dim L_u = l` for the same reason. Containments: `Q_u < N` because
`P < N` and `u in N` (for `u = x+y` too), and `Q_u < L_u` because `P < Q` and
`u in L_u`. So

```text
(N, Q_x), (N, Q_y), (N, Q_(x+y)),  (L_x, Q_x), (L_y, Q_y), (L_(x+y), Q_(x+y))
```

are six flags.

**Lemma 1.2.** Conditioned on `G`, each of the six is distributed exactly as
`Flag`.

*Proof.* `S` is `GL`-equivariant, `G` is `GL`-invariant, and each of the six maps
`(Q,P,x,y) -> flag` is `GL`-equivariant. Apply (Sym). (The three maps involving
`x+y` are also covered directly: `(x,y) -> (x+y,y)` is a measure-preserving
involution of `X^2` that preserves `G` and carries the pair
`((N,Q_x),(L_x,Q_x))` to `((N,Q_(x+y)),(L_(x+y),Q_(x+y)))`, since
`P + <x+y, y> = P + <x,y> = N`.) QED

The artifact verifies Lemma 1.2 by exhaustive enumeration: for `(D,l)` up to
`(5,3)` each of the six maps hits every flag exactly the same number of times.

**Lemma 1.3 (additivity).** If all six flags are accepted, then
`F_Q(x+y) = F_Q(x) + F_Q(y)`.

*Proof.* Fix `u in {x,y,x+y}`. Acceptance of `(N, Q_u)` gives
`sigma_N|_(Q_u) = tau_(Q_u)`; acceptance of `(L_u, Q_u)` gives
`sigma_(L_u)|_(Q_u) = tau_(Q_u)`. Evaluate both at `u in Q_u`:
`sigma_N(u) = sigma_(L_u)(u)`. On `G` we have `L_u = Q + <u>`, so
`sigma_(L_u)(u) = F_Q(u)`. Hence `sigma_N(u) = F_Q(u)` for all three `u`.
`sigma_N` is a linear functional on `N` and `x, y, x+y in N`, so
`sigma_N(x+y) = sigma_N(x) + sigma_N(y)`. QED

**Proposition 1.4.** Put `rho_Q := Pr_(x,y in X)[F_Q(x+y) != F_Q(x)+F_Q(y)]` and
`rho := E_Q rho_Q` with `Q` uniform. Then

```text
rho  <=  6 eps + 1.5 theta  <=  7.5 eta.
```

*Proof.* Under `S` the marginal of `Q` is uniform and `(x,y)` is uniform on
`X^2`, so `rho = Pr_S[F_Q(x+y) != F_Q(x)+F_Q(y)]`. Split on `G`. On `G`,
Lemma 1.3 and Lemma 1.2 with a union bound give failure probability at most
`6 eps`. Off `G` bound by `Pr[not G] <= 1.5 theta`. QED

## Step 2. BLR at each seed

**Lemma 2.1 (BLR, self-contained).** Let `F : X -> F_2` with
`rho_F := Pr_(x,y)[F(x+y) != F(x)+F(y)] < 1/8`. Define
`A(x) := maj_y [F(x+y) + F(y)]`. Then `A` is linear and
`Pr_x[F(x) != A(x)] <= 2 rho_F`.

*Proof.* (i) For fixed `x` and independent uniform `y, z`,
`Pr[F(x+y)+F(z) != F(x+y+z)] <= rho_F` because `x+y` and `z` are independent
uniform, and `Pr[F(y)+F(x+z) != F(x+y+z)] <= rho_F` because `y` and `x+z` are
independent uniform. Adding, `Pr[F(x+y)+F(y) != F(x+z)+F(z)] <= 2 rho_F`. If `p`
is the probability that `F(x+y)+F(y)` equals its majority value, this says
`2p(1-p) <= 2 rho_F`, and `p >= 1/2` gives `1-p <= 2 rho_F`. So for every `x`,

```text
Pr_y[ F(x+y)+F(y) = A(x) ]  >=  1 - 2 rho_F.       (*)
```

(ii) Linearity. Fix `a,b` and draw `y,z` independent uniform. By (*) applied at
`a`, `b`, `a+b` (with the uniform elements `y`, `z`, `y+z`),
`A(a) = F(a+y)+F(y)`, `A(b) = F(b+z)+F(z)` and
`A(a+b) = F(a+b+y+z)+F(y+z)` each hold with probability `>= 1-2 rho_F`. Also
`F(a+y)+F(b+z) = F(a+b+y+z)` with probability `>= 1-rho_F` (independent uniform
arguments) and `F(y)+F(z) = F(y+z)` with probability `>= 1-rho_F`. The union of
the five failures has probability `<= 8 rho_F < 1`, so some `(y,z)` makes all
five hold, and then `A(a)+A(b) = A(a+b)`. Since also `A(0)=0`, `A` is linear.

(iii) Distance. `Pr_(x,y)[F(x) != F(x+y)+F(y)] = rho_F`. For any `x` with
`F(x) != A(x)`, (*) gives `Pr_y[F(x) != F(x+y)+F(y)] >= 1-2 rho_F`. Hence
`rho_F >= Pr_x[F != A] (1-2 rho_F)`, so
`Pr_x[F != A] <= rho_F/(1-2 rho_F) <= 2 rho_F`. QED

Call `Q` **good** if `rho_Q < 1/8`, and then let `A_Q in X^*` be the linear
function of Lemma 2.1, so `Pr_x[F_Q(x) != A_Q(x)] <= 2 rho_Q`. By Markov and
Proposition 1.4,

```text
Pr_Q[ Q bad ]  <=  8 rho  <=  60 eta.          (2.2)
```

## Step 3. Neighbouring seeds predict the same bit

**Sampling `W'`.** `Q` uniform in `Gr(X,l-1)`, `P` a uniform hyperplane of `Q`,
`Q~` uniform in `{ Q' in Gr(X,l-1) : Q' > P }`, and `x` uniform in `X`. Let
`G' := { x notin Q, x notin Q~ }`, so `Pr[not G'] <= 2 theta`. Write `W` for the
induced Markov chain `Q -> Q~` on `Gr(X,l-1)` (the **down-up walk**).

**Lemma 3.1.** `Pr_(W')[ F_Q(x) != F_(Q~)(x) ]  <=  2 eps + 2 theta`.

*Proof.* Work on `G'`. If `Q~ = Q` there is nothing to prove. Otherwise
`R := P + <x>` has dimension `l-1`, and `R < Q + <x> =: L` and
`R < Q~ + <x> =: L~`, both of dimension `l`. So `(L,R)` and `(L~,R)` are flags,
each obtained from `(Q,P,Q~,x)` by a `GL`-equivariant map on the `GL`-invariant
event `G'`, hence each is exactly `Flag`-distributed by (Sym). If both are
accepted then `sigma_L(x) = tau_R(x) = sigma_(L~)(x)`, that is
`F_Q(x) = F_(Q~)(x)`. QED

**Lemma 3.2 (the walk mixes).** `W` is reversible with uniform stationary
distribution, and every eigenvalue other than `1` has modulus at most
`1/2 + s`, where `s := 1/(2^(D-l+2) - 1)` is the holding probability.

*Proof.* Write `k := l-1`, `n := D`, so `1 <= k <= n-2`. From `Q`, the walk picks
`P < Q` of codimension 1 (there are `2^k - 1` choices, all equally likely) and
then `Q~ > P` uniformly among the `k`-spaces containing `P`, of which there are
`2^(n-k+1) - 1` (one for each line of `X/P`). One of them is `Q`; the others
each satisfy
`dim(Q cap Q~) = k-1`, and each such `Q~` arises from exactly one `P`, namely
`Q cap Q~`. Hence

```text
W = (1-s) * J  +  s * I,     s = 1/(2^(n-k+1) - 1),
```

where `J` is the simple random walk on the Grassmann graph `J_2(n,k)` (vertices
`Gr(X,k)`, adjacency `dim(Q cap Q~) = k-1`). `J_2(n,k)` is a distance-regular
graph whose eigenvalues are (Delsarte; Brouwer--Cohen--Neumaier, *Distance-Regular
Graphs*, Thm. 9.3.3)

```text
lambda_j = 2^(j+1) [k-j]_2 [n-k-j]_2 - [j]_2 ,   j = 0,...,k,   [m]_2 := 2^m - 1.
```

Expanding, for `0 <= j <= k`,

```text
lambda_j = 2^(n-j+1) + 2^j + 1 - 2^(k+1) - 2^(n-k+1),
```

and in particular the degree is `lambda_0 = 2^(n+1) + 2 - 2^(k+1) - 2^(n-k+1)`.
Two inequalities, both for `1 <= j <= k <= n-2`:

* `lambda_0 - 2 lambda_j = (2^(n+1) - 2^(n-j+2)) - 2^(j+1) + 2^(k+1) + 2^(n-k+1)`.
  For `j = 1` this is `2^(k+1) + 2^(n-k+1) - 4 >= 0`. For `j >= 2` we have
  `2^(n+1) - 2^(n-j+2) >= 2^n` and `2^(j+1) <= 2^(k+1) <= 2^(n-1)`, so it is
  `>= 2^n - 2^(n-1) > 0`.
* `lambda_0 + 2 lambda_j = 2^(n+1) + 2^(n-j+2) + 2^(j+1) + 4 - 3*2^(k+1) - 3*2^(n-k+1)`.
  Using `j <= k` (so `2^(n-j+2) >= 2^(n-k+2)`), `2^(j+1) >= 4`, and
  `k <= n-2` (so `2^(k+1) <= 2^(n-1)` and `2^(n-k+1) <= 2^(n-1)`), this is
  `>= 2^(n+1) + 2^(n-k+2) + 8 - 3*2^(k+1) - 3*2^(n-k+1)`
  `= 2^(n+1) - 3*2^(k+1) - 2^(n-k+1) + 8 >= 2^(n+1) - 3*2^(n-1) - 2^(n-1) + 8 = 8 > 0`.

So `|lambda_j| <= lambda_0 / 2` for every `j >= 1`, i.e. `J` has all non-trivial
eigenvalues of modulus `<= 1/2`, and `W = (1-s)J + sI` has them of modulus
`<= (1-s)/2 + s <= 1/2 + s`. QED

The artifact diagonalises `W` exactly for seven parameter points and matches the
closed formula to `1e-8`; the largest non-trivial modulus observed is `0.400`.

## Step 4. One global functional

Partition `Gr(X,l-1)` into the classes `C_A := { Q good : A_Q = A }` for
`A in X^*`, together with `C_bad := { Q bad }`.

**Lemma 4.1.** `Pr_W[ Q and Q~ lie in different classes ] <= alpha`, where

```text
beta  := 4 rho + 2 eps + 2 theta   <=  34 eta,
alpha := 2 beta + 16 rho           <=  188 eta.
```

*Proof.* Under `W` both endpoints are uniform (the chain is reversible with
uniform stationary law). On the event that both are good,

```text
Pr_x[A_Q(x) != A_(Q~)(x)] <= Pr_x[A_Q != F_Q] + Pr_x[F_Q != F_(Q~)] + Pr_x[F_(Q~) != A_(Q~)],
```

so taking expectations over `W` and using Lemma 2.1, Lemma 3.1 and
Proposition 1.4,

```text
E_W[ 1{both good} * Pr_x[A_Q(x) != A_(Q~)(x)] ]  <=  2 rho + 2 rho + 2 eps + 2 theta = beta.
```

Two distinct elements of `X^*` disagree on exactly half of `X`, so the indicator
of `A_Q != A_(Q~)` contributes exactly `1/2` whenever it is `1`. Hence
`Pr_W[both good, A_Q != A_(Q~)] <= 2 beta`. Adding `2 Pr[Q bad] <= 16 rho` from
(2.2) for the event that an endpoint is bad gives `alpha`. QED

**Lemma 4.2.** Some class has measure `>= 1 - 2 alpha`, and it is a `C_A`.

*Proof.* Let `mu_i` be the measures of the classes. For a reversible chain with
uniform stationary distribution and non-trivial eigenvalues of modulus `<= lam`,
the expander mixing lemma gives `Pr_W[both ends in class i] <= mu_i^2 + lam mu_i(1-mu_i)`.
Summing over classes and using Lemma 4.1,

```text
1 - alpha <= sum_i (mu_i^2 + lam mu_i (1-mu_i))  =  1 - (1-lam) sum_i mu_i(1-mu_i),
```

so `(1-lam) sum_i mu_i(1-mu_i) <= alpha`.

*The bound on `s`, stated explicitly (referee audit 2026-09-18).* Lemma 3.2
gives `lam <= 1/2 + s` with `s = 1/(2^(D-l+2) - 1)` for the walk on
`Gr(X, l-1)`. This is **not** controlled by `l <= D-2` alone: at `l = D-2` one
gets `s = 1/15` and `1/2 + s = 0.567`. It is controlled by the *other*
hypothesis of Theorem R. From `2^(l-D) <= eta <= 1/2000` we get
`2^(D-l) >= 2000`, hence `D - l >= 11`, hence

```text
s  =  1/(2^(D-l+2) - 1)  <=  1/(2^13 - 1)  =  1/8191  <  1.3e-4,
lam  <=  1/2 + s  <  0.5002,        1/(1 - lam)  <  2.001.
```

With `sum_i mu_i(1-mu_i) = 1 - sum_i mu_i^2 >= 1 - mu_max` we get
`mu_max >= 1 - alpha/(1-lam) >= 1 - 2.001 alpha >= 1 - 376.2 eta > 0.81`. Since
`Pr[C_bad] <= 60 eta < 0.81` by (2.2), the maximal class is some `C_A`. QED

Fix that `A`. So `Pr_Q[ Q good and A_Q = A ] >= 1 - 2.001 alpha`.

**Lemma 4.3.** `E_Q Pr_x[ F_Q(x) != A(x) ] <= 2.001 alpha + 2 rho <= 392 eta`.

*Proof.* Split on whether `Q` is in the maximal class. If it is,
`Pr_x[F_Q != A] = Pr_x[F_Q != A_Q] <= 2 rho_Q` by Lemma 2.1; average and use
Proposition 1.4. Otherwise bound by `1`, with probability `<= 2.001 alpha`. QED

## Step 5. From prediction functions back to `sigma` and `tau`

By the second sampling identity, drawing `Q` uniform and `x` uniform in `X` and
conditioning on `x notin Q` produces `L := Q + <x>` uniform in `Gr(X,l)` with
`x` uniform in `L \ {0}`, and then `F_Q(x) = sigma_L(x)`. Since
`Pr[x in Q] <= theta`,

```text
Pr_(L uniform, x uniform in L\{0}) [ sigma_L(x) != A(x) ]  <=  2.001 alpha + 2 rho + theta.
```

For a fixed `L`, `sigma_L` and `A|_L` are both in `L^*`; if they differ they
differ on exactly `2^(l-1)` of the `2^l` points of `L`, hence on
`2^(l-1)/(2^l - 1) > 1/2` of `L \ {0}`. Therefore

```text
Pr_L[ sigma_L != A|_L ]  <=  2 (2.001 alpha + 2 rho + theta)  <=  2*376.2 eta + 4*7.5 eta + 2 eta = 784.4 eta,
```

which is Theorem R's first inequality with room to spare (`<= 800 eta`). For the
second, a flag is accepted with probability `1 - eps`, and on an accepted flag
`tau_Q = sigma_L|_Q`, so

```text
Pr_(Q<L ~ Flag)[ tau_Q != A|_Q ]  <=  eps + Pr_L[sigma_L != A|_L]  <=  eta + 784.4 eta;
```

the marginal of `Q` under `Flag` is uniform, giving `<= 801 eta`.

Corollary R1 is Proposition 1.4 together with Lemma 4.3 (`392 <= 400`).

**Where the hypotheses are used.** `eta <= 1/2000` makes `rho <= 7.5 eta < 1/8`
(so Markov in (2.2) has content), `2.001 alpha <= 0.189 < 1/2` (so the maximal
class in Lemma 4.2 is unique and is a `C_A`), and `8 rho_F < 1` inside Lemma
2.1. `2^(l-D) <= eta` makes the four `theta` terms harmless **and** forces
`D - l >= 11`, which is what bounds `s` and hence `lam` in Lemma 4.2; the
weaker `l <= D-2` does not suffice there. `l >= 2` is needed for `P` to exist
(`dim P = l-2 >= 0`) and for `k = l-1 >= 1` in Lemma 3.2; `l <= D-2` is needed
for `k <= n-2` there.

**Slack.** The final budget is `784.4 eta` against the claimed `800 eta`, so
Theorem R has about `2` percent of slack and Corollary R1 about `2` percent
(`392` against `400`). Any future loosening of Lemma 4.1's `alpha <= 188 eta`
by more than that factor has to be paid for in the claim's constants.

## Lemma F (folding is free)

This lemma is not used in Theorem R; it removes one of the two difficulties that
`dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` lists under "Evidence
against", and is stated here because its proof is two lines in the present
notation. Use the DKKMS notation of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`: a folding class `C`
with representative `R_C`, a class label `sigma_C in (R_C)^*`, and its unfolding
at a member `(U,L)` equal to `tilde sigma_U|_L` where `tilde sigma_U` is the
linear functional on `R_C + H_U` with `tilde sigma_U|_(R_C) = sigma_C` and
`tilde sigma_U|_(H_U) = h_U`.

**Lemma F.** Fix a `k`-tuple `U` and suppose `alpha in (X_U)^*` satisfies
`alpha|_L = tilde sigma_U|_L` for *every* `L` with `(U,L) in C`, for every class
`C` meeting `U`. Then `alpha|_(H_U) = h_U`, so `alpha` satisfies all `k`
equations of `U` and is a legal A-label of the outer game `Phi_k`.

*Proof.* Fix a class `C` meeting `U` and put `M := R_C + H_U`, of dimension
`l + k`. The members of `C` over `U` are exactly the `L in Gr(X_U, l)` with
`L < M` and `L cap H_U = 0`. Every `v in M \ H_U` lies in such an `L`: extend
`<v>` to an `l`-dimensional complement `L` of `H_U` inside `M`, which is
possible because `v notin H_U`. Hence `alpha` and `tilde sigma_U` agree on
`M \ H_U`. A proper subspace's complement spans, so `M \ H_U` spans `M` (here
`H_U != M` because `l >= 1`), and both maps are linear, so they agree on all of
`M`, in particular on `H_U`. By construction `tilde sigma_U|_(H_U) = h_U`. QED

## Check

`python3 experiments/grassmann-99-rigidity-2026-09-18/check_grassmann_99_rigidity.py`,
seed 20260918. It verifies Lemma 3.2 (exact spectra against the closed formula,
seven parameter points), Lemma 1.2 (exhaustive flag counts for four parameter
points, all exactly uniform) and the conclusion of Theorem R (exact `eta` and
exact `min_A Pr_L[sigma_L != A|_L]` for six labelling families at four sizes;
worst ratio `3.0`, well inside `800`).
