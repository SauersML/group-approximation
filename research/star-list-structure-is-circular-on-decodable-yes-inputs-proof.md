---
rg: 2
id: star-list-structure-is-circular-on-decodable-yes-inputs-proof
kind: route
title: Build the flip orientation from the solution of a J-instance, bound every lift labelling star by star (two-sided half agreement off one branch per reference, one bit against two halves on flat stars, Q-uniformity for the rest), then splice it into any selector by Gaussian elimination
target: star-list-structure-is-circular-on-decodable-yes-inputs
requires:
  - dkkms-list-seed-needs-lists-exponential-in-l
  - dkkms-ev-list-structure-needs-lists-exponential-in-k
  - value-free-star-list-references-put-np-in-rp
  - dkkms-near-perfect-labellings-are-outer-honest
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
artifacts:
  - experiments/ugc-star-splice-2026-09-17/check_star_splice.py
---

The notation is that of the target. "LS Lemma i" means Lemma i of
`dkkms-list-seed-needs-lists-exponential-in-l-proof`. "Lemma A" is Lemma A of
`dkkms-ev-list-structure-needs-lists-exponential-in-k`.

## Step 0: inputs

* **Star law (LS Lemma 1).** Given `(U, V)` with `L' ∩ H' = 0`, the seed `L'`
  is uniform on the `(l-1)`-spaces of `X_V` avoiding `H'`. Given the star
  `(q, U)` with `q = (V, L')`, the direction `x_e` is uniform on
  `X_U \ (L' + H_U)`, and `L = L' + <x_e>`.
* **Growth set (LS Lemma 4 and its proof).** If `Phi` is onto `X_V`, then
  `x_e ∉ W_U` implies `c(L) = c(L')`. Also `W_U ⊇ L' + H_U`,
  `dim W_U = 3k - l + r'` with `r' = rank phi|_(L') = l - 1 - N`, and
  `Pr[x_e ∈ W_U | star] <= 2^(-1-N)`.
* **Small events (LS Lemma 7).** Given `V` (and `U`, since the proof only uses
  `H'`): (a) `Pr[M̄ ∩ N0 != 0] <= 2^(-s-1)`; (b) for every nonzero
  `p ∈ F_2^n`, `Pr[p ∈ P] < 2^(-s-1)`, where `P = Phi(L')` and
  `c(L') = P ∩ K`.
* **Lemma A.** For a proper subspace `W < X` and `x` uniform on `X \ W`, a
  functional `psi` with `psi|_W != 0` has `Pr[psi(x) = 0] = 1/2` exactly.
  (Direct proof: `X \ W` is a union of cosets `w0 + W`, and on each of them
  `psi` takes both values equally often because `psi|_W != 0`.) Hence
  `Pr[psi(x) = 1] = 1/2` as well.
* **Q-closeness (`dkkms-near-perfect-labellings-are-outer-honest-proof`,
  "Distance between P and Q").** Given `U`, the `G_multi` law of `(L', L)` is
  within total variation `SD*` of the law `Q`: `L'` uniform on the
  `(l-1)`-spaces of `X_U`, then `L` uniform among the `l`-spaces containing
  `L'`. Under `Q`, `(L', L)` is a uniform flag. So given `L`, `L'` is a uniform
  hyperplane of `L`, and it equals any fixed hyperplane with probability
  `1/(2^l - 1)`.

## Step 1: the balanced choices exist

Fix a star and a label `tau` of `L'`. The two preimages of `tau` differ by
`nu_(L')`, and `nu_(L')(x_e) = 1`. So choosing `pref_e(tau)` uniformly and
independently makes `pref_e(tau)(x_e)` a uniform independent bit on each free
copy. The free copies of a star at `tau` number `m >= 2^(3k-l) - 2^(k+l-1)`
`>= 2^(3k-l-1)`. At `tau != tau_h` this is all of `X_U \ (L' + H_U)`. At
`tau_h` on a non-flat star it is `W_U \ (L' + H_U)`, and `dim W_U >= 3k - l`.
For fixed `(lambda, tau, b)`, Hoeffding gives

```text
Pr[ | #{free e : lambda(x_e) = pref_e(tau)(x_e) + b} - m/2 | > eta m ]  <=  2 exp(-2 eta^2 m)  <=  2 exp(-2^(k-l)).
```

There are `2^(3k)` functionals, at most `2^(l-1)` labels and `2` bits. A union
bound leaves positive probability once `2^(3k+l+1) exp(-2^(k-l)) < 1`, and a
star has `2^(O(k))` copies, so resampling finds a balanced choice in time
`2^(O(k))` per star. The deviation `eta m` is at most `eta` times the star
mass. ∎

The preferred preimages at `tau_h` are legal: `a*|_L` restricts to
`a*|_(L') = tau_h`. On a flat star `c(L') = 0`, so `a* = y_(G(0)) = y_0 = x`,
and the flip `x|_L + nu_(L')` also restricts to `x|_(L') = tau_h`.

## Step 2: item 1 (the value of the defect witness)

Put `W := (sigma, (tau, b))` with `sigma := h_G` on A-vertices,
`tau := h_G` on B-vertices, and `b := 0`. Let `U` be clean for `x` (all its
equations satisfied) and `Phi` onto `X_V`. By LS Lemma 3, the A-label unfolds
at `(U, L)` to `y_(G(c(L)))|_L`, and `tau_q = y_(G(c(L')))|_(L') = tau_h`.

Take a copy with `x_e ∉ W_U`. By Step 0, `c(L) = c(L')`. So
`sigma_(U,L) = a*|_L = pref_e(tau_h)`, and with `b_q = 0` the copy is
lift-satisfied. Its mass in the star is `>= 1 - 2^(-1-N)`. Averaging over
stars, and replacing the law of `N` by its limit law at total-variation cost
`2^(l-k)` (LS Lemma 5), gives

```text
val(U_o*, W)  >=  1 - E[2^(-1-N_l)] - 2^(l-k) - beta_bad - delta_dirty  =  v(l) - 2^(l-k) - beta_bad - delta_dirty .
```

Here `delta_dirty` is the mass of tuples that are not clean. It is `0` when
`x` satisfies every equation. The degenerate copies are counted as `0`. On flat
stars they are in fact unsatisfied by `b = 0`, which is the point of the flip.
Theorem LS gives `v(l) >= 0.6096` for `l >= 8`. ∎

## Step 3: the star inequality

Let `W' = (sigma, (tau, b))` be any lift labelling of `U_o*`, let
`H = (sigma, tau)`, and let `T` be the set of copies it lift-satisfies. Fix a
star `(q, U)`. In it, `tau_q` and `b_q` are constants. Let `lambda` be any
functional on `X_U`.

If `e ∈ T`, then `sigma_(U,L)|_(L') = tau_q`, so `e ∈ Sat(H)`. Also
`ev_e(sigma) = sigma_(U,L)(x_e) = pref_e(tau_q)(x_e) + b_q`, since
`nu_(L')(x_e) = 1`. If moreover `e ∉ X(H, lambda)`, then `ev_e(sigma) = lambda(x_e)`.
Hence

```text
T  ⊆  X(H, lambda)  ∪  Agr(lambda),     Agr(lambda) := { e : lambda(x_e) = pref_e(tau_q)(x_e) + b_q },
Pr[T | star]  <=  Pr[X(H, lambda) | star] + Pr[Agr(lambda) | star].              (3.1)
```

**Per-star bound.** Call the star **covered by `lambda`** if `Phi` is onto
`X_V`, the star is not flat, `tau_q = tau_h`, and
`psi := (lambda - a*)|_(X_U) ∈ W_U^⊥`. If the star is not flat and not covered
by `lambda`, then

```text
Pr[Agr(lambda) | star]  <=  1/2 + eta .                                          (3.2)
```

*Proof.* If `tau_q != tau_h`, every copy is free, and balance (Step 1) gives
(3.2). If `tau_q = tau_h`, split the star into `F := {x_e ∈ W_U}` and
`N := {x_e ∉ W_U}`. On `F` the copies are free (the star is not flat), so
`Agr ∩ F` has at most `(1/2)Pr[F] + eta` of the star mass. On `N`,
`pref_e(tau_h) = a*|_L`, so `Agr ∩ N = {psi(x_e) = b_q} ∩ N`. Given `N`,
`x_e` is uniform on `X_U \ W_U`, because its law is uniform on
`X_U \ (L' + H_U)` and `W_U ⊇ L' + H_U`. As `psi ∉ W_U^⊥`, Lemma A gives
exactly `1/2` for either value of `b_q`. Summing gives (3.2). ∎

## Step 4: one branch per reference, and the covered mass

Let `Phi` be onto `X_V`. Then `phi` is onto `X_U`, and
`W_U = (phi|_(X_U))^(-1)(phi(L'))`, so

```text
W_U^⊥  =  { omega ∘ phi |_(X_U)  :  omega ∈ (F_2^l)^*,  omega|_(phi(L')) = 0 } .
```

Since `a* = y_d = x + <d, zeta(.)>` with `d = G(c(L'))`, a covered star has

```text
lambda|_(X_U)  =  x|_(X_U) + (omega ∘ phi + <d, zeta>)|_(X_U)  =  x|_(X_U) + ((omega, d) ∘ Phi)|_(X_U).
```

`Phi` maps `X_U` onto `F_2^n`, so the dual map
`(F_2^n)^* -> X_U^*, (omega, d) -> ((omega, d) ∘ Phi)|_(X_U)` is injective.
So `lambda^j_U` determines at most one pair `(omega_j, d_j)`, and hence at most
one branch `d_j = d_j(U)`, which depends on `U` only. A star covered by
`lambda^j_U` has `G(c(L')) = d_j(U)`.

* If `d_j != 0`, then `(0, d_j) ∈ c(L') ⊆ P`. Given `(U, V)`, this has
  probability `< 2^(-s-1)` by LS Lemma 7(b).
* If `d_j = 0`, then `c(L') = 0` and the star is not flat, so
  `M̄ ∩ N0 != 0`. This has probability `<= 2^(-s-1)` by LS Lemma 7(a). This
  event does not depend on `j`, so it is counted once for all `j` with
  `d_j = 0`.

So, for every list `Lambda` of `L` references,

```text
Pr_stars[ the star is covered by some lambda^j_U ]  <=  (L + 1) 2^(-s-1) .     (4.1)
```

The references are arbitrary. Nothing about value or outer consistency was used.

## Step 5: flat stars

Take a flat star. If `tau_q != tau_h`, every copy is free and (3.1)-(3.2) hold
as in Step 3. So let `tau_q = tau_h = x|_(L')`. Here `N = 0`, so
`dim phi(L') = l - 1`, and `W_U` is a hyperplane of `X_U`.

**Case lemma.** For a copy `e` of the star with `e ∈ T`, write
`mu_(U,L) := sigma_(U,L) - x|_L`. Then `mu_(U,L)|_(L') = 0`, so
`mu_(U,L) ∈ {0, nu_(L')}`, and

```text
e ∈ T   =>   ( mu_(U,L) = 0  and  b_q = [x_e ∈ W_U] )   or   ( e ∈ T2 ),
T2  :=  { copies with mu_(U,L) != 0 and ker mu_(U,L) = L' } .
```

*Proof.* Lift satisfaction says `sigma_(U,L) = pref_e(tau_h) + b_q nu_(L')`.
If `x_e ∉ W_U`, then `pref = x|_L`, so `mu = b_q nu_(L')`. If `x_e ∈ W_U`,
then `pref = x|_L + nu_(L')`, so `mu = (1 + b_q) nu_(L')`. If `mu = 0`, this
forces `b_q = [x_e ∈ W_U]`. Otherwise `mu = nu_(L')`, whose kernel is `L'`. ∎

The artifact (Part A) checks this lemma exhaustively for `m <= 5`,
`l ∈ {2, 3}`.

**The single bit.** `b_q` is one bit for the whole star. So the first
alternative has star mass at most `max(Pr[deg | star], Pr[not deg | star])`.
With `|X_U| = 2^(3k)`, `|L' + H_U| = 2^(k+l-1)` and `|W_U| = 2^(3k-1)`:

```text
Pr[not deg | star]  =  2^(3k-1) / (2^(3k) - 2^(k+l-1))  =  1 / (2 (1 - t)),     t := 2^(l-1-2k),
Pr[deg | star]      =  (2^(3k-1) - 2^(k+l-1)) / (2^(3k) - 2^(k+l-1))  <  1/2 .
```

Since `1/(2(1-t)) - 1/2 = t/(2(1-t)) <= t` for `t <= 1/2`,

```text
Pr[T | flat star at tau_h]  <=  1/2 + 2^(l-1-2k) + Pr[T2 | star] .              (5.1)
```

This bound does not use any reference.

**The cross-star term.** The event `T2` depends only on the triple
`(U, L', L)`: `mu_(U,L)` is a function of the A-vertex `(U, L)`, and `T2`
asks that the seed `L'` equal the hyperplane `ker mu_(U,L)` of `L`. Summing
over all flat stars at `tau_h`, and then over all stars,

```text
Pr_(G_multi)[T2]  <=  Pr_Q[ L' = ker mu_(U,L) ] + SD*  <=  1/(2^l - 1) + SD* .   (5.2)
```

The first inequality is Q-closeness (Step 0), applied given `U`. The second
holds because, under `Q`, `L'` given `(U, L)` is a uniform hyperplane of `L`.
The artifact (Part B) shows on toy stars that this bound is needed and is
attained in order: the flip optimum `0.8333` is below `0.6667` plus the
largest `T2` share, `0.3889`.

## Step 6: summation (item 2)

Fix `Lambda`. For each star pick `j*` minimising `mu(X(H, lambda^j) | star)`,
and apply (3.1) with `lambda = lambda^(j*)_U`. By cases:
* **`Phi` not onto `X_V`.** Use `Pr[T | star] <= 1`, which costs `beta_bad`.
* **Covered by `lambda^(j*)`.** Use `Pr[Agr] <= 1`, which is `1/2` more than
  (3.2). By (4.1) this costs at most `(1/2)(L + 1) 2^(-s-1)`.
* **Flat at `tau_h`.** Use (5.1). The star-by-star `T2` terms sum to (5.2).
* **Every other star.** Use (3.1) and (3.2).

Averaging over stars, with `D_L(H, Lambda) = E_star mu(X(H, lambda^(j*)) | star)`:

```text
val(U_o*, W')  <=  1/2 + D_L(H, Lambda) + eta + 2^(l-1-2k) + 1/(2^l - 1) + SD* + (L+1) 2^(-s-1) + beta_bad
               =   1/2 + D_L(H, Lambda) + E .
```

Finally, `X(H, lambda) ⊆ X^C(H, lambda)`, so `D_L <= D^C_L`. No step used that
`x` satisfies the equations. This is item 2. ∎

The same proof works when the orientation is fixed per multi-edge
`(U, L)-(V, L')` rather than per copy. Degeneracy is a property of `L`
(`x_e ∈ W_U` iff `L <= W_U`, since `L' <= W_U`). In Step 1 the summands are
then the agreement fractions of whole multi-edges. These lie in `[0, 1]` and
have mean `1/2`, because the two preimages give complementary agreement at
every direction. There are `2^(l-1)` times fewer summands, which changes only
the Hoeffding exponent, to `2^(k-2l+1)`.

## Step 7: Proposition S (the splice)

**Running time.** `k`, `l` and `n = k - c` are constants of the reduction.
The instance `G(x)` has `|x|^(O(k))` stars, each with `2^(O(k))` copies.
Splitting into components is linear time. Deciding whether a component is a
J-copy has constant cost, since it has `2^n - 1` variables. For a J-copy,
one finds a map `u : variables -> F_2^n \ 0` that sends every equation to a
line. To do this, fix `n` points spanning the copy, give them the unit
vectors, and close under "the third point of a line", which gives
`u(p) + u(p') = u(p'')` for each equation. The per-star work of Step 1 and
the exact value of Step 2 cost `2^(O(k))` per star. So `S'` runs in
polynomial time.

**The labelling is a kernel map of rank `n`.** Put `Phi(e_p) := u(p)` on each
copy and sum over copies. It kills every equation vector, and it is onto
`F_2^n`. Any other identification of a copy with `F_2^n \ 0` that preserves
lines differs from `u` by some `M_c ∈ GL(F_2^n)`. This is the fundamental
theorem of projective geometry over `F_2` for `n >= 3`, and also direct from
the closure construction. Relabelling a copy by `M_c` is an automorphism of
that copy. The LS Step 7 surjectivity bound uses only that the label lines of
the `k` blocks of `U` are i.i.d. uniform lines of `F_2^n`, and that is
preserved by `M_c`. So on a J-instance with `N >= k` copies,
`delta_sur < 2^(n-k)`, and hence
`beta_bad <= delta_sur/(1 - 2^(l-1-k)) < 2^(n-k+1)`, as LS Step 6 states.

**Selector property.** If `S'` outputs `o*`, it has checked exactly that
`val(U_o*, (h_G, (h_G, 0))) >= 1/2 + gamma`, so the witness exists with
probability `1`. Otherwise `S'` outputs `S(x)`, which has the property with
probability `>= theta` on YES inputs. Either way `S'` is a constant-bias
selector.

**On J-instances.** Take `x = 0`, which satisfies every equation (or all but
the flipped lines, by Corollary N). Step 2 gives value
`>= v(l) - 2^(l-k) - beta_bad - delta_dirty >= 0.6096 - 2^(l-k) - 2^(n-k+1) - 2^(n-k)`.
This is `>= 0.605` once `2^(-c) <= 10^(-3)` and `k` is large, and
`c >= 12` gives that. So both tests pass and `S'` outputs `o*`, for every
`gamma <= 0.105`. ∎

## Step 8: the corollaries

**CIRC.** Let `l >= 8`, `2^(2-l) <= gamma' < gamma <= 0.105`,
`L <= gamma'^2 2^(k-l-16)`, `c = ceil(log2(1/gamma')) + 12`, `n = k - c` and
`s = n - l`. Then each term of `E` is bounded:
* `1/(2^l - 1) < 2^(1-l) <= gamma'/2`;
* `(L + 1) 2^(-s-1) <= gamma'^2 2^(k-l-16) 2^(-k+c+l-1) + 2^(-s-1)`
  `<= gamma'^2 2^(c-17) + 2^(-s-1) <= gamma'/16 + 2^(-s-1)`, using
  `2^c <= 2^13/gamma'`;
* `beta_bad < 2^(1-c) <= gamma'/2^11`;
* `eta + 2^(l-1-2k) + SD* + 2^(-s-1) -> 0` as `k -> oo`, with `l` and
  `gamma'` fixed. Here `SD* = (log log k / sqrt k) 2^(l+3) + 3 2^(l-k)`.

So `E < gamma'` for all large `k`. The artifact (Part D) finds the explicit
threshold. For `l = 8` and `gamma' = 2^(-6)` it is about `k >= 2^40`, and the
`SD*` term dominates.

Now let `S` be a constant-bias selector. On every J-instance with `N >= k`
copies, `S'` outputs `o*` deterministically (Step 7). Every lift labelling
`W'` of `o*` with value `>= 1/2 + gamma` has, by Theorem O item 2 and for
every list of at most `L` references,
`D^C_L(proj W', Lambda) >= gamma - E > gamma - gamma'`. So (Star-List^C) fails
for `S'` on a YES input. The converse direction is vacuous.

For the range of `L`: the Corollary DK^C budget is at most `exp(k/4)` for every
`q >= 0`, since `p gamma'/3 < 1`. Also `gamma'^2 2^(k-l-16) = exp(k ln 2 - O(l))`,
and `ln 2 > 1/4`. So the range contains the whole budget at large `k`. ∎

**PNP.** On YES inputs, DKKMS completeness gives a labelling of `G(x)` of value
`>= 1 - eps_c > 1/2 + gamma`. Deciding whether a partial labelling extends to
one of value `>= 1/2 + gamma` is in NP. So if `P = NP`, self-reduction finds a
labelling `H = (H_A, H_B)` with `val_G(H) >= 1/2 + gamma` in polynomial time.
Orient each copy by `pref_e(tau) := H_A(U, L)` when
`tau = H_A(U, L)|_(L')`, and arbitrarily otherwise. Then every copy satisfied
by `H` is lift-satisfied by `(H_A, (H_B, 0))`. So the lift value is
`>= 1/2 + gamma`, with probability `1`. Combined with CIRC, "(Star-List^C) for
every selector" implies that no selector exists, hence `P != NP`. ∎

**TR.** `X ⊆ X^C` gives `D^C_L >= D_L`. `D_L` takes the best `j` per star
`(V, L', U)`, which is the value of `D(h, Lambda)` under one particular index
map `i(U, V, L')`. Corollary EL bounds `D(h, Lambda)` for every index map. So
`D^C_L(h, Lambda) > 0.110` for every list of `L < 2^(k-l-11)` arbitrary
references, on rank-`(k-8)` J-instances. ∎

**N.** Let a copy carry one flipped line `l0`, with right-hand side `1`, and
`n >= 3`. Take a 3-dimensional subspace containing `l0`. Its 7 points and 7
lines form a Fano plane. Suppose some assignment satisfies every equation of
the copy. For any point `p` of the plane, the 3 lines through `p` cover the 7
points, with `p` covered 3 times. So the sum of their left-hand sides is the
sum of all 7 values, and it is the same for every `p`. The sum of the
right-hand sides is `1` for a point on `l0` and `0` for a point off `l0`,
which is a contradiction. So the value is `< 1`.

The zero assignment violates only the flipped lines, at most one per copy.
That is a fraction `<= 3/((2^n - 1)(2^(n-1) - 1))` of the equations, so the
instance is a YES input of Gap3Lin(`1 - eps`, ...) for any `eps` at least
that. The automorphism group of the underlying J-hypergraph (`GL_n` per copy,
together with permutations of copies) is transitive on equations. So each
block of a uniform legitimate tuple has a uniform equation, and
`delta_dirty <= 3k/((2^n - 1)(2^(n-1) - 1)) <= 2^(n-k)` at large `k`. Item 2
of Theorem O is unchanged, since it never used the equations' right-hand
sides. Item 1 loses `delta_dirty`, and Step 7 already allowed for that. ∎

## What the artifact checks

`experiments/ugc-star-splice-2026-09-17/check_star_splice.py` prints
`ALL PASS` and exits `0` in about 10 seconds. It checks:
* **Part A.** The case lemma of Step 5, exhaustively on `F_2^m` for `m <= 5`
  and `l ∈ {2, 3}`.
* **Part B.** On toy stars (`X = F_2^4`, `phi` the low two bits, `H = {0, 8}`
  or `{0}`), the exact optimum of the flip orientation against the bound of
  (5.1)-(5.2): `0.8333 <= 0.6667 + 0.3889` and `0.7857 <= 0.5714 + 0.4048`.
  It also checks the naive gap: honest `x` gets `0.6667` under the flip
  against `0.8472` under the random orientation.
* **Part C.** In the image model, that every covering functional is
  `x + (omega, G(c(L'))) ∘ Phi`, that agreement off the covered set is exactly
  `1/2` for both bits, and that each branch's covered mass is
  `<= (2^(l-1) - 1)/(2^n - 1) < 2^(-s-1)`.
* **Part D.** The numbers of CIRC for `8 <= l <= 20` and `gamma' = 2^(2-l)`:
  the threshold `k` beyond which `E < gamma'`, the Hoeffding condition, the
  value `>= 0.605`, and `ln 2 > 1/4`.

What is not machine-checked: Q-closeness (quoted from
`dkkms-near-perfect-labellings-are-outer-honest-proof`), and LS Lemmas 1, 4,
5 and 7 (quoted from the LS route).
