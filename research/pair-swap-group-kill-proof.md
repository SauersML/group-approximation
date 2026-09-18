---
rg: 2
id: pair-swap-group-kill-proof
kind: route
title: Switching lemma, degree-two moment matching, and Maroti's order bound against the moment entropy count
target: pair-swap-groups-of-smooth-pairing-designs-contain-alt
requires: [primitive-groups-without-alt-have-order-below-50-n-sqrt-n]
artifacts:
  - experiments/pair-swap-group-kill-2026-09-17/check_pair_swap_group_kill.py
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
---

Notation: `N = 2n`, `K` is the set of all 2-subsets of `[N]`, and for
`W <= K` and a perfect matching `M`, `X_W(M) = |M cap W|`. "Uniform" means
the uniform law on all `(N-1)!!` perfect matchings. Assume `n >= 3`
throughout. The only import is Maroti's bound
(`primitive-groups-without-alt-have-order-below-50-n-sqrt-n`).

## Lemma 1 (degree-two moment matching)

If `mu` is exactly 2-wise uniform, then `E_mu Q = E_unif Q` for every
polynomial `Q` of degree at most two in the edge indicators `1[e in M]`.

*Proof.* A degree-two monomial `1[e in M] 1[f in M]` with `e != f` vanishes
identically on matchings when `e, f` share a point. Otherwise its
expectation is `1/((N-1)(N-3))` under both laws. Degree-one monomials have
expectation `1/(N-1)` under both, and `1[e in M]^2 = 1[e in M]`. Linearity
finishes. In particular `E_mu X_W = E_unif X_W` and
`Var_mu X_W = Var_unif X_W` for every `W <= K`.

## Lemma 2 (switching lemma)

Let `w : K -> R` be such that `w(M) = sum_(e in M) w(e)` is the same for all
perfect matchings `M` of `[N]`, `N >= 4`. Then there is `f : [N] -> R` with
`w(ab) = f(a) + f(b)` for all `a != b`. If moreover `w` takes values in
`{0,1}`, then the support of `w` is empty, all of `K`, a star
`star(v) = {e : v in e}`, or a co-star `K \ star(v)`. Conversely these four
kinds of sets have constant `X_W` (values `0`, `n`, `1`, `n-1`).

*Proof.* For distinct `a,b,c,d`, fix a perfect matching `R` of the other
`N-4` points. The matchings `R + {ab,cd}`, `R + {ac,bd}`, `R + {ad,bc}` have
equal weight, so

```
w(ab)+w(cd) = w(ac)+w(bd) = w(ad)+w(bc).                            (4pt)
```

For distinct `a,b,c` put `g(a,b,c) = w(ab)+w(ac)-w(bc)`, symmetric in
`b,c`. For `d` outside `{a,b,c}`,
`g(a,b,c)-g(a,b,d) = [w(ac)+w(bd)] - [w(ad)+w(bc)] = 0` by (4pt). Using the
symmetry and this move one may replace either of the last two arguments by
any other point different from `a` and from the remaining argument, so
`g(a,.,.)` is a constant, written `2f(a)`. Adding
`g(a,b,c) = 2f(a)` and `g(b,a,c) = 2f(b)` gives `2w(ab) = 2f(a)+2f(b)`.

Now let `w` be 0/1. For distinct `a,b,c`,
`f(a) = (w(ab)+w(ac)-w(bc))/2` lies in `{-1/2, 0, 1/2, 1}`.

* If `f(a) = 1`, then `w(ab) = 1+f(b) <= 1` forces `f(b) <= 0`, and
  `w(ab) >= 0` with `f(b) >= -1/2` forces `f(b) = 0` for all `b != a`. So
  `w(ab) = 1` exactly when `a` is an end: `w = 1_star(a)`.
* If `f(a) = -1/2`, then `w(ab) = f(b)-1/2 >= 0` forces `f(b) = 1/2` for
  all `b != a` (the value `3/2` is excluded). So `w = 1_(K \ star(a))`.
* Otherwise every `f` value is `0` or `1/2`. Two different values would give
  `w(ab) = 1/2`. So `f` is constant and `w` is `0` or `1` identically.

The converse counts are immediate. The script checks the dimension of the
real solution space (`N`) for `N = 4,6,8` and enumerates all 0/1 solutions
for `N = 4,6`.

## Lemma 3 (moment entropy count)

Let `mu` be any law on perfect matchings with `||1_E D_mu||_q <= C` for some
real `q > 1`, and `nu_(mu,m)(E) >= theta > 0`. Then with `q' = q/(q-1)`,

```
|supp mu| >= (theta/C)^(q') m^n.
```

*Proof* (artifact Section 4, repeated with every step). `nu_(mu,m)` is
carried by `S`, the union over `M in supp mu` of the `m^n` colorings
constant on the pairs of `M`, so `D_mu` vanishes off `S` and
`U(S) <= |supp mu| m^(-n)`. Holder with exponents `q, q'` gives
`theta <= E_U[1_E D_mu 1_S] <= ||1_E D_mu||_q U(S)^(1/q')
<= C (|supp mu| m^(-n))^(1/q')`. Rearranging gives the bound.

## Proof of the theorem

Let `mu` be exactly 2-wise uniform with the moment bound and mass
`theta_n`, and let `H <= S_N` contain `h_M` for every `M in supp mu`.

**(a) `H` is transitive.** Every pair `{a,b}` has `Pr_mu[ab in M] =
1/(N-1) > 0`, so some support matching `M` contains it and `h_M(a) = b`.

**(b) `H` is primitive.** Suppose `H` preserves a partition of `[N]` into
`r >= 2` blocks of size `b`, `1 < b < N`. For a block `B` and `M in supp mu`,
`h_M(B)` is a block. If `h_M(B) = B`, no pair of `M` leaves `B`. If
`h_M(B) = B' != B`, every point of `B` is matched into `B'`. Hence
`X_(BB')(M) := |M cap K_(B,B')|` lies in `{0, b}` for all blocks `B != B'`,
where `K_(B,B')` is the set of pairs with one end in each. The polynomial

```
S(M) = sum_(B<B') X_(BB')(M) (b - X_(BB')(M))
```

has degree two in the edge indicators, is nonnegative on all matchings
(since `X_(BB') <= b`), and vanishes on `supp mu`. By Lemma 1,
`0 = E_mu S = E_unif S`. So `S = 0` on every matching. It remains to exhibit
a matching `M0` with `0 < X_(BB')(M0) < b` for one pair of blocks.

* `r = 2`, so `b = n >= 3`. If `b` is odd, match one `a in B` with one
  `a' in B'` and match the even sets `B - a`, `B' - a'` internally:
  `X = 1`. If `b` is even (so `b >= 4`), use two cross pairs and match the
  rest of each block internally: `X = 2 < b`.
* `r >= 3`. Match `a in B` with `a' in B'`. If `b` is odd, match `B - a`
  and `B' - a'` internally. If `b` is even, match all but one point of each
  of `B - a`, `B' - a'` internally, and match the two leftover points to two
  distinct points of a third block `B''` (which has `b >= 2` points). The
  remaining points lie outside `B cup B'`, have even count, and are matched
  arbitrarily. Then `X_(BB')(M0) = 1 < b`.

This contradicts `E_unif S = 0`, since `M0` has positive uniform mass.

**(c) `H` contains `A_N`.** Otherwise `H` is a primitive group of degree
`N` not containing `A_N`, and by the import `|H| < 50 N^(sqrt N)`. The map
`M -> h_M` is injective and lands in `H`, so
`|supp mu| < 50 N^(sqrt N)`. Lemma 3 gives
`|supp mu| >= (theta_n/C)^(q') m^n`. Taking logarithms, the contradiction
holds as soon as

```
log 50 + sqrt(2n) log(2n) < n log m - q' log(C/theta_n),
```

which holds for all large `n` because `log m >= log 2 > 0`, `q'` and `C` are
fixed and `log(1/theta_n) = o(n)`. Let `n_1` be an `n >= 3` beyond which it
always holds. This proves the theorem.

Illustrative thresholds, with the arbitrary polynomially small choice
`theta_n = (n+1)^(-(m-1))`: the script finds the first crossing `n = 202`
for `(m,q,C) = (2,2,10)`, `233` for `(2,2,1000)`, `77` for `(3,4,100)` and
`83` for `(5,2,10^6)`, and checks that the inequality keeps holding for every
`n` from there up to `20000`. Beyond that it persists: the derivative of the
right side minus the left side in `n` is
`log m - q'(m-1)/(n+1) - (log(2n)+2)/sqrt(2n)`, which is increasing for
`n >= 1` and already positive at the crossing in each case.

The equivalent form: if a structure `Sigma` on `[N]` is preserved by all
`h_M`, then `H = Aut(Sigma)` contains `A_N`.

**Necessity of each step.** The script finds by linear programming that
exact 2-wise uniform laws on the fixed-point-free involutions of a group
are infeasible for the intransitive groups `S_4 x S_2`, `S_6 x S_2`
and the imprimitive groups `S_3 wr S_2`, `S_2 wr S_3`, `S_4 wr S_2`,
`S_2 wr S_4`, feasible for `S_6`, `S_8`, and **feasible for `M_12`**
(order 95040, 396 fixed-point-free involutions). So no argument of degree
two alone kills primitive groups; the order step is needed. (It also
reports `PGL(2,5)` on 6 points and `AGL(3,2)` on 8 points as infeasible;
those two are not asserted by the theorem at such small degree.)

## Proof of the single-orbit corollary

Let `mu` be uniform on the orbit `O = G . M0` of a perfect matching under
`G <= S_N`, exactly 2-wise uniform, with the moment bound and mass
`theta_n`, and `n >= max(3, n_1)`.

**Step 1 (invariant pair sets).** Let `W <= K` be `G`-invariant. Then
`X_W(gM) = |gM cap W| = |M cap g^(-1) W| = X_W(M)`, so `X_W` is constant on
`O` and `Var_mu X_W = 0`. By Lemma 1, `Var_unif X_W = 0`, so `X_W` is
constant on all perfect matchings. By Lemma 2, `W` is empty, `K`, a star or
a co-star.

**Step 2 (2-homogeneity).** The `G`-orbits on `K` are nonempty, pairwise
disjoint, invariant, and cover `K`. If there is one orbit, `G` is
2-homogeneous on `Omega = [N]`. Otherwise each orbit is a star or a
co-star. Two different stars meet (in the pair of their centres), a star
and a co-star with different centres meet (in a pair `vx`, `x` outside both
centres), and two different co-stars meet (in a pair avoiding both
centres, which exists since `N >= 4`). So the orbits are exactly
`star(v)` and `K \ star(v)` for one `v`. Then `G` fixes `v` (the only point
lying in every pair of `star(v)`, since `N >= 3`) and is 2-homogeneous on
`Omega = [N] \ {v}`. In both cases `|Omega| >= N - 1 >= 5`, and `G` acts
faithfully on `Omega`.

**Step 3 (primitivity).** A 2-homogeneous group on `Omega`, `|Omega| >= 3`,
is primitive. If `A` were a proper nonempty invariant subset, the pairs
crossing between `A` and `Omega \ A` would form a nonempty invariant proper
set of pairs unless `|A| = |Omega \ A| = 1`. If a block system had blocks of
size `1 < b < |Omega|`, the pairs inside blocks and the pairs across blocks
would both be nonempty and invariant.

**Step 4 (dichotomy).** If `G^Omega` does not contain `A_Omega`, the import
gives `|O| <= |G| < 50 |Omega|^(sqrt |Omega|) <= 50 N^(sqrt N)`, and Lemma 3
gives the same contradiction as in (c). So `G >= A_Omega`. The group
`S_Omega` acts transitively on perfect matchings of `[N]`: when `Omega`
omits `v`, a matching is a choice of the partner of `v` together with a
matching of the remaining `N-2` points, and `S_Omega` moves both freely.
The stabilizer of `M0` in `S_Omega` contains the transposition of a pair of
`M0` avoiding `v` (one exists since `n >= 2`), an odd permutation. So
`|A_Omega . M0| = |A_Omega| / (|Stab_(S_Omega)(M0)|/2) = |S_Omega . M0|`,
and `O` contains every perfect matching. So `mu` is uniform on all perfect
matchings.

**Automorphism form.** For an automorphism `g` of a regular 2-to-1 instance
fixing the left vertex `u`, with label permutations `g_u` at `u` and `g_v`
at `v`, the relation `pi_(g e) o g_u = g_(g v) o pi_e` shows that the kernel
pairing of `g e` is `g_u` applied to the kernel pairing of `e`. The map
`e -> ker pi_e` is equivariant, so when the automorphisms fixing `u` act
transitively on the edges at `u`, every fibre over the orbit has the same
size, and the edge-uniform law at `u` is the uniform law on a single orbit
of the image group `G = {g_u}`.

## What this does not cover

* Laws whose kernel involutions generate a group containing `A_N`. This
  includes the random-family and composition constructions of the
  smooth-design artifact (`D o Q` with `D` a `2t`-wise uniform permutation
  family), whose swaps `sigma h_M sigma^(-1)` are spread across `S_N`, and
  families of involutions generating `Alt` of exponential size.
* Laws that are invariant under a small group but not uniform on a single
  orbit. The uniform law on all matchings is invariant under every group,
  so no statement of the form "G-invariant implies rich" can hold; the
  corollary really needs a single orbit.
* The NP-hardness question itself. The theorem constrains the local label
  symmetry of any instance witnessing `finite-moment-pairing-2to1-hardness`
  at large `n`; it does not refute that claim.
