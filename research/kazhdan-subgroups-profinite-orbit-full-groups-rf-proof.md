---
rg: 2
id: kazhdan-subgroups-profinite-orbit-full-groups-rf-proof
kind: route
title: The same-atom indicator is almost invariant, its Kazhdan projection is an invariant near-relation, and the clusters of its fibre measure form a finite K-set
target: kazhdan-subgroups-of-profinite-orbit-full-groups-are-rf
requires: []
---

**Notation.**
- Write `g` for `rho(g)` and fix Borel representatives. Relations in `K` then hold off a null set,
  and since `K` is countable, off one null set simultaneously.
- The atoms of level `i` are `C = p_i^{-1}(t)` for `t in X_i`. There are `n_i` of them, and each has
  `mu(C) = 1/n_i` by transitivity. `C(x)` denotes the atom containing `x`.
- The level-`i` partitions refine one another and separate the points of `X`. So they generate the
  Borel sigma-algebra, and `E_i`, the conditional expectation onto level `i`, satisfies
  `E_i(f) -> f` in `L^1` for every `f in L^1` (martingale convergence).
- `h in H` maps each atom of level `i` onto an atom of level `i`, because `p_i` is equivariant.
- `MALG` is the measure algebra of `(X, mu)`, with metric `d(A, B) = mu(A Δ B)`. It is a Polish
  space, and `K` acts on it by isometries, `A -> gA`.

**Step 0: selections.** Enumerate `H = {h_1, h_2, ...}`. For `g in K`, put `c_g(x) = h_n` for the least
`n` with `g x = h_n x`, and `A_(g,h) = {x : c_g(x) = h}`. The `A_(g,h)` are Borel and partition `X`
up to a null set. No cocycle identity is needed.

**Step 1: the vectors.** Let `pi` be the diagonal Koopman representation of `K` on `L^2(X x X, mu x mu)`,
`(pi(g)F)(x, y) = F(g^{-1}x, g^{-1}y)`. Put `Y_i = {(x, y) : C(x) = C(y)}`. Then
`(mu x mu)(Y_i) = n_i (1/n_i)^2 = 1/n_i`, so `f_i = sqrt(n_i) 1_(Y_i)` is a unit vector.

**Step 2: almost invariance.** Fix `s in K`. If `(x, y) in Y_i` and `c_s(x) = c_s(y) = h`, then
`s x = h x` and `s y = h y` lie in the one atom `h C(x)`, so `(s x, s y) in Y_i`. Since the diagonal map `(x, y) -> (sx, sy)`
preserves `mu x mu`,

```text
||pi(s) f_i - f_i||^2 = 2 n_i (mu x mu){(x,y) in Y_i : (sx, sy) notin Y_i}
                      <= 2 n_i (mu x mu){(x,y) in Y_i : c_s(x) != c_s(y)}
                      = 2 sum_C mu(C) (1 - sum_h a_(C,h)^2),
```

where `a_(C,h) = mu(A_(s,h) ∩ C) / mu(C)`. Here we used `n_i mu(C)^2 = mu(C)`, and the fact that for
independent uniform points `x, y` of `C` the probability that `c_s(x) != c_s(y)` is
`1 - sum_h a_(C,h)^2`.

Since `sum_h a_(C,h) = 1`, the right side equals
`2 sum_h ∫ E_i(1_(A_(s,h))) (1 - E_i(1_(A_(s,h)))) dmu`. For each fixed `h`, the integrand tends to
`1_A (1 - 1_A) = 0` in `L^1`. Term `h` is at most `mu(A_(s,h))`, and these are summable, so dominated
convergence over `h` gives

```text
gamma_i(s) := ||pi(s) f_i - f_i|| -> 0      (i -> infinity), for every s in K.        (AI)
```

**Step 3: Kazhdan projection.** By definition of (T) for a discrete group, there is a finite set
`S ⊂ K` and `epsilon > 0` such that every unitary representation without nonzero invariant vectors
has `max_(s in S) ||sigma(s) v - v|| >= epsilon ||v||` for all `v`. Let `P` be the projection onto the
`pi(K)`-invariant vectors. Apply this to the restriction of `pi` to the invariant complement
`ker P`, with `v = f_i - P f_i`. Then `pi(s) v - v = pi(s) f_i - f_i`, so

```text
||f_i - xi_i|| <= delta_i := epsilon^{-1} max_(s in S) gamma_i(s) -> 0,     xi_i := P f_i.
```

`pi` commutes with complex conjugation and `f_i` is real, so `xi_i` is real.

**Step 4: an invariant near-relation.** Put `E = {(x, y) : xi_i(x, y) > sqrt(n_i)/2}`. Since `xi_i` is
`pi(K)`-invariant, `(mu x mu)(E Δ (g x g)E) = 0` for every `g in K`. On `E Δ Y_i` we have
`|xi_i - f_i| >= sqrt(n_i)/2`, so

```text
(mu x mu)(E Δ Y_i) <= 4 delta_i^2 / n_i.                                            (NR)
```

Let `E(x) = {y : (x, y) in E}` and `Psi(x) = E(x) in MALG`. By Fubini `Psi` is Borel. From
`(g x g)E = E` modulo null sets and the measure preservation of `g`, we get `Psi(g x) = g Psi(x)` for
a.e. `x`, for each `g in K`. So `m := Psi_* mu` is a `K`-invariant Borel probability measure on `MALG`.

Also `∫ d(Psi(x), C(x)) dmu(x) = (mu x mu)(E Δ Y_i)`, since `Y_i(x) = C(x)`.

**Step 5: the finite K-set.** Fix `tau in (0, 1/10]` and put `r = tau/n_i`. Distinct atoms satisfy
`d(C, C') = 2/n_i = 2r/tau >= 20 r`. Define:

```text
Q    = {A in MALG : m(B(A, r)) >= 1/(2 n_i)}       (B = open ball),
A ≈ B  iff  there is a chain A = A_0, ..., A_t = B in Q with d(A_j, A_(j+1)) < 4r.
```

`K` acts by isometries and preserves `m`, so `Q` and `≈` are `K`-invariant. Hence `K` permutes the set
`Q/≈` of classes.

This set is finite. If `A` and `A'` lie in different classes then `d(A, A') >= 4r`, so their `r`-balls
are disjoint, and each has `m`-mass at least `1/(2 n_i)`. So there are at most `2 n_i` classes. This
gives a homomorphism

```text
rho_(i,tau) : K -> Sym(Q/≈).
```

**Step 6: clean atoms have their own small classes.**

*Good points.* Call `x` good if `d(Psi(x), C(x)) < r`. By Markov and (NR), the bad set has measure

```text
beta := mu{x bad} <= (4 delta_i^2 / n_i) / r = 4 delta_i^2 / tau.
```

*Clean atoms.* Call an atom `C` clean if both of the following hold:
- (a) at least half of `C`, by measure, is good;
- (b) `mu{x bad : Psi(x) in B(C, 8r)} < 1/(2 n_i)`.

*Few atoms are unclean.*
- Each atom failing (a) contains bad mass at least `1/(2 n_i)`.
- The balls `B(C, 8r)` are pairwise disjoint, since `16 r < 20 r`. So the atoms failing (b) can be
  charged disjointly to bad mass at least `1/(2 n_i)` each.

Hence at most `4 beta n_i` atoms are unclean, and their union has measure at most `4 beta`.

*Claim.* If `C` is clean, then `C in Q`, and every `A in Q` with `d(A, C) < 6r` has `d(A, C) < 2r`.

*Proof.*
- **`C in Q`.** By (a), `m(B(C, r)) >= mu{x in C good} >= 1/(2 n_i)`.
- **Setup.** Suppose `A in Q` and `2r <= d(A, C) < 6r`. Split the mass `m(B(A, r)) >= 1/(2 n_i)` by
  the source point `x`.
- **Good `x` in `C`.** `d(Psi(x), A) >= d(A, C) - r >= r`, so these contribute nothing.
- **Good `x` in another atom `C'`.** `d(Psi(x), A) >= d(C', C) - r - d(A, C) > 20r - 7r`, so these
  contribute nothing.
- **Conclusion.** The whole mass comes from bad `x` with `Psi(x) in B(A, r) ⊂ B(C, 7r)`. That is
  less than `1/(2 n_i)` by (b), a contradiction.

*Consequence.*
- For clean `C`, a chain in `Q` that starts at `C` with steps `< 4r` never leaves `B(C, 2r)`. A step
  from a point within `2r` of `C` lands within `6r`, and then, by the claim, within `2r`.
- So the class `[C]` of `C` lies in `B(C, 2r)`.
- Distinct clean atoms have distinct classes, since `d(C, C') >= 20r`.

**Step 7: separation.**

*Setup.* Let `g in K` with `g != 1` in `[R_H]`, so `s_g := mu{x : g x != x} > 0`.

*The moved mass is visible at fine levels.* The sets `{x : C(gx) != C(x)}` at level `i` increase with
`i`, and their union is `{x : gx != x}`, because the partitions separate points. So

```text
mu{x : C(gx) != C(x)} -> s_g.
```

*A fixed clean class forces little movement.* Suppose `rho_(i,tau)(g)` fixes the class `[C]` of a
clean atom `C`.
- `g C in Q`, since `Q` is `K`-invariant, and `g[C] = [gC]`.
- So `gC in [C] ⊂ B(C, 2r)`.
- Then `mu{x in C : gx notin C} = mu(gC \ C) = d(gC, C)/2 < r = tau mu(C)`.

*The contradiction.* If `rho_(i,tau)(g) = 1`, summing over clean atoms and adding the unclean mass
gives

```text
mu{x : C(gx) != C(x)} < tau + 4 beta <= tau + 16 delta_i^2 / tau.
```

Take `tau = min(1/10, s_g/4)`. For all large `i`:
- `16 delta_i^2 / tau < s_g/4`, by Step 3;
- the left side exceeds `s_g/2`.

This is a contradiction. Hence `rho_(i,tau)(g) != 1` for all large `i`. Every nontrivial element of
`rho(K)` survives in a finite quotient of `rho(K)`, since each `rho_(i,tau)` factors through `rho`. So
`rho(K)` is residually finite. QED.

**Remarks.**
- **Hypotheses used.** Measure preservation, and the fact that each element of `H` maps atoms to
  atoms. Transitivity of `H` on `X_i` gives equal atom masses. Nothing about `H` itself is used:
  neither amenability, soficity, (T), nor freeness of the action.
- **Where the proof would break for a Bernoulli host.** Step 2 needs a refining sequence of finite
  partitions that generates the sigma-algebra and is permuted atom-by-atom by every element of `H`.
  A mixing action has no such sequence, so (AI) is the step that fails.
- **Credit.** The Kazhdan-projection step is the standard one (Connes--Weiss, Schmidt, Popa). The
  cluster construction of Steps 5 to 7 appears to be new in this graph. The cluster construction
  replaces uniform stability in permutations, which is not available for Kazhdan groups:
  Becker--Chapman, JEMS 25 (2023) 3599--3632, arXiv:2005.06652, prove it for amenable groups and
  `SL_r(Z)`, `r >= 3`, and show it fails for free groups.
