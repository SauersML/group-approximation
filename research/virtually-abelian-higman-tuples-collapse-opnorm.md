---
rg: 2
id: virtually-abelian-higman-tuples-collapse-opnorm
kind: claim
title: Higman tuples generating virtually abelian groups collapse, and corona microstates stay 1/10 away from all of them
artifacts:
  - research/virtually-abelian-higman-tuples-collapse-opnorm-proof.md
  - experiments/virtually-abelian-higman-2026-09-17/check_va_collapse.py
  - experiments/virtually-abelian-higman-2026-09-17/out_check_va_collapse.txt
distinct_from:
  finite-image-higman-models-collapse-opnorm: that proves collapse when the generated subgroup of U(k) is finite and concludes countermodels must generate infinite groups, leaving generic-phase (irrational) monomial and torus-regauge models open; this proves finite-image tuples are norm-dense in all virtually abelian tuples, so every virtually abelian (typically infinite, dense in a torus extension) tuple collapses with the same constant, and adds a uniform distance bound for arbitrary tuples and an equivalence with (HMF5).
  thompson-v-gap-witnesses-need-unbounded-lie-closure: that treats exact representations of the virtually free G0 of Thompson V via the adjoint representation of the closure; this treats approximate Higman tuples of the free group, whose closures are typically all of U(k), and its robust invariant is the operator-norm distance to the virtually abelian tuples, not the Lie algebra of one closure.
  one-small-higman-generator-collapses-the-four-cycle: that assumes one generator is spectrally small; this assumes nothing about spectra, only that the tuple is near a tuple generating a virtually abelian group.
  higman-opnorm-collapse-is-a-one-unitary-z4-problem: that reformulates (HMF5) as a one-unitary Z/4 problem and records a local-descent census; this gives a different equivalent form of (HMF5), uniform approximability by finite-image tuples, and certifies that the stored census optima are at distance at least 0.043 from every virtually abelian tuple.
  higman-four-cycle-intrinsic-mf-seed: that is the open dimension-uniform collapse for all tuples; this proves it on the virtually abelian class and on its 1/10-neighbourhood in the corona limit, and shows the open statement is equivalent to uniform finite-image approximability.
---

**ESTABLISHED** by `virtually-abelian-higman-tuples-collapse-opnorm-proof`.

## Notation

For a four-tuple `u = (u_0,u_1,u_2,u_3)` in `U(k)^4` put

```text
D(u) = max_i || u_i u_(i+1) u_i^* - u_(i+1)^2 ||_op,     M(u) = max_i || u_i - 1 ||_op,
```

with indices modulo four.  This is the defect of the presentation `(HMF1)` of
`higman-four-cycle-intrinsic-mf-seed`.  Let `VA_k` be the set of tuples in
`U(k)^4` whose generated subgroup `<u_0,..,u_3>` is virtually abelian.
Equivalently, `u` lies in some closed subgroup `K <= U(k)` whose identity
component `K^0` is abelian, that is, a torus.  Let `FIN_k` be the set of tuples
whose generated subgroup is finite.  For `u` in `U(k)^4` and a set `A` of
tuples put

```text
dist(u, A) = inf_{v in A} max_i || u_i - v_i ||_op .
```

## Statement

Every constant below is independent of `k`, of the index of the abelian
subgroup, and of the group generated.

1. **(VA1) Density.**  `FIN_k` is dense in `VA_k` in operator norm.  In fact,
   if `K <= U(k)` is closed with `K^0` a torus, then `K` is the closure of an
   increasing union of finite subgroups `F_1 <= F_2 <= ...`.

2. **(VA2) Collapse.**  If `u` is in `VA_k` and `D(u) < 1/2`, then

   ```text
   M(u) <= D(u).
   ```

   The constant `1` is sharp.  Take `u_j = z`, a scalar, and `u_i = 1` for
   `i != j`.  Then `D(u) = M(u) = |z - 1|`.

3. **(VA3) Distance from the virtually abelian class.**  Every `u` in
   `U(k)^4` satisfies

   ```text
   dist(u, VA_k) = dist(u, FIN_k) >= min( (1/2 - D(u))/5 , (M(u) - D(u))/6 ).
   ```

4. **(VA4) Corona microstates.**  Let `rho : Hig -> U(Q)` be nontrivial, where
   `Q = prod_n M_(k_n) / (+)_n M_(k_n)` is a norm matrix corona.  Let
   `u^(n)` in `U(k_n)^4` be any unitary lifts of `rho(g_0),..,rho(g_3)` with
   `D(u^(n)) -> 0`.  Then

   ```text
   limsup_n dist(u^(n), VA_(k_n)) >= min(1/10, M_rho/6) = 1/10,
   ```

   where `M_rho = max_j ||rho(g_j) - 1||`.  The equality uses
   `M_rho >= 2 sin(2 pi/5) > 3/5`, from
   `one-small-higman-generator-collapses-the-four-cycle`.  Also:

   - Every homomorphism from `Hig` into a subgroup
     `prod_n K_n / {(x_n) : ||x_n - 1|| -> 0}` of `U(Q)` is trivial, where each
     `K_n <= U(k_n)` is a closed subgroup with abelian identity component.
   - The same holds for the corresponding ultraproducts.

5. **(VA5) Equivalent form of the open seed.**  The dimension-uniform collapse
   `(HMF5)` of `higman-four-cycle-intrinsic-mf-seed` holds if and only if the
   following holds:

   ```text
   (FA)  for every eta > 0 there is delta > 0 such that, for every k,
         every u in U(k)^4 with D(u) <= delta has dist(u, FIN_k) <= eta.
   ```

   The same equivalence holds with `VA_k` in place of `FIN_k`.

## What this kills (class obstruction)

**Invariant.** The identity component of the closure of the generated group,
seen robustly through the operator-norm distance to `VA_k`.

**Death step.** Density (VA1) moves a virtually abelian tuple to a
finite-image tuple.  Then the finite quotient in the Zassenhaus step of
`finite-image-higman-models-collapse-opnorm` finishes it, because `Hig` has
no finite quotient.  (VA3) makes the kill robust under perturbations of size
up to `(1/2 - D)/5`.

Excluded ansaetze.  None of these can produce a sequence contradicting
`(HMF5)`, and neither can anything within operator-norm distance `1/10` of
them along the sequence.

- **Monomial tuples, in any orthonormal basis and with arbitrary real phases.**
  This corrects the reading of `finite-image-higman-models-collapse-opnorm`
  and of the `(CGC)` bullet in `higman-exact-packet-cycles-collapse-opnorm`
  that a torus-regauge search "has to use phases that are not all roots of
  unity".  With monomial matchers `H_n` and diagonal regauges `W_j` from the
  joint commutant `{P_n,D_n}'`, the phases may be rational or irrational: the
  generated group lies in `U(1)^q x| S_q` and is virtually abelian, so (VA2)
  applies unchanged.
- **Tuples normalizing any maximal torus.**  This includes tuples that permute
  a decomposition of `C^k` into lines.
- **Clock-and-shift (generalized Clifford) tuples with any rotation angle.**
  This includes irrational angles.
- **Direct sums and tensor products of the above.**  Finite products of groups
  with abelian identity component again have abelian identity component.
- **Tuples inside any fixed compact group with abelian identity component,**
  in any unitary representation and any dimension.

So along any sequence contradicting `(HMF5)`, every tuple within `1/10` must
generate a group whose closure has a nonabelian identity component.  That is,
the closure contains a nontrivial compact connected semisimple subgroup.

**Census.**  `check_va_collapse.py` recomputes the stored Z/4 optima of
`higman-opnorm-collapse-is-a-one-unitary-z4-problem` in the tuple form
`U_i = S^i P S^(-i)`.  By (VA3) each is at operator-norm distance at least
`0.0434` from every virtually abelian tuple of the same dimension:

```text
chain64  N=64  D=0.282726  M=1.999494  dist_to_VA >= 0.043455
chain80  N=80  D=0.282938  M=1.999498  dist_to_VA >= 0.043412
chain96  N=96  D=0.280783  M=1.999501  dist_to_VA >= 0.043843
```

A random-restart descent over generic-phase monomial tuples, with `n <= 8`,
never went below the (VA2) margin `D - min(1/2, M) = 0`.  The value `0` is
attained at `n = 2` by a single nontrivial diagonal generator, which is the
sharpness example in (VA2).  This is a sanity check only, not part of the
proof.

## Next step that can fail on its own

Bound `D` below uniformly on tuples lying in compact `K <= U(k)` with
`dim [K^0,K^0] <= N`.  This is the approximate-tuple analogue of the adjoint
transfer in `thompson-v-gap-witnesses-need-unbounded-lie-closure`.

The obvious transfer runs as follows.

1. Pass to `K/K^0` using the finite-group theorem of Thom (arXiv:1005.0823,
   Theorem `main`, with the quotient length).
2. Push the tuple into `[K^0,K^0]`.
3. Apply the fixed-dimension gap to the adjoint tuple in `U(N)`.

Step 3 controls `||Ad(u_i) - 1||` only.  Passing from `||Ad(s) - 1||` small
back to `s` near the centre in `U(k)` costs a factor proportional to the
largest weight of the representation `K^0 -> U(k)`, which is unbounded (for
example `Sym^m` of `SU(2)`).  So bounded semisimple rank alone does not
obviously suffice, and the weight growth is where such a transfer dies or
must be paid.

## Remark on Thom's constant (not load-bearing here)

In the proof of Theorem `main` of arXiv:1005.0823 (source lines 386--392),
the displayed estimate uses `4 epsilon * l(a_(i+1))` for
`d([a_(i+1),a_i],[a_(i+1),a~_i])`.  But Lemma `comp` with
`d(a_i,a~_i) < 4 epsilon` gives `16 epsilon * l(a_(i+1))`.

- So the printed bound `9 epsilon` becomes `33 epsilon`.
- The argument then closes whenever `33 epsilon < 7/32`, that is for
  `epsilon < 7/1056`, rather than for all `epsilon < 1/64`.
- Corollary `corhig` uses `epsilon < 1/3000` and is unaffected.

The present node does not use Thom's theorem.  It uses the graph's
self-contained (FIC).
