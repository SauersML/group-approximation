---
rg: 2
id: deligne-finite-parameter-group-has-period-prime-to-three
kind: claim
title: If Deligne's norm-parameter group is finite then its order is prime to three
distinct_from:
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that asserts 1/3 is not in P_op outright; this asserts it only on the finite branch, so it says nothing when P_op = R/Z and is strictly weaker.
  deligne-sep7-norm-parameter-closed-subgroup: that proves P_op is R/Z or (1/m)Z/Z with m even; this asks for the residue of m at the prime three on the finite branch.
  sp4-quasirep-windings-are-sublinear: that would exclude the branch P_op = R/Z; this is about the complementary finite branch and is independent of windings.
---

**OPEN.** Let `P_op` be the norm-parameter group of `deligne-sep7-norm-parameter-closed-subgroup`. The claim is:

```text
if P_op = (1/m)Z/Z for some even m, then 3 does not divide m.
```

Equivalently, `1/3 in P_op` implies `P_op = R/Z`. In words: an operator-norm `1/3`-model of the Maslov cocycle
already forces arbitrarily small parameters.

**Why it matters.** Together with `sp4-quasirep-windings-are-sublinear`, it gives the flagship
`deligne-triple-cover-exact-mf-radical`, through route `deligne-triple-cover-via-sublinear-windings`. It is the
arithmetic half of that split, and it involves no winding estimate.

**How it can fail.** An MF model of `E_3` (a `1/3`-model) whose parameter group is still finite, for example
`P_op = (1/6)Z/Z`. Such a model would make `E_6` MF while `E_q` is not MF for every `q` not dividing `6`.

## Attempts
- **2026-09-18, swarm-0917-w7-w7-deligne-break: posed.** No test has been run. The tensor-power amplification of
  `deligne-sep8-first-order-tensor-threshold` needs `o(|t|)` errors with `t -> 0`. It does not start from one fixed
  parameter `1/3` with nonzero error, so it gives no leverage here.
- **2026-09-18, swarm-0917-w8-w8-deligne-last1 (cohomology-index): virtual descent is killed as a class, and the
  hole stays OPEN.** See `deligne-parameter-group-is-a-virtual-invariant`, ESTABLISHED.
  - *Finite-index invariance.* `P_op` is the same on every finite-index `Gamma'`. Twisted induction preserves the
    operator-norm defect blockwise.
  - *Divisibility.* If `[b|Gamma'] = n[beta] + tors`, then `P(Gamma',beta) = n P_op`. By Deligne, `n` is always
    in `{+-1, +-2}`, and `n = 2` is attained.
    - A virtual division by an odd prime or by `4` would make the matching `E_q` a finite-index extension of a
      fibre product `Gamma' x_(Z/s) F`, hence residually finite.
  - *What dies.* An attempt to get `1/9`, or any parameter outside `(1/6)Z/Z`, from a `1/3`-model dies at "divide
    by `3` on a finite-index subgroup". The attempt may use tensor products, sums, rephasing, automorphisms,
    restriction, induction and virtual division. The hypothetical `P_op = (1/6)Z/Z` is closed under all of them.
    The invariant is the virtual divisibility set `{+-1, +-2}` of the Maslov class.
  - *Remaining algebraic loophole.* Block-monomial models have genuine finite `Gamma`-sets as block patterns (V6).
    What (V5) does not cover is sequences whose stabilizers change along the sequence, with index going to
    infinity. Apart from that, a proof of this hole needs analytic input about operator-norm approximation, beyond
    virtual cohomology.
  - *Side observations (not proved in a node).*
    - Suppose some relator `r` has `3 not | k`. Then a `1/3`-model in dimension `d` with `3 not | d` has defect at
      least of order `1/d` on `W_r`, since `det W_r = 1` while `omega^(kd) != 1`. So the dimensions of a norm
      model must eventually be divisible by `3`, or tend to infinity.
    - Property (T) of `E_infinity` gives a uniform spectral gap for representations with `zeta != 1`, but it yields
      no contradiction with a `1/3`-model.
- **2026-09-18, swarm-0917-w8-w8-deligne-follow (stability-approximation): the tensor-cube reduction dies at
  matricial instability of `Gamma`, and the hole stays OPEN.** Let `U : E_infinity -> U(Q)` be a `1/3`-model,
  with lifts `U_n` in dimension `d`. Put `V = U (x) U (x) U`.
  - *The cube is untwisted.* Since `c_(1/3)^3 = c_1 = 1`, `V` is an honest hom `Gamma -> U(Q')` with defect at most
    `3 eps`, where `Q' = prod M_(d^3) / (+)`.
  - *Virtual triviality of the cube is impossible (short proof).* Suppose `V|Lambda = 1` in `Q'` for some finite-index
    `Lambda`. An eigenvalue argument (`a_i a_j a_l ~ 1` for all `i, j, l` forces `a_i ~ a_j` and `a_i^3 ~ 1`) makes
    `U_n(g) ~ lambda_n(g) I` with `lambda_n(g)` near `mu_3`. A diagonal subsequence then gives an exact
    `lambda : Lambda -> mu_3` with `delta lambda = omega^b` on `Lambda`. So `E_3` is virtually `Lambda x C_3`, which
    is residually finite, contradicting Deligne. The same holds if `V` is only `Q'`-close to a hom with finite image.
  - *Consequence.* Suppose every honest hom `Gamma -> U(Q)` were `Q`-close to one with finite image, or merely every
    tensor cube. Then `1/3 not in P_op`, which is the whole flagship and not just this hole.
  - *Where it dies.* That stability fails. By `dadarlat-linear-groups-have-nonzero-h2-windings`, `Gamma` has
    asymptotic homs with nonzero `H_2` windings, and these are far from all honest representations. The cube carries
    no extra constraint that would rule this out. Its winding on a relator `r` is `kappa_r(V) = d^2 (3j - k d)` for
    some integer `j`: eigenvalues of the relator word are `omega^k e^(i psi_a)`, `det = 1`, and
    `kappa_r(V) = 3 d^2 sum(psi)/(2 pi)`. After `U -> U (+) U (+) U` gives `3 | d`, this congruence allows
    `kappa_r(V) = 0`.
  - *Class killed.* Arguments that pass through the untwisted cube (or `U (x) U-bar`) and use only its winding or
    congruence data. What survives is stability restricted to cubes, which is as hard as the flagship.
