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
- **2026-09-18, swarm-0917-w11-w11-deligne-last1 (group-rings): tensor induction from the full multiplier torus of
  finite-index subgroups is killed, and the hole stays OPEN.** See
  `deligne-parameter-tori-corestrict-only-through-maslov-line`, ESTABLISHED.
  - *The idea.* Unlike additive induction (w8), tensor induction `TI` corestricts every multiplier class of a
    finite-index `H`, including the non-Maslov (Mess) directions of `H^2(H,R)`. The norm-model set `P(H)` is a closed
    subgroup of the torus `H^2(H,T)` and could contain subtori there. `TI` maps them into `P(Gamma)`.
  - *Proved.* Tensor induction realizes the transfer: `TI o res = [Gamma:H]`, and for normal `H`,
    `res o TI = sum_(G) g^*`. This is shown with exact twisted regular representations.
    - Consequence: `P_op = R/Z` iff `res[b] in Lie P(H)^0` iff (for normal `H`) `(Lie P(H)^0)^G != 0`.
    - On the finite branch, `TI` kills `P(H)^0`, `Lie P(H)^0` lies in the nontrivial `G`-isotypic part, and `TI`
      factors through the finite group `P(H)/P(H)^0`.
    - Exact (profinite) points corestrict into `{0, e(b/2)}` on the Maslov circle, by Mal'cev plus Deligne.
  - *Where it dies.*
    - Continuous families of norm models of `H` in any non-Maslov direction, moved by deformation, Hecke operators
      or tensor induction, die at "apply `tau = d TI`". The invariant is `W(H)^G`, which is nonzero only when the
      conclusion `P_op = R/Z` already holds.
    - Exactly realizable torsion points die at (T4).
  - *Survivor.* Tensor-inducing a `1/3` needs a class `y in P(H) \ (P(H)^0 + R(H))`. That is a class in a
    non-identity component of `P(H)`, with norm models, not in `P(H)^0 + R(H)`, and with `TI(y) = e(b/3)`. Only its
    component in the finite group `P(H)/P(H)^0` matters.
- **2026-09-18, swarm-0917-w12-w12-deligne-last1 (operator-algebras): comparison with bounded-level targets is
  killed as a class, and the w8 tensor-cube conditional is a tautology.** See
  `deligne-maslov-tensor-functors-are-asymptotically-regular`, ESTABLISHED. This hole stays OPEN.
  - *Invariant.* Push a `1/3`-model into the tracial ultraproduct. It becomes a trace on `A_omega`, and by
    `deligne-maslov-sector-traces-are-central-regular` it is central-regular. So `tr U_n(g) -> 0` at every
    non-central `g`, and the same holds for every tensor functor `U^(x a) (x) conj(U)^(x c) (x) R` with `a + c >= 1`
    and arbitrary `R`.
  - *Class killed.* Comparing any such functor with a trivial, scalar, finite-image or bounded-level target on a
    finite-index subgroup, whether by stability, rigidity or averaging. Every such argument dies when evaluated at a
    non-central element of the kernel: the functor has trace `0` there and the target has trace `1`, so the HS
    distance is `sqrt 2`. HS-stability versions die too.
  - *The w8 conditional.* "Every cube is `Q`-close to a finite-image hom" fails for every cube once one
    `1/3`-model exists. So the conditional's hypothesis is equivalent to `1/3 not in P_op`, which is the flagship.
  - *Survivor.* Only comparisons with unbounded-level targets whose characters are asymptotically regular remain.
    This is Dadarlat-type matricial stability, which is exactly where w8 found instability.
  - *Uniform side, conditional.* The route remark gives a level-free contradiction for uniform models. It needs a
    verbatim citation of `H^2_b(Lambda, R) = R [b]` for finite-index `Lambda < Sp_4(Z)` (non-cocompact
    Burger--Monod); only the cocompact JEMS 1999 abstract was verified. The remark does not reach point-norm
    models.
  - *Literature.* GLMR (arXiv:2301.00476) does not cover `Sp_4(Z)`. Its Prop 1.0.12 makes lattices in covers of
    Hermitian groups not uniformly `U(1)`-stable. BLSW needs every non-compact factor to have rank at least `3`.
- **2026-09-18, swarm-0917-w13-w13-deligne-last1 (host-geometry): most of the monomial survivor is closed
  uniformly in the Gamma-set, the rest is isolated, and the hole stays OPEN.** See
  `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`, ESTABLISHED.
  - *Duality (L1).* Operator-norm monomial `1/3`-models over an exact `Gamma`-set `X` are exactly almost-flat
    circle bundles on the Schreier complex `Y_X`. The optimal defect is `4/3` times
    `min ||f||_cell` over `f in kappa + 3 H^2(Y_X; Z)`, where `||.||_cell` is the `l^inf` quotient norm.
  - *Killed uniformly in `X`,* including changing stabilizers of unbounded index, which is the w8-last1
    survivor:
    - classes nonzero on spherical cycles (K1), with invariant `M_0`, the `pi_2` generation mass;
    - classes real-proportional to `kappa` (K2). The invariant is `D(Lambda) in {1,2}`, the order of `z` in
      `H_1(Lambda~)`, obtained from Deligne's `Res_fin = <z^2>`. This is the monomial analogue of the
      divisibility set `{+-1,+-2}` of w8, now with a defect floor `||kappa||_(cell,Y) / 6`.
  - *Block models.* Block-monomial models with block size prime to 3 reduce to monomial ones through `det` (K3).
  - *Where it dies.* At non-Kahler integral group classes `u in Hom(H_2(Lambda), Z)` with `u ≡ kappa` mod 3,
    such as Eisenstein and boundary classes of congruence subgroups, and at blocks of size divisible by 3. Neither
    invariant sees them.
  - *New prerequisite.* The residue is posed as
    `deligne-schreier-complexes-have-a-uniform-third-cellular-floor` (OPEN). It is *necessary* for the flagship:
    its failure gives `1/3 in P_op` through permutation-with-phase matrices. It is sufficient for the monomial
    part of this hole.
- **2026-09-20, swarm-0917-w22-w22-deligne-break (quantifier-shift): the uniform conditional is closed
  level-free, the uniform residue of w13 is empty, and the hole stays OPEN.**
  - *New lemmas (ESTABLISHED).*
    - `sp4-lattice-bounded-cohomology-is-the-kahler-line` (by citation): `H^2_b(Lambda;R) = R[b]` for every
      finite-index `Lambda <= Sp_4(Z)`. Sources: Monod, arXiv:0710.5361, Corollary 1.4 (no cocompactness
      hypothesis), and Burger--Monod GAFA 2002, proof of Corollary 24, Corollary 9 and Theorem 21. The Gromov norm
      `nu_b` is the same on every level, by an explicit transfer argument.
    - `deligne-uniform-scalar-models-have-a-level-free-third-floor`: uniform scalar `theta`-models on any
      finite-index `Lambda` have defect `>= 4 dist(theta, Z/2) nu_b`. Uniform monomial `1/3`-models over any finite
      `Gamma`-set have defect `>= min(1, (2/3) nu_b)`, and so do block-monomial ones with blocks of size prime to 3
      (with a `1/r` loss).
  - *What this closes.* The need in the route remark of `deligne-maslov-tensor-functors-are-asymptotically-regular-proof`,
    which asked for non-cocompact Burger--Monod.
  - *Class killed.* All uniform (all-pairs sup-defect) monomial and prime-to-3 block-monomial `1/3`-models,
    uniformly in the stabilizer index.
    - *Invariant:* `dim H^2_b(Lambda) = 1` together with the divisibility set `{1, 2}`.
    - *Where every member dies:* the rounded error `s` is a bounded cocycle, so `[s] = mu [b]` with
      `|mu| >= 1/6`.
  - *Diagnosis of the point-norm residue.* The non-Kahler classes `u = kappa mod 3` left by w13 are exactly the
    classes outside `image(H^2_b -> H^2) = R kappa`. They can occur only when the error cocycle is small on a
    finite window but not bounded-small on all pairs. So the survivor of this hole lives in the gap between the
    cellular finite-window norm and the bar sup norm, and in blocks of size divisible by 3.
  - *Reduction posed, not proved (uniform full models).*
    - *Claim.* `E_3` has no uniform `1/3`-model of small defect, of any shape.
    - *Proposed argument (BOT, Burger--Ozawa--Thom, Section 5).*
      1. Lift the Siegel radical `N = Sym_2(Z)` to an abelian `N_0 <= E_3`.
      2. By Kazhdan's theorem for amenable groups, `pi|N_0` is uniformly close to a representation.
      3. Show `pi` is close to `I` on `qN_0` for some `q`, via Levi invariance and rationality of finite
         `SL_2(Z)`-orbits on the dual torus `T^3`.
      4. The normal closure `E(q)` has finite index, so it contains `z` by Deligne, and `pi(z) = omega` would then
         be close to `I`.
    - *Named prerequisite (BG).* The normal closure of `qN` in `Sp_4(Z)` must be a product of at most `R`
      conjugates of elements of `qN`, with `R` independent of `q`. This is the `Sp_4` analogue of
      Carter--Keller--Paige/Morris for `SL_n`, `n >= 3`. No verbatim source was found; Tavgen and Trost are
      candidates.
    - *Scope.* Steps 1 to 3 have not been checked beyond a sketch. Even if all of this holds, it reaches only
      uniform models, not point-norm ones.
