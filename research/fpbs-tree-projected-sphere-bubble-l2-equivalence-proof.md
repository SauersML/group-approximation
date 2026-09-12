---
rg: 2
id: fpbs-tree-projected-sphere-bubble-l2-equivalence-proof
kind: route
title: Submultiplicative sphere bubbles through cut fibres feed the two-estimate criterion
target: fpbs-tree-projected-sphere-bubble-l2-equivalence
requires:
  - fpbs-relative-susceptibility-tube-excursion-bound
  - fpbs-hyperbolic-quotient-fibre-estimates-l2-gap
  - fpbs-fibre-summed-connectivity-operator
  - fpbs-tree-projected-branch-share-last-crossing-bound
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Theorem 4.3 of the artifact. Steps (⇐3) and (⇐5) fill the two gaps
`major-reviewer` found (`research/artifacts/review-major-swarm-2026-09-12.md`,
§9e).

**Notation.**
* `B` is the free basis, `m_s = #{g in S : pi(g) = s}` and `M = max_s m_s`.
* `S(j)` is the sphere of radius `j` in `F_n`, so `|S(j)| <= 2n(2n-1)^(j-1)` for
  `j >= 1`.
* `beta(w)` is the set of reduced words beginning with `w`.
* Values at `p_c` are left limits.

* **(⇒)** If `p_c < p_{2->2}` then `T_(p_c)` is bounded. Since `H` is amenable,
  `fpbs-fibre-summed-connectivity-operator` gives
  `sum_R b_R(p_c) = ||S_(p_c) delta_1||^2 <= ||T_(p_c)||^2`. So `b_R(p_c) -> 0`.
* **(⇐)** Suppose `b_(R_0)(p_c) = 1 - eta` with `eta > 0`.
  1. **Below `p_c`.** Each `sigma_p(q)` is nondecreasing and left-continuous in
     `p`, and `b_(R_0)` is a finite sum. So `b_(R_0)(p) <= 1-eta` for all `p < p_c`.
  2. **Fibre susceptibility.** The tube excursion bound with `r = R_0-1` gives,
     for `p < p_c`,
     `chi^H_p <= C_(R_0-1)(p) + b_(R_0)(p) <= C_(R_0-1)(p_c) + 1 =: c`, and
     `c < infinity` because `C_r(p) < infinity` for every `p < 1`.
  3. **Small radii are bounded (gap 1).** Item 4 of
     `fpbs-tree-projected-branch-share-last-crossing-bound` gives
     `sigma_p(w) <= chi^H_p prod_(j<=|w|) lambda_p(s_j)`, with
     `lambda_p(s) = p m_s chi^(s)_p`.
     * `X^(s)` is a subgraph of `X` containing `o` and `Gamma_1`, so its cluster
       of `o` lies in `K_o`, and `chi^(s)_p <= chi^H_p <= c`.
     * Hence `sigma_p(w) <= c (M c)^(|w|)`.
     * For every `j < R_0` and `p < p_c`, therefore,
       `b_j(p) <= |S(j)| c^2 (M c)^(2j)`.
     * Put `K = sum_(j<R_0) |S(j)| c^2 (Mc)^(2j) < infinity`.
  4. **Uniform fibre bubble, premise (i).**
     * *Submultiplicativity.* Every path from `o` to `Gamma_(wu)`, for a reduced
       product `wu`, enters the cut fibre `Gamma_w`. BK at the first visit and
       translation give `sigma_p(wu) <= sigma_p(w) sigma_p(u)`, hence
       `b_(R+R') <= b_R b_(R')`.
     * *Geometric decay.* For `R = k R_0 + j` with `0 <= j < R_0`,
       `b_R(p) <= (1-eta)^k b_j(p)`.
     * *Conclusion.* `sum_R b_R(p) <= K/eta` uniformly in `p < p_c`.
  5. **Far halfspaces, premise (ii) (gap 2).** Let `Phi : F_n -> H^d` be the
     rough similarity of `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`, with
     `|d(Phi x, Phi y) - lambda d(x,y)| <= C_0`. Fix `a in F_n` and a halfspace
     `H` with `d(Phi(a), H) >= D` and `Phi^(-1)(H)` nonempty; otherwise the share
     is 0.
     * **(a) Obtuse projection.** Let `z` be the nearest-point projection of
       `Phi(a)` onto the closed convex set `H`. For `x in H`, the triangle
       `(Phi(a), z, x)` has angle at least `pi/2` at `z`.
       * *Law of cosines.* `cosh d(Phi(a),x) >= cosh d(Phi(a),z) cosh d(z,x) >= e^(d(Phi(a),z)+d(z,x))/4`,
         so the Gromov product `(Phi(a)|x)_z <= log 2`.
       * *Thin triangles.* The geodesic `[Phi(a), x]` passes within
         `c_0 = log 2 + 4 delta` of `z`, where `delta` is the hyperbolicity
         constant of `H^d`.
     * **(b) Morse lemma.** For `q in Phi^(-1)(H)`, the image of the tree
       geodesic `[a,q]` under `Phi` is a quasi-geodesic with constants depending
       only on `(lambda, C_0)`. So it lies within some `R_1 = R_1(lambda, C_0, d)`
       of `[Phi(a), Phi(q)]`, and some vertex `r` of `[a,q]` has
       `d(Phi(r), z) <= R_1 + c_0`.
     * **(c) One fixed ball.** Apply (b) to one fixed `q_0` and get `r_0`. For any
       other `q`, its vertex `r` has `d(Phi(r), Phi(r_0)) <= 2(R_1 + c_0)`, so
       `d(r, r_0) <= R := (2(R_1+c_0) + C_0)/lambda`. So every geodesic `[a,q]`
       meets `B(r_0, R)`, and
       `Phi^(-1)(H) ⊆ union_(r in B(r_0,R)) {q : r in [a,q]}`. That is at most
       `N_R = |B_(F_n)(R)|` branches, independent of `D`.
     * **(d) Depth.** `d(Phi(a), Phi(r_0)) >= D - R_1 - c_0`, so every
       `r in B(r_0,R)` has `d(a,r) >= D/lambda - C'` with
       `C' = (R_1 + c_0 + C_0)/lambda + R`.
     * **(e) Share.**
       * *Translation.* Left translation by `a^(-1)` maps
         `{q : r in [a,q]}` onto `beta(w)` with `w = a^(-1) r` reduced and
         `|w| = d(a,r)`.
       * *BK through the cut fibre.* For `|w| >= 1` every path from `o` into
         `pi^(-1) beta(w)` enters through `Gamma_w`, so
         `sum_(q' in beta(w)) sigma_p(q') = E_p|K_o ∩ pi^(-1)beta(w)| <= sigma_p(w) chi_p`.
       * *Bound.* For `D/lambda - C' >= 1`:
         `sh(D) <= N_R sup_(p<p_c) max_(|w| >= D/lambda - C') sigma_p(w)`.
       * *Decay.* `sigma_p(w)^2 <= b_(|w|)(p) <= (1-eta)^(floor(|w|/R_0)) K`
         uniformly in `p < p_c`. Hence `sh(D) -> 0`.
  6. `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`, with premises (i) and
     (ii), gives `p_c < p_{2->2}`.
