---
rg: 2
id: fpbs-amenable-wq-normal-relative-subcriticality
kind: claim
title: Slightly supercritical clusters meet an amenable wq-normal subgroup with finite mean
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for l2-boundedness of the whole critical connectivity operator; this asks only that the two-point function be summable along one amenable wq-normal subgroup at some parameter above p_c, which by fpbs-bs-iff-finite-relative-susceptibility is equivalent to the threshold gap for that group.
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
  - research/artifacts/fpbs/docs/ps-averaged-tilt-relative-susceptibility.md
---

**OPEN.** For every nonamenable finitely generated group `Gamma` having an
infinite amenable wq-normal subgroup `H`, and every finite symmetric generating
set `S`, there is `p > p_c(Cay(Gamma,S))` with

```text
E_p|K_o ∩ H| = sum_{h in H} P_p(o <-> h) < infinity.
```

By `fpbs-bs-iff-finite-relative-susceptibility` this is equivalent, group by
group, to `p_c < p_u` on every Cayley graph of `Gamma`.

## Attempts

* **Count open walks (Section 4.1 of the artifact).** For `H` normal,
  `E_p|K_o ∩ H| <= sum_l (p d)^l q_l(e,e)`, with `q_l` the return probability
  of the random walk projected to `Gamma/H`, which is at most `rho(Gamma/H)^l`.
  **Where it dies:** Kesten gives `rho(Gamma/H) = rho(Gamma)` for amenable `H`,
  so the bound is finite exactly when `p d rho < 1`. That is the classical
  Benjamini--Schramm bound `p_u >= 1/(d rho)`, and it certifies no new graph.
* **Mean-field comparison (Section 4.2).** For critical branching random walk
  the summed occupation of `H` is `sum_l q_l(e,e) <= 1/(1-rho) < infinity`,
  since the quotient is nonamenable. So mean field predicts that the relative
  susceptibility stays finite at `p_c`. **Where it dies:** the comparison needs
  a triangle-condition-type input that is itself open.
* **Hutchcroft's halfspace criterion (Section 4.3).** On a long segment of a
  central `H`, the isoperimetric ratio in Hutchcroft's Proposition 2.7 tends to
  `chi^H_p / chi_p`, so that criterion asks for `chi^H_p = o(chi_p)` on these
  sets. It meets the same quantity rather than supplying it. Choi--Seo Section
  2.3 shows that the halfspace hypothesis fails on these sets for `F_2 x Z`.
  **Where it dies:** the WPD remedy needs acylindricity, which fails for groups
  with an infinite amenable normal subgroup.
* **Openness from criticality (Section 4.4).** If the set of `p` with finite
  relative susceptibility were open, finiteness at `p_c` would suffice. The
  sprinkling bound of arXiv:1804.10191 Lemma 2.4 controls the `(o,H)` row only
  through a quadratic sum over cosets. That sum is bounded by an l2 bound on the
  coset operator, not by `chi^H_p`. **Where it dies:** positive definiteness gives
  `sigma_p(u) <= chi^H_p` pointwise, but the coset sum still needs an
  L2-boundedness-type input.
* **Dangling-bridge pivotals (Section 5).**
  `fpbs-uniqueness-pivotals-are-dangling-bridges` bounds pivotal counts under
  uniqueness by quantities independent of distance. **Where it dies:**
  conditioning on connection costs `theta^(-2)`, and the Russo integral is not
  integrable at `p_c` under mean-field behaviour.
* **Patterson--Sullivan averaged tilt (`ps-averaged-tilt-relative-susceptibility.md`).**
  For normal `H` with hyperbolic `Q = Gamma/H`, tilting Hutchcroft's
  nonunimodular argument (arXiv:1711.02590) by the Radon--Nikodym cocycle of a
  quasi-invariant measure `nu` on `dQ` gives an exact mass-transport principle
  and a symmetric convex averaged susceptibility
  `chi^nu_(p,1/2) = sum_q sigma_p(q) int (d(q_* nu)/d nu)^(1/2) d nu`, with
  `E_p|K_o ∩ H| <= chi^nu_(p,1/2) <= chi_p`. So `p_c < p_t^nu` already gives this
  claim, and on `F_2` exact layers and left-continuity also transfer.
  **Where it dies:** three source steps need a supremum over directions or a
  positive orbit mass: sprinkling (the supremum is L2-strength by a Schur test,
  and any multiplicative closure is at least `||S_p||` by Kesten), the tilted
  Aizenman--Barsky BK step (orbits are `nu`-null), and the best-versus-worst
  comparison. A kernel satisfying the Harris--FKG distortion bounds has finite
  average and infinite supremum, and on `X_rig` nothing forces a radial profile.
* **Calibration: critical finiteness plus openness, tested on Z^d (2026-09-17,
  `research/artifacts/fpbs-lattice-critical-relative-finiteness-2026-09-17.md`).**
  * **World.** `fpbs-lattice-amenable-subgroup-critical-finiteness-no-gap`: on
    nearest-neighbour `Z^d` with `d >= 11`, along `H = Z^k` with codimension
    `m >= 3`, three things hold:
    * the critical fibre profile satisfies
      `sigma_(p_c)(q) <= C(1+|q|)^(-(m-2))`, so `chi^H_(p_c) < infinity`;
    * `sigma_(p_c)` is in `l^r` for `r > m/(m-2)` (square summable when `m >= 5`);
    * `chi^H_p = infinity` for every `p > p_c`.
  * **What it kills.**
    * The Section 4.2 prediction holds with `rho(Q) = 1`. It measures
      transience of the quotient, not nonamenability, so verifying it is no
      evidence for the gap.
    * Any route to openness (Section 4.4) that uses only critical finiteness,
      `l^r` or bubble bounds on the fibre profile, or mean-field two-point
      exponents dies in W1.
  * **Where it dies.** At the passage from `p_c` to some `p > p_c`: W1 has all
    these inputs and no gap. The only separating input in sight is the operator
    norm of convolution by `sigma_(p_c)` on `l^2(Q)`, which is infinite in W1.
    This is consistent with the Kesten barrier and the square-root-law
    equivalence already recorded.
* **Spectral DT certificates (`research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md`).**
  Replace the DT mass `phi_p(S)` by the spectral radius of the boundary measure
  `nu_{S,p}` acting on the Schreier space `l2(H\Gamma)`.
  * A value below 1 bounds `E_p|K_o ∩ H|` by a Neumann series, and the condition
    is open in `p`
    (`fpbs-quotient-spectral-dt-certificates-are-subgroup-blind`). So the
    openness death of Attempt 4.4 is bypassed, and the target follows from
    `fpbs-wq-normal-class-critical-spectral-dt-certificate`, via
    `fpbs-wq-normal-subcriticality-via-spectral-certificate`.
  * **Where the relative leverage dies:** Proposition C proves
    `sp_Gamma(nu) <= sp_{H\Gamma}(nu)` for every subgroup, with equality for
    amenable `H`. The quotient never helps, and any certificate also gives
    `||T_p|| < infinity`
    (`fpbs-spectral-dt-certificate-bounds-connectivity-operator`). This is the
    Kesten coincidence of "count open walks" (the level `S = {o}`), shown to
    hold at every level `S`.
  * The remaining premise is a critical finite-volume L2-type estimate. It
    holds on the tree with `S = B_3`, and has not been checked on any group of
    the class.
* **Is this hole weaker than critical L2? Power improvement plus square-root law
  (2026-09-17, `research/artifacts/fpbs-fibre-power-improvement-2026-09-17.md`).**
  * **General tool.** `fpbs-normal-coset-fibre-mass-power-improvement`, for every
    normal `N` below `p_c(N;G)`:
    * every coset moment is at most the subgroup moment;
    * hence `sigma_p(q) <= C_r P_p(o <-> Gamma_q)^(1-1/r)`;
    * Grimmett's thinning then gives `sigma_p <= C sigma_(p')^s` with
      `s < log p/log p'`.
  * **On tree-projected graphs.** `fpbs-tree-projected-pu-l2-iff-square-root-law`
    shows that `p_{2->2} = p_u` (Question Q of the fibre-mass artifact §5.2) is
    equivalent to the non-strict square-root law
    `sum_q P_p(o <-> Gamma_q)^(2+eps) < infinity` below `p_u`. Unconditionally,
    `p_{2->2} >= sup_(p'<p_u) (p')^(max(r*(p'),2)/2)`.
  * **Consequence.** Wherever the square-root law holds, this hole is equivalent
    to critical L2 graph by graph. On tree-projected graphs no weaker target
    exists unless `fpbs-tree-projected-square-root-fibre-law-below-pu` fails.
  * **Where it stops.** That law is Hutchcroft--Pan's backscattering
    `beta* >= 1/2`. With a central kernel, pairs keep their separation exactly.
    But one child per fibre loses the height spread (`max_h` versus `sum_h`), and
    rigid decorations give no symmetric separation walk for Kesten's bound. The
    missing input is a flat pair lemma, recorded in that node.
