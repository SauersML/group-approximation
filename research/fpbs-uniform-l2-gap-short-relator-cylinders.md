---
rg: 2
id: fpbs-uniform-l2-gap-short-relator-cylinders
kind: claim
title: Each one-relation cylinder of uniformly nonamenable marked groups has uniform l2 gap constants
distinct_from:
  fpbs-uniform-l2-gap-marked-groups: that asks for one uniform pair (M,delta) on all of X_(k,eta); this splits it into one independently falsifiable statement per relation w, and with the high-girth patch only the finitely many w shorter than L(eta) matter.
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
---

**OPEN.** Fix `k >= 2`, `eta in (0,1)` and a nontrivial freely reduced word
`w` in `F_k`. Let `Z_{k,eta,w}` be the set of `k`-marked groups
`(Gamma; s_1,...,s_k)` with `w = e` in `Gamma`, whose simple Cayley graph has
spectral radius at most `1 - eta`. The claim is that for every such
`(k,eta,w)` there are `M_w < infinity` and `delta_w > 0` with

```text
||T^G_{p_c(G) + delta_w}||_{2->2} <= M_w   for every G in Z_{k,eta,w}.
```

Section 4 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.

* Each `Z_{k,eta,w}` is a compact clopen piece of `X_{k,eta}`.
* Only the words with `|w| < L(eta)` are needed to recover the uniform
  conjecture, because `fpbs-high-girth-uniform-l2-patch` covers the rest.
* The pieces can be attacked or refuted separately. Representative pieces:
  - `w = s_1^2`: involutive generators;
  - `w = [s_1,s_2]`: commuting generators, as in `Gamma x Z` with mixed
    markings;
  - `w = s_1^n`: a torsion generator of small order.
* A counterexample on a single piece refutes the uniform conjecture for that
  `(k,eta)`. It does not refute the pointwise l2 conjecture: by
  `fpbs-l2-gap-baire-dichotomy` it gives a failure of uniformity, and a
  pointwise failure needs a nonempty kernel.

## Attempts

* **Transplant the known qualitative classes by compactness (2026-09-17).**
  Cover a cylinder by open neighbourhoods of groups already known to be in
  `C_2`, such as free products, hyperbolic groups and acylindrically
  hyperbolic groups, and take a finite subcover.

  **Where it dies:**
  - A finite subcover needs each point to have a neighbourhood inside *one*
    `U_{M,delta}`, not merely to lie in `C_2`.
  - The known gap theorems give constants that are not locally determined: for
    example, hyperbolicity constants are unbounded along convergent sequences.
    Section 4 of `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`
    records that their constants degenerate.
  - On the cylinder `w = [s_1,s_2]` the pieces contain markings of `Gamma x Z`.
    The factor-of-iid construction of Theorem 6 of
    `research/artifacts/fpbs/exploration.md` shows that nonamenability together
    with finite-cluster averaging does not control the operator there.
  - No piece is decided.
* **Calibrate the piece `w = s_k^2` at trees by free products with an amenable
  factor (swarm-0917-w11, 2026-09-17).**
  `fpbs-l2-threshold-not-lsc-at-trees` (ESTABLISHED) proves the following. For
  infinite amenable `A`, `Cay(A * Z/2)` has edge expansion at least `1/2` and
  `p_(2->2) <= p_c(A)`. The finite-by-`Z^m` approximants `A_R -> F_m` give
  groups `G_R` in `Z_(k,eta_k,s_k^2)`, with `eta_k = 1/(8(2k-1)^2)`, that
  converge to the tree `T_(2k-1)`. For `k = 3`:
  * `limsup p_(2->2)(G_R) <= 1/3 < 1/2 <= p_(2->2)(T_5)`;
  * `limsup slack(G_R) <= 1/12 < 1/4 <= slack(T_5)`.

  **What it gives.** In this piece the point `T_5` is interior to no
  `U_(M,delta)` with `delta > 1/12`. So any proof of this piece's
  `(M_w, delta_w)` must choose `delta_w <= 1/12` near `T_5`, and in general
  `delta_w <= 1/((2k-3)(2k-2))`. Such a proof cannot transplant the tree's own
  slack by ball agreement, and cannot use `rho` as the controlling datum,
  since `rho` jumps along the family for `k >= 4`.

  **Where it stops:** the slack of the family,
  `slack(G_R) <= p_c(A_R) - p_c(G_R)`, stays bounded away from `0`. The
  free-product theorem gives each `G_R` a gap. So the piece is not refuted.
  To refute it, one would need a family in the piece with `slack -> 0`, and
  free products with Z/2 cannot supply one.
* **Transfer to the relative susceptibility through towers of the kernel
  (swarm-0917-w19-w19-bs-follow, reframing, 2026-09-19).**
  `fpbs-l2-gap-transfers-to-kesten-normal-gap` (ESTABLISHED) proves the
  following. Let `N ◁ Gamma` be residually amenable in `Gamma`: a
  `Gamma`-normal tower `N_j <= N` with `N/N_j` amenable and `∩ N_j = {e}`,
  for example the derived series of a residually solvable `N`.
  - Then `Gamma/N_j -> Gamma`. Every `Gamma/N_j` keeps the quotient `Q`, and
    so has `rho <= rho_Q`.
  - On the approximants, Følner compression to the amenable kernel `N/N_j`
    gives `chi^(N/N_j) <= ||T||`.
  - Window agreement then carries any fixed `(M, delta)` bound on the
    approximants to `chi^N <= M` on `[0, p_c(Gamma) + delta]`.

  **What it gives for this node.**
  - *A necessary condition that can fail on its own.* If the piece
    `Z_(k,eta,w)` has constants `(M_w, delta_w)`, then every pair `(Gamma,N)`
    with `w = e` in `Gamma`, `N` residually amenable in `Gamma` and
    `rho_Q <= 1 - eta` has `chi^N <= M_w` at `p_c + delta_w`. Here `N` may be
    nonamenable, and `||T^Gamma||` gives no control of `chi^N`. So any proof
    of a piece must prove a uniform percolation Kesten law on that piece.
    That law is split off as `fpbs-uniform-kesten-law-residually-amenable-pairs`.
    A family of such pairs with vanishing margin refutes the piece.
  - *Calibration.* Outside the pieces, at girth at least `L(eta)`, the law
    holds with the constants of `fpbs-high-girth-uniform-l2-patch`. On `F_k`
    it is consistent with Grigorchuk's cogrowth formula.

  **Where it stops.** It is a reduction and a falsifier, not a proof. No
  pair with vanishing margin under fixed `eta` is known.
  `fpbs-kesten-margin-collapses-near-lamplighter` has `rho_Q -> 1`, so it
  does not qualify. No piece is decided.
