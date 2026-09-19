---
rg: 2
id: popa-vanishing-cohomology-amplification-and-ce-imports
kind: claim
title: Popa's vanishing-cohomology package - amplified Bernoulli cocycles of groups with an infinite relative (T) subgroup are not weak coboundaries in U(R), and CE of R x| Gamma is a lifting problem into the normalizer of R in R^omega
distinct_from:
  stw99-problem-lvi-untwisting-cocycle-actions: that records Popa's positive VC theorem for amenable groups; this imports the negative side (Theorem 3.2, Corollary 3.3), the amplification construction and the Section 6 reformulation of Connes embeddability.
  finitary-extension-ce-iff-action-lifts-to-normalizer: that is an in-repo proof of the lifting criterion for genuine actions; this is the literature source for the same criterion (Theorem 6.3) together with the non-untwistable amplified Bernoulli cocycles.
  popa-bernoulli-cocycle-superrigidity: that is Popa's 2007 cocycle superrigidity for measurable 1-cocycles of Bernoulli actions; this concerns U(N)-valued 2-cocycles of cocycle actions on II_1 factors (arXiv:1802.09964).
---

**ESTABLISHED by citation** (route `popa-vanishing-cohomology-amplification-and-ce-imports-citation`).
Source: S. Popa, *On the vanishing cohomology problem for cocycle actions of groups on II_1 factors*,
arXiv:1802.09964. The route quotes every item verbatim.

**Conventions (Section 1).**
- A cocycle action `(sigma, v)` of `Gamma` on a II_1 factor `N` satisfies `sigma_g sigma_h = Ad(v_(g,h)) sigma_(gh)`
  and the 2-cocycle identity. It is **free** if every `sigma_g`, `g != e`, is outer. Freeness is equivalent to
  `N' ∩ (N x|_(sigma,v) Gamma) = C1`.
- In the crossed product the canonical unitaries satisfy `U_g U_h = v_(g,h) U_(gh)`. The trace is `tau(sum U_h x_h) = tau_N(x_e)`.
- `v` **vanishes** if `v = dw` for some `w : Gamma -> U(N)`. It **weakly vanishes** if this holds modulo scalars.
  Equivalently, some `w_g U_g` form a genuine (respectively projective) representation of `Gamma`.
- `VC_w(N)` is the class of groups all of whose free cocycle actions on `N` have weakly vanishing cocycle.

**Amplification (Definition 3.1).**
- Take a free action `sigma` of `Gamma` on `N`, a projection `p` of trace `t`, and partial isometries `w_g` from
  `sigma_g(p)` to `p` (with `w_e = p`).
- Then `sigma^p_g = w_g sigma_g(.) w_g^*` is a free cocycle action on `pNp` with cocycle
  `v^p_(g,h) = w_g sigma_g(w_h) w_(gh)^*`.
- Up to cocycle conjugacy it depends only on `t`.

**(P1) Non-vanishing (Theorem 3.2, Corollary 3.3).**
- Take `sigma` to be the noncommutative Bernoulli action of `Gamma` on `R = R_0^(⊗Gamma)`, with `R_0 ≅ R` and
  `0 < t < 1`.
- If `Gamma` contains an infinite subgroup with the relative property (T), or an infinite subgroup with non-amenable
  centralizer, then the cocycle `v^t` is **not weak-vanishing**.
- Hence `Gamma ∉ VC_w(R)`.

**(P2) Normalizer and Theorem 6.3.**
- Every automorphism of `R` is `Ad(U)|_R` for some `U` in the normalizer `N_(R^omega)(R)`. Such a `U` is unique up to
  `U(R' ∩ R^omega)`.
- For a free action `sigma` of `Gamma` on `R`, `R x|_sigma Gamma` is Connes embeddable iff there are
  `U_g in N_(R^omega)(R)` implementing `sigma` with `U_g U_h = U_(gh)`.
- The proof of Theorem 6.3 uses the fact that any two copies of `R` in `R^omega` are unitarily conjugate.

**(P3) Wreath products (Remark 6.5.1).**
- Popa's source for this is [HaS16]: if `H` and `Gamma` are sofic, then `H wr Gamma` is sofic, hence CAE.
- For an amenable ICC `H`, one has `L(H) ≅ R`, and the Bernoulli crossed product `R x|_sigma Gamma = L(H wr Gamma)`
  is CAE.

**(P4) Groups versus factors (Definition 6.2).** A group is CAE (hyperlinear) iff `L(Gamma)` embeds into `R^omega`,
which is [R06].

**(P5) Cocycle conjugacy (Proposition in 1.2).** A `*`-isomorphism `N_1 x| Gamma_1 ≅ N_2 x| Gamma_2` carrying `N_1`
onto `N_2` yields a cocycle conjugacy up to a group isomorphism. Conversely, a cocycle conjugacy extends to an
isomorphism of the crossed-product inclusions.
