---
rg: 2
id: thompson-t-triangle-genuine-rep-relator-gap
kind: claim
title: "Relator gap on honest representations of the triangle group: there is c > 0 such that every nontrivial finite-dimensional unitary representation rho of Delta(4,3,5) has max(||rho(r_1) - 1||, ||rho(r_2) - 1||) >= c"
distinct_from:
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that gap ranges over all exact pairs of Z/4 * Z/3 and includes the pentagon defect; this ranges only over honest representations of the linear group Delta(4,3,5), where the pentagon is exact, and is strictly weaker (gamma_n >= delta_n, with gamma_2 = 0.618 > delta_1 = 0.518).
  thompson-t-pentagon-winding-rigidity: that is an integer-valued condition on near pairs of Z/4 * Z/3; genuine Delta-representations have kappa_P = 0 identically, so this gap is invisible to that invariant.
  simple-kazhdan-mf-lives-in-gap-near-representations: that lives on near-representations far from genuine ones of a group with no genuine ones; this is a statement only about genuine representations, of the residually finite cover Delta.
---

**OPEN.** This is condition (R_Delta) of `thompson-t-not-mf-iff-triangle-gap-and-rounding`.

With `Delta = <a, b | a^4, b^3, (ba)^5>` and the Lochak--Schneps words `r_1 = [bab, a^2 bab a^2]` and
`r_2 = [bab, a^2 b^2 a^2 bab a^2 b a^2]`, the claim is:

```text
inf_n gamma_n > 0,     gamma_n = min { max_i ||rho(r_i) - 1|| : rho : Delta -> U(n) nontrivial }.
```

## What is known

- **It is necessary.** Its failure makes `T` MF (item 2 of the equivalence claim).
- **Each dimension is gapped.** Each `gamma_n` is attained and positive.
- **Irreducible form.** Only irreducible representations matter.
- **Small dimensions.** `gamma_1 = infinity`, since `Delta` is perfect, and `gamma_2 = (sqrt 5 - 1)/2`.
- **A reformulation.** Equivalently, no sequence of finite-dimensional unitary representations of `Delta`
  converges in the norm corona to a nontrivial representation that factors through `T`.
  - Honest representations of `Delta` are plentiful. `Delta` is linear and residually finite.
  - So the claim asks whether the normal closure of `{r_1, r_2}` can be almost killed in operator norm,
    uniformly, by honest representations.

## How it fails

The claim is refuted by nontrivial representations `rho_j` of `Delta` with `max_i ||rho_j(r_i) - 1|| -> 0`.
Such a sequence would be an MF model of `T` built from honest representations of the Fuchsian group. For
example, it could come from finite quotients `Delta ->> Q_j` in which `r_1, r_2` act almost trivially in
some faithful unitary representation.

## Attempts

- **2026-09-19 (swarm-0917-w17-w17-ptl-follow).** Node created. `gamma_2` was computed exactly: both
  2-dimensional representations factor through the binary icosahedral group, and `r_1 = 1` in both. In the
  witness to `gamma_2`, `r_2` has trace `(1+sqrt 5)/2`, so it has order 10. No lower bound uniform in `n` is known. Possible tools are the
  following.
  - *Largeness.* Use that `T` is simple and not residually finite, so that `r_1, r_2` normally generate a
    subgroup whose quotient has no finite-dimensional representations.
  - *Character varieties.* Compactness of the `U(n)` character varieties of `Delta`, together with
    some quantitative Malcev statement.

  A quantitative Malcev theorem of the needed kind would itself be a form of this claim, so neither tool
  closes it.

- **2026-09-19 (swarm-0917-w19-w19-ptl-follow).** Exact decomposition, plus a kill of the
  finite-quotient mode. The node stays OPEN.
  - *Decomposition.* By `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`, item 2, this claim
    is equivalent to three uniform gaps, one per classical family:
    - `thompson-t-triangle-gap-on-dense-projective-unitary-images`;
    - `thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images`;
    - `thompson-t-triangle-gap-on-dense-symplectic-adjoint-images`.

    Each concerns homomorphisms of `Delta` with **dense** image in one classical adjoint group, and
    the route is `thompson-t-triangle-gap-via-classical-adjoint-trichotomy`. It is an instance of the
    new engine `lie-closure-trichotomy-without-finite-quotients`, which needs only three inputs: the
    positivity of `gamma_n`, the fact that `T` has no finite quotients, and `gamma_1 = infinity`.
  - *The suggested failure mode is dead.* The "How it fails" paragraph above proposes finite quotients
    `Delta ->> Q_j`. By item 5 of that claim, every nontrivial representation through any finite
    quotient has `d_T >= 1/2`. The same bound, or better, kills two further classes:
    - induced representations from surface subgroups, at `sqrt 2`;
    - all pullbacks from one fixed compact group, such as `Sym^m` over a dense `Delta -> SO(3)`, at
      `min(1/2, gamma_3/2)`.

    The invariant is `N = dim [l, l]` of the image closure, and the death step is `delta_N`.
  - *Comparison.* Each Delta-level gap follows from the matching gap over `Z/4 * Z/3`, with the same
    constant.
  - *Not done.* No uniform bound for dense images with rank tending to infinity has been proved.
