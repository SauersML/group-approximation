---
rg: 2
id: cubic-division-congruence-representations-converge-strongly
kind: claim
title: The prime-level congruence representations of SL_1(O_D), D a cubic division algebra, converge strongly to the regular representation
distinct_from:
  cubic-division-lattice-purely-matricial-field: that asks for ANY sequence of finite-dimensional representations of Gamma_D; this fixes the canonical one, the mean-zero regular representations of the prime congruence quotients.
---

OPEN.  Let `D` be a central division algebra of degree 3 over `Q`, `O_D` a
maximal order and `Gamma_D = SL_1(O_D)`.  For all primes `p` outside a finite
set `P_D`, `O_D/pO_D = M_3(F_p)` and reduction `Gamma_D -> SL_3(F_p)` is onto
(strong approximation).  Put

```text
pi_p = l^2_0(SL_3(F_p))   (left regular representation minus constants,
                           pulled back to Gamma_D).
```

Claim: for some such `D`, `pi_p -> lambda_(Gamma_D)` strongly as `p -> infinity`,
`p` not in `P_D`: `lim ||pi_p(z)|| = ||lambda(z)||` for every `z in C[Gamma_D]`.

**Only the upper bound is at stake.**  For `a = z*z` and fixed `n`, once `p`
is large the support of `a^n` meets `Gamma_D(p)` only in `e`, so the trace of
`a^n` on `l^2(SL_3(F_p))` is `|SL_3(F_p)| tau(a^n)`; removing the constants
changes it by `(sum a)^n`, which is negligible after normalising.  Hence
`liminf ||pi_p(a)|| >= tau(a^n)^(1/n)` for every `n`, and this tends to
`||lambda(a)||`.  So the claim says: no outliers.

**Why primes.**  Along any sequence of levels in which a fixed modulus recurs
as a divisor, the full congruence representations never converge strongly
(`congruence-sc-fails-along-levels-with-recurring-divisor`); prime levels (or
new parts) are forced.

## Attempts

* **Invariant-vector obstruction.**  Absent at large `p`: every nonamenable
  subgroup is Zariski dense (`cubic-division-lattice-subgroups-are-zariski-dense`).
* **Automorphic temperedness.**  Not a proof.  Ramanujan bounds for the
  automorphic spectrum of `Gamma_D(p) \ SL_3(R)` (via Jacquet--Langlands,
  cuspidal `GL_3` forms) bound convolution by `K`-bi-invariant kernels.  An
  element `gamma in Gamma_D` acts on `l^2(Gamma_D / Gamma_D(p))` by right
  translation, which preserves no `K`-invariant structure, so the group ring
  is invisible to that spectrum.
* **Trace method with rapid decay.**  `Gamma_D` has property RD (V. Lafforgue,
  J. Lie Theory 10 (2000), cocompact lattices of `SL_3(R)`), which gives
  `|a^n(g)| <= ||lambda(a)||^n` pointwise.  But the girth of the level-`p`
  quotient is `Theta(log p)` while `log |SL_3(F_p)| ~ 8 log p`, so traces of
  powers below the girth lose a factor `|SL_3(F_p)|^(1/n) = e^(O(1))`.
  Beyond the girth the needed cancellation is equidistribution of the walk
  mod `p` with error `||lambda(a)||^n`, which is the claim itself.
* **Descent to thin subgroups.**  A positive answer is inherited by the
  congruence quotients of every finitely generated nonamenable subgroup,
  including thin free subgroups
  (`cubic-division-congruence-sc-descends-to-thin-subgroups`).  So the
  positive direction contains deterministic strong convergence for an
  explicit free group, which van Handel's survey (arXiv:2510.12520, Section
  2.2) records as open.  Conversely, one thin free subgroup with an outlier in
  its congruence Cayley graphs refutes this claim.
* **Numerical search for outliers.**  None found.  The algebra is
  `D = (Q(2cos(2pi/7))/Q, sigma, 2)`, with a certified free pair
  `<a^19, b^19> <= SL_1(Lambda)`.  The runs cover all `p == +-1 mod 7` up to 967,
  i.e. `N ~ 1e6`, on these sectors of `l^2_0(SL_3(F_p))`:
  - mean-zero functions on `P^2(F_p)`;
  - Legendre-twisted sections;
  - flags (Steinberg), up to `p = 139`.

  The excess over the regular norm stays within about `2e-4`, the same as for
  Haar-random pairs.  On `P^2` this holds for three weightings of the
  generators; on flags only equal weights were tested.  The one exception is a
  transient at `p = 419`, where `a^19` has order 22.  Cuspidal sectors are
  untested.  Details:
  `research/artifacts/cubic-division-congruence-numerics-2026-09-13.md`.
  Evidence only.
