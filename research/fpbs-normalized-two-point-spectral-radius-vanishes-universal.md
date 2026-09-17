---
rg: 2
id: fpbs-normalized-two-point-spectral-radius-vanishes-universal
kind: claim
title: On every nonamenable transitive graph the l2 norm of the subcritical two-point operator is little-o of the susceptibility
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for boundedness of the critical operator; this asks only that the subcritical operator norms grow more slowly than the susceptibility, a ratio statement with no rate and no critical-exponent content.
  fpbs-hutchcroft-l2-gap-criterion: that imports the criterion mixing susceptibility and iota; this is the universal OPEN statement that 1-iota(T_p) tends to zero, with no susceptibility bound.
  fpbs-critical-volume-tail-mean-field-universal: that is the critical exponent half (V) of critical l2; this is the spectral half (S), the only half that fails on amenable graphs.
---

OPEN. Let `G` be a connected, locally finite, transitive, nonamenable graph,
`T_p` its two-point operator and `chi_p=||T_p||_(1->1)`. Then

    ||T_p||_(2->2) / chi_p -> 0     as p ↑ p_c,

or equivalently `s(p) = 1-iota(T_p) -> 0`.

This is condition (S) of `fpbs-critical-l2-iff-volume-tail-and-spectral-spreading`.
That claim proves:

* critical l2 is equivalent to (S) plus (V);
* `s(p)=1` for all `p<p_c` on every amenable graph;
* on a Cayley graph, (S) forces `chi^H_p = o(chi_p)` for every amenable
  subgroup `H`;
* under (V), a single sequence `p_n ↑ p_c` with
  `s(p_n) < (1-p_c)^2/(2C''^2||A||^2)` already gives (S).

**Necessary conditions it must survive.** On `F_2 x Z` (standard generators)
the cluster mass inside a coset of the central `Z` must be `o(chi_p)`. More
generally the same holds for every amenable subgroup, including the infinite
amenable normal subgroups of nonamenable groups.

## Attempts

* **2026-09-17, ratio form.** Chosen as the nonamenable half of critical l2.
  Uniform spectral gap of the simple random walk does not give (S) directly.
  `T_p/chi_p` is a Markov operator whose step distribution depends on `p` and
  spreads to scale `xi_p -> infinity`. Nonamenability bounds the spectral
  radius of a fixed walk below 1, but not of walks at growing scale, unless
  their steps are uniformly non-concentrated on amenable pieces. Item 6 of
  the equivalence node shows this non-concentration is necessary.
