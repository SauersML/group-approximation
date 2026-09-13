---
rg: 2
id: zaremsky-4-03-rips-complex-of-zn-contractible
kind: claim
title: "Zaremsky Problem 4.3 resolved: is the Rips complex of Z^n with the standard word metric contractible at large scale?"
root: true
distinct_from:
  hyperbolic-rips-complex-models-proper-actions: that is the classical fact that large-scale Rips complexes of hyperbolic groups model proper actions; this is Zaremsky's question for the free abelian group Z^n with its standard word metric
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 3,
verbatim: "Is the Rips complex of `Z^n` with the standard word metric
contractible for large enough Rips parameter? [The answer is yes, recently
proved by Ziga Virk in arXiv:2405.09134.]"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-03-by-virk` requires
  `rips-complexes-of-integer-lattices-are-contractible`.
- **No** would be a sequence of arbitrarily large scales with non-contractible
  Rips complexes. The yes answer refutes it, so no no-route is written.

Never write a `requires: []` route into this claim.

**Reading.** The standard word metric on `Z^n` comes from the standard basis
and equals the `l^1` metric `d_1`. "Contractible for large enough Rips
parameter" means there is `r_0` with the Rips complex contractible for every
scale `r ≥ r_0`. Since `d_1` is integer-valued, the closed convention
(diameter `≤ r`) and the open convention (diameter `< r`) differ only by a shift
of the scale by 1, so the answer does not depend on the convention.

**Status.** Answered affirmatively in the list's own note, by Žiga Virk
(arXiv:2405.09134).
