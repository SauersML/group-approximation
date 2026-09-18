---
rg: 2
id: thompson-f-bounded-cohomology-vanishes-separable-duals
kind: claim
title: "Monod 2021: the bounded cohomology of Thompson's group F vanishes in every positive degree for every separable dual Banach module; in particular F is boundedly acyclic"
distinct_from:
  amenable-normalish-kills-l2-betti-bounded-cohomology: that is the BKKO vanishing for mixing modules in any group with an amenable normalish subgroup; this is Monod's vanishing for separable dual modules, proved through co-amenable lamplighter subgroups of F.
  thompson-f-quasimorphisms-vanish-on-f-prime: that concerns homogeneous quasimorphisms restricted to F'; this is vanishing of all bounded cohomology of F with separable dual coefficients, which contains the degree-two trivial-coefficient case.
---

**ESTABLISHED (literature import).**

**Source.** N. Monod, *Lamplighters and the bounded cohomology of Thompson's group*,
arXiv:2112.13741v1 (27 Dec 2021); published in Geom. Funct. Anal. 32 (2022) (journal data recalled,
not re-read).

**Verbatim** (§1, read from the arXiv PDF on 2026-09-17):

> "Theorem 1. Thompson's group F is boundedly acyclic."

> "This statement means that the bounded cohomology H^n_b(F) vanishes for all n > 0, where H^n_b(−)
> denotes the bounded cohomology (of Gromov [Gro82] and Johnson [Joh72, §2]) with coefficients in R
> viewed as a trivial module."

> "Theorem 2. The vanishing H^n_b(F, E) = 0 holds for all n > 0 and all separable dual Banach F-modules E."

> "However we caution the reader that this statement does not answer the amenability question. Indeed,
> our proof also works for many groups that are similar to F but known to be non-amenable. For instance,
> the proof holds unchanged for all piecewise-projective groups introduced in [Mon13]."

§4.C, verbatim: "Theorem 3 does not hold without the separability assumption on the dual module E.
Indeed, in that case the vanishing of H^n_b(−, E) for all n > 0 is equivalent to amenability."

**Reading notes.**
- Johnson's criterion, as recalled in the source: "amenability is equivalent to the vanishing of
  H^n_b(−, E) with coefficients in all dual Banach modules E, see [Joh72, Thm. 2.5]."
- The proof of Theorem 2 applies Corollary 6 of the source to `F'` acting on the dyadic points of
  `(0,1)`, with `Z_0` the open interval between a dyadic `x_0` and `g(x_0)`. It was read but not
  re-checked line by line.

Proof route: `thompson-f-bounded-cohomology-separable-citation`.
