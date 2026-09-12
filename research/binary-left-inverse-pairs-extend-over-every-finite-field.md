---
rg: 2
id: binary-left-inverse-pairs-extend-over-every-finite-field
kind: claim
title: Every binary left-inverse pair extends to a Frobenius-equivariant left-inverse pair over every finite field of characteristic two
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asks for one polynomial pair whose identity is formal; this shows left-inverse extensions over each finite field always exist, so formality is exactly a uniform-degree condition.
  low-degree-strict-pairs-have-one-sided-linear-parts: that extracts one-sided linear parts from a pair over F_q with deg sigma * deg tau < q; this constructs extensions over every F_(2^k) whose slicewise rules read traces of degree 2^(k-1), with no degree bound claimed either way.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `tau`, `sigma` be automata on `(F_2^n)^G` with `sigma o tau = id`. For every `k >= 1` there are
automata `tau_k`, `sigma_k` on `(F_(2^k)^n)^G` that:
- restrict to `tau` and `sigma` on the Boolean subshift;
- commute with the sitewise Frobenius;
- satisfy `sigma_k o tau_k = id`;
- keep the same memories.

If `tau` is strict, `tau_k` is strict.

**Construction.** Normalize `tau(0) = 0` by a constant translation. Take a normal basis `beta_j` and
its trace-dual normal basis `gamma_j`. Apply `tau` to each Boolean slice `Tr(gamma_j x)` and
recombine along `beta_j`.

**Consequence.** A pair is formalizable iff one `F_2`-polynomial pair of representatives satisfies
the identity on `F_(2^k)`-points for infinitely many `k`. Finite fields never obstruct
formalizability: the obstruction can only be uniformity of degree, which is to say the infinite
field.

Proof: Section 3 of the artifact.
