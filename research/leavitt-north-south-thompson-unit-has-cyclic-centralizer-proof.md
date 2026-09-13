---
rg: 2
id: leavitt-north-south-thompson-unit-has-cyclic-centralizer-proof
kind: route
title: Push supports through the flow, read coefficients near the attractor, and compare contraction rates
target: leavitt-north-south-thompson-unit-has-cyclic-centralizer
requires: [leavitt-algebras-l-k-1-n-are-simple, binary-leavitt-unit-word-problem-decidable]
artifacts:
  - research/artifacts/leavitt-north-south-centralizer-2026-09-12.md
---

Full proof in the artifact. The inputs are simplicity of `R`, which makes both the
function module and every aperiodic Chen module faithful, and the normal form. The steps
are these.

- **Lemma 1.** An element of depth `N` with `T` terms enlarges support measure by at most
  `T 2^N`.
- **Lemma 2.** An element annihilating every function that vanishes near both fixed
  points annihilates every aperiodic Chen module, so it is `0`.
- **Step 1.** If `g` commutes with `c^a`, then `g` preserves the flow module. Otherwise
  the support of `g c^(-am) f` would be both vanishingly small and almost everything.
- **Step 2.** On a deep fundamental domain `[0^(ak) 1]`, a term of `g` either shifts the
  zero prefix, contributing `c^j f`, or lands within `N` domains of the fixed points.
  Equivariance forces the second kind to cancel. So `g = p_g(c)` on the flow module,
  where `p_g` is the parity polynomial of the terms `(0^a', 0^b)`.
- **Step 3.** Lemma 2 gives `g = p_g(c)`. The units of `F_2[t^(+-1)]` are monomials.
- **Items 3 and 4.** Suppose `g c^a g^-1 = c^b`. The domains `c^(am) D` have measure
  `2^-(am-1) mu(D)`, and a function is contracted by `c^(bm)` at rate `2^-bm` or expanded
  near the repeller. Lemma 1 applied to `g` and to `g^-1` gives `|a| = |b|`. Conjugation
  then maps `N_Q(<c>)` to `{+-1}`, with kernel `<c>`.
- **Item 5.** Finite `<c>`-orbits under conjugation lie in some `C_Q(c^n) = <c>`.
