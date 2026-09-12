---
rg: 2
id: tame-maps-induce-every-permutation-of-prime-field-cubes
kind: claim
title: Formally invertible polynomial maps induce every permutation of F_p^n for n >= 2 and only the affine group for n = 1
distinct_from:
  formalizable-pairs-induce-polynomial-automorphisms-on-constants: that constrains formalizable pairs through the constant-configuration map; this computes which permutations formally invertible maps can realize, which is what makes sitewise pairs formalizable after stabilization.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `p` be prime. The permutations of `F_p^n` induced by composites of elementary maps
`x_i -> c x_i + f(x_(j != i))`, with `c` in `F_p^x` and `f` a polynomial, are:
- all of `Sym(F_p^n)` when `n >= 2`;
- exactly `AGL(1,p)` when `n = 1`. This is `Sym(F_p)` only for `p <= 3`.

Every such composite is formally invertible.

**Proof sketch** (Section 3 of the artifact; self-contained, no external input):
1. The elementary map `x_i -> x_i + delta_b`, with `delta_b` the indicator polynomial of a point `b` in the
   other coordinates, induces a `p`-cycle on one axis-parallel line.
2. For `p = 2` these are the hypercube-edge transpositions, which generate the symmetric group.
3. For `p` odd, two line cycles meeting in one point have a 3-cycle as commutator. These 3-cycles have
   connected supports, so they generate the alternating group (a short induction, Lemma 3.3).
4. Scaling one coordinate by a generator of `F_p^x` is an odd permutation.
5. In one variable, formally invertible polynomial maps are affine.
