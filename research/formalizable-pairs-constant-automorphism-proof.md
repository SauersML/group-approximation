---
rg: 2
id: formalizable-pairs-constant-automorphism-proof
kind: route
title: Specialize every site variable to one track variable and use that surjective endomorphisms of polynomial rings are automorphisms
target: formalizable-pairs-induce-polynomial-automorphisms-on-constants
requires: []
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Section 2 of the artifact.

1. `X_(h,i) -> T_i` is a ring homomorphism. By equivariance it sends `tau*(X_(g,i))` to `p_i(T)` for every
   `g`, and the formal identity `Q_i((tau*(X_(s,j)))_(s,j)) = X_(1,i)` to `q_i(p(T)) = T_i`.
2. So `q o p = id`. Then `p* o q* = id` for the pullbacks, `p*` is a surjective endomorphism of the
   Noetherian ring `F_q[T_1..T_n]`, hence injective, hence an automorphism.
3. Evaluating at a constant configuration gives `p(c) = mu(c,...,c)`.
4. For `n = 1`, degrees multiply under composition, so `p` is affine. `|AGL(1,q)| = q(q-1) < q!` for
   `q >= 4` supplies non-affine permutations, whose sitewise automata have no formalizing representatives.
