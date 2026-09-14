---
rg: 2
id: boundary-crossed-product-is-a-leavitt-path-algebra
kind: claim
title: For every field k and d >= 2, LC(∂F_d, k) ⋊ F_d is isomorphic to the Leavitt path algebra of the reduced-letter graph with 2d vertices
distinct_from:
  boundary-crossed-product-carries-leavitt-family: that writes a unital d-ary Leavitt family inside the boundary crossed product, which is a homomorphism from L_k(1,d) and not onto; this is a ring isomorphism with a Leavitt path algebra of a finite graph.
artifacts:
  - research/artifacts/sk-hyperlinear-boundary-a-reduction-2026-09-13.md
---

ESTABLISHED by `boundary-crossed-product-is-a-leavitt-path-algebra-proof` (unreviewed).

Let `F_d = <c_1, ..., c_d>` with `d >= 2`, and let `A = {c_1^(±1), ..., c_d^(±1)}` be the letters. `∂F_d` is the space
of infinite reduced words, and `C(w)` is the cylinder of words beginning with `w`. Put
`R_∂ = LC(∂F_d, k) ⋊ F_d` with `P_U u_g = u_g P_(g^(-1)U)`.

Let `E_d` be the finite graph with vertex set `A` and one edge `e_(ab)` from `a` to `b` whenever `b != a^(-1)`. Then

```text
rho(a) = P_(C(a)),   rho(e_(ab)) = u_a P_(C(b)) = P_(C(ab)) u_a,   rho(e_(ab)^*) = P_(C(b)) u_(a^(-1))
```

extends to a unital ring isomorphism `rho : L_k(E_d) -> R_∂`.

This is the algebraic counterpart of Spielberg's Cuntz–Krieger description of `C(∂F_d) ⋊ F_d`. Here the
isomorphism is written down directly, over any field, with no groupoid machinery.
