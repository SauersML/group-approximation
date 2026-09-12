---
rg: 2
id: leavitt-evaluation-kernel-unitization-not-directly-finite
kind: claim
title: The unitized kernel of the Leavitt evaluation carries a one-sided inverse pair
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks for any one-sided inverse pair in F_2[R^x]; this asks for one whose defect is killed by evaluation, the invisible normal form, and it is sufficient for that target and independent of the visible form.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the visible normal form, a pair over (s_0, t_0); this is the invisible normal form, a pair over (1, 1).
  leavitt-evaluation-kernel-hits-augmentation-one: that is the established fact that the kernel is nonzero and meets augmentation one; this asks the kernel's unitization to fail direct finiteness.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

**OPEN.** Let `pi : F_2[R^x] ->> R = L_(F_2)(1,2)` be the evaluation and
`K = ker pi`. Exhibit `u, v` in `K` with

    (1 + v)(1 + u) = 1,        (1 + u)(1 + v) != 1.

Equivalently, the unital subring `K^+ = F_2 1 + K` of `F_2[R^x]` is not directly
finite. Equivalently, some direct-finiteness failure of `F_2[R^x]` has a defect
that evaluation kills. By `leavitt-inverse-defects-are-visible-or-invisible`,
this and `left-invertible-lift-of-s0-in-leavitt-group-algebra` are the only two
ways `F_2[R^x]` can fail to be directly finite.

In module form: a nonzero projective `P` with `S (+) P ~= S` and
`P (x)_S R = 0`, where `S = F_2[R^x]`. A defect is never equivalent to `1` in a
group algebra, and here it evaluates to zero as well. The defect has
augmentation zero and vanishing lifted trace, like every inverse defect.

## Attempts

* **Radical perturbation.** Dead. `z = [1] + [g] + [g^2]` lies in `K` and
  `1 + z = [g] + [g^2]` is a proper idempotent, so `K` is not in the Jacobson
  radical and `1 + K` contains non-units.
* **Separated powers.** Dead. `K` contains infinitely many orthogonal nonzero
  idempotents (`leavitt-recursive-kernel-idempotents`), which lie in every
  power, so the separated-powers mechanism of
  `residually-p-kernels-preserve-modular-stable-finiteness` cannot run.
* **Finite-dimensional detection.** Dead as a proof method. Every
  finite-dimensional representation of `F_2[R^x]` over a field factors through
  the augmentation, since `R^x` is finitely generated, simple and infinite. It
  therefore kills all of `K n ker(eps)`, where every invisible defect lives.
* **Recursive corner transport.** Neutral. The embedding `lambda` of
  `leavitt-primitive-corner-recursive-extension` satisfies `rho lambda = pi`. It
  maps invisible pairs to invisible pairs in the primitive corner and does not
  convert either normal form into the other.
* **Converting from the visible problem.** Not known in either direction.
  Direct sums of defect modules stay in their class, because `R (+) R ~= R`.
