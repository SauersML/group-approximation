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
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

**OPEN.** Let `pi : F_2[R^x] ->> R = L_(F_2)(1,2)` be the evaluation and
`K = ker pi`. Exhibit `u, v` in `K` with

    (1 + v)(1 + u) = 1,        (1 + u)(1 + v) != 1,

that is, `v + u + vu = 0` and `uv != vu`.

Equivalently, the unital subring `K^+ = F_2 1 + K` of `F_2[R^x]` is not directly
finite. Equivalently again, some direct-finiteness failure of `F_2[R^x]` has a
defect that evaluation kills. By `leavitt-inverse-defects-are-visible-or-invisible`,
this claim and `left-invertible-lift-of-s0-in-leavitt-group-algebra` are the only
two ways `F_2[R^x]` can fail to be directly finite.

In module form: a nonzero projective `P` with `S (+) P ~= S` and `P (x)_S R = 0`,
where `S = F_2[R^x]`.

The gk-kdf-lift lane proved the same invisible half independently. Its node was
merged into this one on 2026-09-12; the mapping of ids is in its artifact.

## Necessary conditions

* **Augmentation.** `eps(u) = eps(v) = 0`, since `eps(1 + v) eps(1 + u) = 1`.
* **Support.** The supports of `1 + u` and of `1 + v` each generate a subgroup whose
  group algebra is not directly finite
  (`subgroup-supported-one-sided-inverse-rigidity`).
* **The defect.** `d = 1 - (1 + u)(1 + v)` is an idempotent of `K`. It has zero class
  in `K_0(S)`, because `S = (1+u)(1+v) S (+) dS ~= S (+) dS`, and so it has zero
  lifted trace at every precision. It is not a finite sum of finite-subgroup
  projectives (`lifted-trace-detects-finite-subgroup-projectives`). It is never
  equivalent to `1` (Proposition 6 of the normal-forms artifact).
* **No nilpotent parts.** `1 + n` with `n` nilpotent is a two-sided unit, so a strict
  pair needs non-nilpotent kernel parts in both factors.

## Attempts

* **Kernel corners feed this claim.** If `q` in `K` is an idempotent and
  `b a = q != a b` with `a, b` in `qSq`, then `(1 - q) + a` and `(1 - q) + b` witness
  it. The cross terms vanish, and `a - q`, `b - q` lie in `K` because `K` is an ideal
  containing `q`. Nonzero kernel idempotents exist
  (`leavitt-corner-kernel-not-jacobson-radical`, `leavitt-recursive-kernel-idempotents`).
  This dies where every corner lane dies: no strict pair in any corner has been
  constructed.
* **Radical perturbation.** Dead. `z = [1] + [g] + [g^2]` lies in `K`, and
  `1 + z = [g] + [g^2]` is a proper idempotent. So `K` is not in the Jacobson radical,
  and `1 + K` contains non-units.
* **Separated powers.** Dead. `K` contains infinitely many orthogonal nonzero
  idempotents (`leavitt-recursive-kernel-idempotents`). They lie in every power, so
  the mechanism of `residually-p-kernels-preserve-modular-stable-finiteness` cannot run.
* **Finite-dimensional detection.** Dead as a proof method. Every finite-dimensional
  representation of `F_2[R^x]` over a field factors through the augmentation,
  because `R^x` is finitely generated, simple and infinite. So it kills all of
  `K n ker(eps)`, where every invisible defect lives.
* **Recursive corner transport.** Neutral. The embedding `lambda` of
  `leavitt-primitive-corner-recursive-extension` satisfies `rho lambda = pi`. It maps
  invisible pairs to invisible pairs in the primitive corner and converts neither
  normal form into the other.
* **Converting from the visible problem.** Not known in either direction. Direct sums
  of defect modules stay in their class, because `R (+) R ~= R`.
