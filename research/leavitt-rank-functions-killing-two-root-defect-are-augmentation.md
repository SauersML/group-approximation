---
rg: 2
id: leavitt-rank-functions-killing-two-root-defect-are-augmentation
kind: claim
title: A Sylvester rank function on the Leavitt unit group algebra is the augmentation rank exactly when it kills the two-root defect
distinct_from:
  el3-unit-root-matrix-units-iff-two-root-identities: that characterizes the matrix-unit hypothesis for one homomorphism of EL_3 into a ring; this applies it to the quotient of the group algebra by the null ideal of an arbitrary Sylvester rank function, so that the rank of one element decides the whole rank function.
  simple-group-rank-functions-are-augmentation-or-detecting: that shows a rank function other than the augmentation rank detects every nontrivial group element; this names one element of the group algebra, the two-root defect, whose rank already decides, with no simplicity hypothesis and over every field of positive characteristic.
  rank-models-of-el3-satisfy-the-two-root-identities: that is the open identity for homomorphisms into rank ultraproducts; this is an established equivalence for every Sylvester rank function on the group algebra, which makes the binary instance of that identity a special case of a statement about the group algebra alone.
artifacts:
  - research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-rankfn`; verification requested from `w3-vf-linear`) by
`leavitt-rank-functions-two-root-defect-proof`.

Let `K` be a field of characteristic `p > 0` and `R = L_K(1,2)`. Identify `Γ = R^x` with
`GL_3(R) = EL_3(R)` through the three-leaf prefix code. Put `N_ab = [x_ab(1)] - 1` and
`D = N_23 N_12` in `K[Γ]`. For every Sylvester matrix rank function `rk` on `K[Γ]`:

```text
rk = rk_ε      iff      rk(N_12^2) = 0  and  rk(D) = 0 .
```

In characteristic two `N_12^2 = 0` already in `K[Γ]`, so `rk = rk_ε` iff `rk(D) = 0`. The defect `D`
lies in the kernel of the evaluation `K[Γ] -> R`.

**Consequences.**
- `binary-leavitt-units-carry-nonaugmentation-rank-function` holds iff some Sylvester matrix rank
  function on `F_2[R^x]` gives `D` positive rank. Its negation is
  `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`.
- That negation makes every characteristic-two rank model of `R^x` trivial (route
  `non-linear-sofic-via-sylvester-two-root-gate`).
- A gate argument using only exact group relations, ring identities and the Sylvester axioms with
  faithfulness proves that negation. It then decides the target negatively, not only linear soficity
  (artifact Corollary 5).

## Attempts

Established, not open. Proof in artifact Section 1.
