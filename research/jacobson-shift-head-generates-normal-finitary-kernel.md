---
rg: 2
id: jacobson-shift-head-generates-normal-finitary-kernel
kind: claim
title: The shifted Jacobson head normally generates a simple locally finite linear kernel
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that identifies the kernel of the full Jacobson ring group's symbol map; this proves the kernel inside the separately specified stable-letter presentation and gives its quotient by presentation elimination.
  jacobson-shift-has-full-finite-linear-intervals: that constructs the finite intervals; this proves their union is normal, simple, and exactly the marked normal closure.
artifacts:
  - research/artifacts/jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md
---

In `Theta_shift`, let `L=<K_i:i in Z>`. Then

```text
L ~= GL_fin(F_2^(Z x {1,2,3})),
L normal in Theta_shift,
L=normalClosure(G_Q)=normalClosure(w),   w=x_13,Q.
```

The group `L` is infinite, nonabelian, simple and locally finite,
and the literal bilateral representation is faithful on it.
Consequently every homomorphism from `Theta_shift` either kills
all of `L` or is injective on `L`; this is not an assertion of
injectivity on the whole ambient group.

There is also an exact quotient description

```text
Theta_shift/L ~= Lambda x Z,
Lambda=<G_P *_(K_P) G_* |
          (h q_P)^3=1,
          [[h c_P h,k_P],h r_P h] r_P=1>.
```

Both displayed factors of the amalgam are the prescribed `GL_3(F_2)`
groups, sharing `K_P=GL(<e_1,e_3>)`, with `h=w_12` in `G_*`.
No identification of `Lambda` with an arithmetic group is asserted.

The unrestricted matrix-gap problem asks whether every norm-corona
homomorphism kills this kernel. Local finiteness and simplicity alone
do not answer that question.

DERIVATION
jacobson-shift-finitary-normality-and-quotient-proof
