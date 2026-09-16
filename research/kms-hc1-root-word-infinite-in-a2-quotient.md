---
rg: 2
id: kms-hc1-root-word-infinite-in-a2-quotient
kind: claim
title: The HC1 reflected root word keeps infinite order in the A~2 triangle quotient
artifacts:
  - research/artifacts/kms-hc1-root-word-a2-quotient-and-finite-images-2026-09-16.md
---

For every prime `p`, let

```text
Gamma^A2_p = < a,b,c |
  a^p, b^p, c^p,
  [a,b,a], [a,b,b], [b,c,b], [b,c,c], [a,c,a], [a,c,c] >,
```

with `[x,y]=x^-1 y^-1 x y` and left-normed iterated commutators. This is the
quotient of `Gamma_p` from `kms-hc1-reflected-root-word-is-nontrivial` by the
normal closure of `[a,c,c]`, since `[a,c,c,a]` and `[a,c,c,c]` follow from
`[a,c,c]=1`. Then

```text
r=[b,a],  s=[b,c]  satisfy  <r,s> = <r> * <s> = C_p * C_p  in Gamma^A2_p,
```

so `rs` has infinite order and `w_p=(rs)^p` is nontrivial in `Gamma^A2_p`.

This claim has three consequences:

- **Free product in `Gamma_p`.** Pulled back along `Gamma_p -> Gamma^A2_p`, it
  gives `<r,s> = C_p*C_p` in `Gamma_p` itself. That proof does not use
  Caprace--Marquis Theorem 6.9.
- **The hole forces non-residual-finiteness.** Suppose that, for some `p`,
  every finite image of `Gamma_p` kills `w_p`, as in
  `kms-hc1-finite-images-kill-reflected-root-word`. Then the CAT(0)
  triangle-complex group `Gamma^A2_p` is not residually finite.
- **A route to refuting the hole.** Suppose that, for every prime `p>=7`, some
  finite quotient of `Gamma^A2_p` does not kill `w_p`. Then that hole claim is
  false.
