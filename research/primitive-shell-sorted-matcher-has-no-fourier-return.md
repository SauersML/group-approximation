---
rg: 2
id: primitive-shell-sorted-matcher-has-no-fourier-return
kind: claim
title: The primitive-shell sorted matcher has no Fourier-type second return
distinct_from:
  primitive-shell-sorted-matcher-is-one-phase-torus: that reduces every exact sorted matcher to K=RH; this proves that no point of that phase torus can use the standard symmetric-Fourier or monomial-square mechanism for obtaining a fourth return.
  periodic-clock-has-opnorm-almost-central-fourth-power-escape: that constructs unrelated fourth powers which almost centralize the clock; this is an exact obstruction imposed on the matcher itself.
artifacts:
  - research/primitive-shell-sorted-matcher-has-no-fourier-return-proof.md
---

**ESTABLISHED.**  Let `q=3^n`, `n>=2`, `L=2*3^(n-1)`, and let `P,D,B,H`
be the primitive-shell objects of
`primitive-shell-sorted-matcher-is-one-phase-torus`.  Thus, after a harmless
choice of Fourier signs,

```text
H_(a,b)=L^(-1/2) omega^(f(a)b),
f(a)=floor(2u_a/3),
u_a = the representative of 2^a mod q in {1,...,q-1},
```

and every exact sorted matcher is `K=RH`, with `R` diagonal unitary.

For every such `R`:

1. `K` is not symmetric;
2. `K^2` is not a monomial unitary.

In particular, the familiar Fourier return mechanism---symmetrize the
complex Hadamard matcher so that its square is a permutation and its fourth
power is scalar---is unavailable on every nontrivial primitive shell.

This is only a fence.  A projective order-four unitary may have a dense
involutive square, so the claim does **not** prove a positive lower bound for
`||K^4 P K^(-4)-P||`, and it does not exclude near-spectral matchers.
