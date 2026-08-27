---
rg: 2
id: steinberg-ordinary-fourier-blocks-do-not-descend-mod-p
kind: claim
title: Ordinary additive Fourier blocks neither descend mod p nor remain stable under X
invalidates:
  - steinberg-x-dual-via-ordinary-additive-fourier-blocks
artifacts:
  - research/steinberg-fourier-block-firewall-proof.md
distinct_from:
  steinberg-x-plus-incidence-dual-is-surjective: this invalidates one semisimple frequency proof of the open modular surjectivity statement, not that statement itself.
---

**ESTABLISHED FIREWALL.**  Over an auxiliary characteristic-zero splitting
field, partial `b`-Fourier transform gives a clean formula for endpoint
potentials, but `A^(-1)` mixes `b` and `c` frequencies and `B^(-1)` mixes
`a` and `b` frequencies.  Hence `X_ch^*` has no fixed-`b`-frequency block.

More decisively, the desired rank statement is over `F_p`, where

```text
F_p[C_p]=F_p[t]/(t-1)^p.                               (SFF1)
```

Translations are unipotent rather than diagonalizable.  Cyclotomic
frequency division introduces factors whose product is `p`, so
characteristic-zero Fourier invertibility cannot certify the rank modulo
`p`.  A valid transform must control the full augmentation filtration and
the exceptional tree cuts.

DERIVATION
steinberg-fourier-block-firewall-proof
