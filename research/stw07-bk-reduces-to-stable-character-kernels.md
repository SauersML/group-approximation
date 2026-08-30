---
rg: 2
id: stw07-bk-reduces-to-stable-character-kernels
kind: claim
title: The Blackadar-Kirchberg problem reduces exactly to unital stable-character kernels
distinct_from:
  stw99-problem-vii-blackadar-kirchberg: this is an equivalent normal form for a counterexample, not a proof that every stable-character algebra is quasidiagonal.
artifacts:
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

The following two assertions are equivalent:

1. every separable nuclear stably finite C*-algebra is quasidiagonal;
2. every nonzero separable unital nuclear stably finite C*-algebra `E` which
   admits a character `chi:E -> C` with stable essential kernel is
   quasidiagonal.

More precisely, any counterexample `A` to assertion 1 produces the
counterexample

```text
E=(A tensor K)~,       ker(chi)=A tensor K,              (SC1)
```

to assertion 2.  Thus a negative answer never requires a nonsplit extension
or a quotient more complicated than `C`.
