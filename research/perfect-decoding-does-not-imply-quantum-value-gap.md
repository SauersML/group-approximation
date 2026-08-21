---
rg: 2
id: perfect-decoding-does-not-imply-quantum-value-gap
kind: claim
title: Excluding perfect finite-dimensional LCS strategies does not bound quantum value below one
artifacts:
  - research/artifacts/zpc-perfect-decoding-gap-audit-2026-08-18.md
---

There are finite binary linear-system games with

```text
omega^q(G)=1
```

but with no perfect finite-dimensional strategy.  Hence a compiler theorem
which only says that every **perfect** finite-dimensional output strategy
decodes to a perfect input strategy cannot, by itself, establish the strict
quantum-value hypothesis required by `perfect-lcs-gap-implies-nonhyperlinear`.

Slofstra's arXiv:1703.08618 gives exactly such an LCS example: a perfect
correlation exists in `C_qa`, as a limit of finite-dimensional strategies, but
none exists in `C_q`/`C_qs`.  This is the non-closedness phenomenon that an
approximate-representation argument must control.
