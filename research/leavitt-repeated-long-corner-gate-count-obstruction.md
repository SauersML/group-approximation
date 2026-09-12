---
rg: 2
id: leavitt-repeated-long-corner-gate-count-obstruction
kind: claim
title: Four nontrivial gates make the repeated long-corner placement impossible
artifacts:
  - research/leavitt-repeated-long-corner-gate-count-proof.md
  - research/artifacts/search-leavitt-repeated-long-corner-radius2.py
  - research/artifacts/search-leavitt-repeated-long-corner-radius2.sbatch
distinct_from:
  leavitt-repeated-long-corner-template-kills-omega: that proves the abstract Tietze template works if the collision exists; this proves the chosen degree-four cyclic slot placement cannot realize that collision with nontrivial gates.
---

For signs `++-++-++`, fix

```text
g_2=a,  g_3=c,  g_5=b,  g_6=d
```

with all four gates nonidentity.  For arbitrary group elements
`g_0,g_1,g_4,g_7`, the unary corner `H` and trivalent tails `L,N` satisfy

```text
ell_C(H)=ell_C(L)+2=ell_C(N)+2
```

in the free product of the four coefficient copies.  Hence `H=L=N` is
impossible, even with arbitrarily long compound Leavitt words in the four
remaining slots.
