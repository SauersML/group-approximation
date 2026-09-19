---
rg: 2
id: residually-p-two-generator-recursive-is-pi3-complete
kind: claim
title: For every prime p, being residually a finite p-group is Pi-zero-three complete for two-generator recursive presentations
distinct_from:
  residual-finiteness-two-generator-recursive-is-pi3-complete: that is residual finiteness, decided by the profinite topology of Z; this is residual p-finiteness, decided by the pro-p topology, with p-adic rows in place of dyadic ones and the lower central p-series in place of arbitrary finite-index subgroups.
  shift-raag-family-is-rf-iff-symmetrized-index-set-closed: that is the profinite criterion; this is its pro-p refinement on the same family.
---

ESTABLISHED.  Fix a prime `p`.  For `J <= Z_{>0}` and
`G_J = < a, t | [a, t^j a t^-j] = 1, j in J >`,

```text
G_J is residually a finite p-group   iff   J^s = J u (-J) u {0}
                                           is closed in the pro-p topology of Z,   (RP1)
```

i.e. iff for every `d notin J^s` some `k` has `(d + p^k Z) n J^s` empty.
Consequently, for recursive presentations on two generators,

```text
RESIDUALLY-p_rec2 is Pi^0_3-complete,     its complement Sigma^0_3-complete.  (RP2)
```

The hardness family uses `p`-adic rows `{ p^x (p j + 1) : j < |W_g(e,x)| }`.
