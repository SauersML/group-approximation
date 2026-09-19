---
rg: 2
id: marked-quotient-growth-necessity-proof
kind: route
title: One lamp at the compressed site witnesses the growth
target: marked-quotient-mf-forces-commutant-growth
requires: [commuting-lamp-defect-survives]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

The site `tau o` has `Stab_V(tau o) = tau Gbar tau^{-1} = abar(Gbar)`, and in
either quotient the lamp `c_{tau o}` commutes with every group element fixing
its site.  Hence

```text
Theta(c_{tau o})  in  Theta(abar(Gbar))' cap Q  =  Ad Theta(tau) (C).
```

If `Theta(c_{tau o})` also lay in `C = Theta(Gbar)' cap Q` it would commute
with `Theta(v_1)`, giving

```text
Theta(u) = Theta( c_{tau o} c_{v_1 tau o} ) = 1 ,
```

while `u` has nontrivial image in both quotients by
`commuting-lamp-defect-survives`.  Injectivity of `Theta` forbids this, so the
inclusion `C <= Ad Theta(tau)(C)` is strict.

No property (T), no transport, and no finiteness is used; the argument is the
compression relation plus injectivity on one element.
