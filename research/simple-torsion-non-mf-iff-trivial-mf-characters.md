---
rg: 2
id: simple-torsion-non-mf-iff-trivial-mf-characters
kind: claim
title: A simple torsion-marked group has full MF radical exactly when all of its MF characters are trivial
artifacts:
  - research/simple-torsion-mf-character-proof.md
distinct_from:
  simple-torsion-groups-have-a-macroscopic-mf-dichotomy: that reblocks every surviving corona representation into a pointwise Hilbert--Schmidt separating model; this identifies the resulting trace-limit criterion and its converse.
  hyperlinear-elementwise-visibility: that constructs finite Hilbert--Schmidt models from hyperlinearity; this starts with operator-norm asymptotic representations and uses their trace limits only after macroscopic reblocking.
---

Call `chi:G->C` an **MF character** when there are operator-norm asymptotic
unitary representations `sigma_n:G->U(d_n)` such that
`tr_(d_n)(sigma_n(g))->chi(g)` for every `g`.  Let `G` be a nontrivial
finitely generated simple group containing a nonidentity element of finite
order.  Then

```text
Rad_MF(G)=G
  iff
every MF character of G is the trivial character 1.                  (MFC1)
```

Thus the Property-`(T)`-free Leavitt radical problem can be stated without
Kazhdan language: every operator-norm microstate character of the simple
torsion-marked target must be trivial.  This reformulation does not solve
that problem.  If its proof used only normalized Hilbert--Schmidt
multiplicativity and applied to the regular character, it would instead
prove nonhyperlinearity; a genuinely MF-specific proof must consume
operator-norm/corona structure.

No Property `(T)`, stability theorem, or literature input is used.

DERIVATION
simple-torsion-mf-character-proof
