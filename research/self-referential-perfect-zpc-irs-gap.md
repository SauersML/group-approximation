---
rg: 2
id: self-referential-perfect-zpc-irs-gap
kind: claim
title: A computably specified TailoredMIP fixed point has perfect ZPC-IRS value and a quantum gap
distinct_from:
  perfect-zpc-irs-quantum-gap-game: That theorem extracts some soundness instance by contradiction; this one selects a particular instance effectively by self-reference.
  explicit-zpc-irs-gap-game-witness: That target asks for the finite game table to be literally materialized and audited; this theorem gives an effective finite specification but deliberately leaves that extraction separate.
---

Fix once and for all an acceptable numbering of Turing machines, the effective
Bowen--Chapman--Vidick TailoredMIP compiler `e |-> G_e`, and the computable
ZPC-IRS upper hierarchy from `zpc-irs-value-computable-upper-hierarchy`.
There is an effectively obtainable machine index `e_*` such that, for the
finite tailored game

```text
G_* = G_(e_*),
```

we have

```text
omega_ZIRS(G_*) = 1,
omega*(G_*) < 1/2,
```

and the ZPC-IRS value one is attained by an actual strategy.

More precisely, `e_*` can be obtained by the effective form of Kleene's
recursion theorem from the program transformer which, on parameter `e`,
computes the rational sequence `alpha_t^Z(G_e)` and halts at the first stage
with

```text
alpha_t^Z(G_e) < 1.
```

Thus the existential machine in the halting diagonalization can be replaced
by one computably specified self-referential machine.  Since the TailoredMIP
map is effective and its output is finite, the finite game `G_*` is itself
computably specified.  This statement does not claim that the enormous game
table has already been materialized in the repository; that separate
engineering task is isolated by `materialize-self-referential-zpc-game`.
