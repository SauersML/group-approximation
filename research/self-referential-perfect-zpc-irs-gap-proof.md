---
rg: 2
id: self-referential-perfect-zpc-irs-gap-proof
kind: route
title: Make the ZPC halting diagonalization self-referential
 target: self-referential-perfect-zpc-irs-gap
requires:
  - zpc-irs-value-computable-upper-hierarchy
---

Let `T(e)=G_e` denote the effective TailoredMIP compiler of
Bowen--Chapman--Vidick.  For each finite tailored game `G`, the prerequisite
provides computable rational optima

```text
alpha_1^Z(G) >= alpha_2^Z(G) >= ... -> omega_ZIRS(G).
```

Define a partial computable two-input procedure `P(e,-)` which ignores its
second input, computes `G_e`, and then computes the upper hierarchy until it
finds a stage satisfying

```text
alpha_t^Z(G_e) < 1.
```

At the first such stage it halts.  (If no such stage occurs it runs forever.)
By the parameter theorem this is a computable program transformer in `e`.
The effective Kleene recursion theorem therefore supplies, effectively from
this transformer, an index `e_*` whose machine has exactly the behavior of
`P(e_*,-)`.

Put `G_*=G_(e_*)`.  We first prove that the fixed-point machine does not halt.
If it halted, TailoredMIP perfect completeness would give `G_*` a perfect
finite ZPC permutation strategy.  Such a strategy is in particular a ZPC-IRS
strategy, so

```text
omega_ZIRS(G_*)=1.
```

Every `alpha_t^Z` is an upper bound on `omega_ZIRS` (and game values are at
most one), hence no stage can satisfy `alpha_t^Z(G_*)<1`.  This contradicts
the defining halting condition of the fixed-point machine.  Therefore
`e_*` is a non-halting TailoredMIP instance.

TailoredMIP soundness now applies to this *particular* instance and gives

```text
omega*(G_*) < 1/2.                                      (1)
```

It remains to determine its ZPC-IRS value.  Suppose
`omega_ZIRS(G_*)<1`.  Since the computable upper bounds converge downward to
that value, for some finite `t` we would have

```text
alpha_t^Z(G_*) < 1.
```

But this is exactly the event on which the fixed-point machine halts, contrary
to the preceding paragraph.  Hence

```text
omega_ZIRS(G_*)=1.                                      (2)
```

The ZPC-IRS strategy space is the closed subset of the compact IRS strategy
space cut out by the finitely many Z-alignment and edge-commutation cylinder
equations; the finite-game value is continuous.  Therefore the supremum in
(2) is attained by an actual perfect ZPC-IRS strategy.

Finally, the effective recursion theorem produces `e_*` algorithmically from
the displayed program transformer.  The TailoredMIP compiler is effective
and outputs a finite game, so `G_*` is a computably specified finite tailored
game.  This strengthens the earlier pure-existence diagonalization: no
search through unknown non-halting machines is left.
