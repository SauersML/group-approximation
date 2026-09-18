---
rg: 2
id: fp-groups-have-no-multiplier-product-completions
kind: claim
title: No finitely presented group has an open product of finite groups with infinitely many mod-p multipliers in its profinite completion
distinct_from:
  products-of-finite-groups-with-schur-factors-not-fp: that excludes subgroups of a product of finite groups that contain the restricted product; this assumes nothing about subgroups or restricted products and reads the obstruction off the profinite completion alone.
  kassabov-nikolov-alternating-frames-are-not-fp: that settles the Kassabov--Nikolov frames, which contain the restricted product of alternating groups; this excludes every finitely presented group whose completion has an open product of alternating groups, frame or not.
  simple-product-completions-block-regular-tree-actions: that turns an open simple product in the completion into a tree obstruction; this restricts which simple products a finitely presented group can have there.
---

**ESTABLISHED.** Let `Γ` be a finitely presented group and `Γ^` its profinite
completion (`Γ` need not be residually finite). Suppose some open subgroup `U`
of `Γ^` is isomorphic, as a topological group, to `prod_(i in I) Q_i` with
every `Q_i` finite. Then for every prime `p`, only finitely many `i` satisfy

```text
H^2(Q_i; F_p) != 0,   i.e.  Q_i has a non-split central extension by Z/p.   (MP1)
```

**Consequences.**
- For perfect `Q_i`, `(MP1)` says that `p` divides the order of the Schur
  multiplier `H_2(Q_i; Z)`. By `alternating-groups-have-nonzero-schur-multiplier`,
  every `Alt(n)` with `n >= 5` has `H^2(Alt(n); F_2) != 0`. So no finitely
  presented group has an open subgroup of its completion isomorphic to
  `prod_(n in I) Alt(n)` with `I` infinite. This is the Kassabov--Nikolov shape
  (`kassabov-nikolov-alternating-frames-are-not-fp`), now excluded for all
  finitely presented groups.
- The same holds for any family of simple groups whose multipliers share one
  prime infinitely often, for example `PSL_2(q)` with `q >= 5` odd, whose
  multiplier contains `Z/2`. That multiplier fact is Schur's classical
  computation and is not imported as a node; nothing downstream uses it.
- **What survives.** A product of simple groups can occur only if, for every `p`,
  `p` divides `|H_2(S_i; Z)|` for only finitely many `i`. Infinite families with
  trivial multiplier exist, for example `SL_2(2^k)` with `k >= 3` (again classical
  and not imported). This criterion says nothing about them.

The mechanism is standard in profinite presentation theory: the continuous
`H^2` of a finitely presented profinite group is finite-dimensional. The proof
recorded here is elementary and uses only the cohomology of a finite-index subgroup of `Γ`. No novelty is
claimed for the principle, only for its use on this frontier.

DERIVATION
fp-groups-have-no-multiplier-product-completions-proof
