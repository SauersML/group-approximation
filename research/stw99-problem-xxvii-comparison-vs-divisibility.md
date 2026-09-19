---
rg: 2
id: stw99-problem-xxvii-comparison-vs-divisibility
kind: claim
title: Strict comparison implies pure, and almost divisibility implies pure (STW Problem XXVII)
root: true
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
  - research/artifacts/stw27-villadsen-compact-divider-no-go-audit-2026-08-30.md
  - research/artifacts/stw27-soft-divider-hinge-audit-2026-08-30.md
  - research/artifacts/stw27-dimension-drop-high-rank-audit-2026-08-30.md
  - research/artifacts/stw27-real-rank-zero-divisibility-audit-2026-08-30.md
---

**Problem XXVII of Schafhauser--Tikuisis--White, arXiv:2506.10902**, two
parts, for `A` unital simple separable (nuclear) non-elementary: (1)
does strict comparison imply pureness (i.e. give almost divisibility for
free)?  (2) does almost divisibility of `Cu(A)` imply pureness (i.e.
give strict comparison for free)?  STW: "it is unclear whether strict
comparison gives rise to some form of divisibility, or... whether
sufficiently strong divisibility conditions give rise to strict
comparison."

Known: (1) holds when all ranks almost occur (AH algebras, ASH of slow
dimension growth); in the presence of strict comparison all the
divisibility conditions (almost divisibility, tracial divisibility,
Dadarlat--Toms (iii), rank realization) coincide.

A second positive class does not require rank realization: every simple
separable non-type-I real-rank-zero algebra has almost divisible Cuntz
semigroup (`stw27-real-rank-zero-almost-divisibility`).  The mechanism is
finite and local.  Perera--Rordam put arbitrarily large unital matrix blocks
inside every nonzero projection corner; elementary integer division of the
block sizes divides that compact Cuntz class, and projection approximate
units capture arbitrary way-below pairs.  Therefore strict comparison
implies purity throughout the real-rank-zero class, without a stable-rank-one
hypothesis.

## Attempts

* Part (1) follows from the Rank Problem
  (`stw99-problem-xxiii-rank-problem`): exact occurrence implies almost
  occurrence, and strict comparison + almost occurrence ⟺ pure
  (STW `prop:cu-regular` (7) ⟺ (5)).  Part (1) is also the exact
  companion needed to close Toms--Winter from Winter's question
  (`stw99-xxvi-xxvii-imply-xviii`).
* Toms's uniform-Γ counterexample `B` is now a second test object for
  part (2): `B` is not pure — it provably fails strict comparison
  (`toms-gamma-counterexample-fails-strict-comparison`) — while being
  AH with all ranks almost occurring.  So if `B` is almost divisible,
  part (2) is refuted outright.  `B` cannot test part (1), whose
  hypothesis it fails.
* Part (2) fails without simplicity trivially and has no known nuclear
  candidate; STW could not even produce a unital simple separable
  nuclear non-elementary algebra WITHOUT almost divisibility in which
  all ranks occur — the divisibility side of the Cuntz semigroup is
  essentially unprobed away from comparison.  Test cases they name:
  almost divisibility for Villadsen type I without strict comparison
  (sr1, so all ranks occur by Thiel) and for type II (unique trace).
  A type-I Villadsen computation of divisibility of the Cuntz class of
  the unit — i.e. whether `η_m`-type bundle classes admit approximate
  halving in the limit — is a concrete finite computation in the same
  Euler calculus as `uniformly-doubled-rordam-steps-force-proper-infiniteness`:
  there, exact halving of tower classes was shown to cross the
  section-existence boundary.  A mod-prime Chern calculation now shows that
  the `+1` slack still does not produce compact dividers in coordinate-heavy
  blocks: an `ell`-almost projection divider requires the coordinate Euler
  fraction to be at most `1/(ell+1)`, irrespective of factorial divisibility
  of the total matrix rank
  (`stw27-coordinate-euler-slack-obstructs-compact-dividers`).  Thus the
  proposed projection/bundle computation cannot prove almost divisibility.
  For a threshold-violating Villadsen system of this form, any counterexample
  to part (2) must instead divide the canonical compact Hopf class by a
  genuinely noncompact soft Cuntz element. Whether variable-rank soft
  elements evade the Chern obstruction is the exact
  remaining finite-stage hinge.  This is distinct from the simple AH
  examples of Robert--Rordam with `Div_* > 1` or `Div_* = infinity`: those
  algebras fail almost divisibility, whereas part (2) requires almost
  divisibility together with failure of strict comparison.
* The soft loophole closes completely for a homogeneous image bundle of
  rank `M<n(n+1)`: the fibre-rank interval of an `(n,n+1)`-divider has length
  less than one, so the divider has constant finite rank and is a projection
  (`stw27-low-rank-soft-divider-rounding`).  The bound is sharp: at
  `M=n(n+1)`, the rank-jumping module
  `C([0,1])^n direct_sum C_0((0,1])` is already a noncompact divider of the
  trivial bundle.  Since a Villadsen seed projection has unbounded image rank
  along the tail, this exact rounding theorem explains why the compact Chern
  obstruction does not yet decide the inductive limit.
* There is now also a uniform high-rank construction.  If `E` has rank `M`
  over a finite CW complex of dimension `d`, `D=ceil(d/2)`, and
  `M>=(2n+1)D+n(n-1)`, stable `K`-theory and the Bezout identity split
  `E` as `nF direct_sum (n+1)G`.  Thus `End(E)` contains a unital endpoint
  copy of `Z_(n,n+1)` and `[F]+[G]` is a compact divider
  (`stw27-stable-range-endpoint-division`).  On `(S^2)^N` this applies at
  `M>=(2n+1)N+n(n-1)`, regardless of Chern classes.  The finite-stage
  uncertainty is therefore confined to the middle rank/dimension window
  between the coordinate-Euler obstruction and this stable-range splitting.
