---
rg: 2
id: lalonde-perfect-fd-strategy-has-no-tracial-game-state
kind: claim
title: A perfect finite-dimensional game strategy need not yield any perfect tracial game state
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  maximally-entangled-vectorization-is-hs-isometry: that gives an exact normalized-HS identity once the canonical maximally entangled state is already available; this proves that a general perfect finite-dimensional strategy cannot be replaced by that state for free.
  one-gram-vector-decodes-a-finite-bcs-strategy: that intentionally retains one nontracial Gram vector and derives a sound finite strategy; this is an explicit example showing why such state data cannot generally be discarded.
  tracial-npa-cannot-separate-canonical-trace: that says a feasible canonical trace defeats a matrix-only separator; Lalonde instead gives a different finite game whose prescribed perfect tracial face is empty and has an exact finite-level certificate.
---

**THEOREM/FENCE (Lalonde, arXiv:2608.05378v1).**  There is a bipartite
game `G_(4,3,6,6)` with four Alice questions, three Bob questions, and six
answers on each side which has a perfect finite-dimensional strategy in
local dimension six, but no perfect strategy using a maximally entangled
state (Theorem 1.1).

The separation is exactly relevant to tracial compilation.  Lalonde forms
a star algebra with square-root generators `M_a^x,N_b^y`, effects

```text
E_a^x=(M_a^x)^*M_a^x,  F_b^y=(N_b^y)^*N_b^y,
sum_a E_a^x=sum_b F_b^y=1,  [E_a^x,F_b^y]=0.          (LTS1)
```

A perfect maximally entangled strategy would give a tracial state `f` on
this algebra satisfying

```text
f(E_a^x F_b^y)=0                                      (LTS2)
```

for every losing answer pair.  A strengthened level-four tracial-NPA
calculation proves that no such tracial state exists.  The infeasibility
certificate is rational (5.6 MB), and the resulting nonexistence proof is
formalized in Lean as `noPerfectMaximallyEntangledStrategy`.

The perfect strategy uses the nonmaximally entangled Schmidt vector
proportional to `(1,1,2,2,2,2)`.  Thus

```text
perfect finite vector-state strategy
  does not imply a perfect state on the tracial face (LTS1)--(LTS2).  (LTS3)
```

This is a hard fence around any Cairn compiler step that silently replaces
an arbitrary perfect strategy by normalized-HS/maximally-entangled data.
It does not rule out state-aware Gram compilers, and it does not by itself
produce a finite-dimensional-versus-commuting value gap: the same game
already has a perfect finite-dimensional strategy.
