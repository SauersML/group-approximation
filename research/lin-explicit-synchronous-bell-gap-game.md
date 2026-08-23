---
rg: 2
id: lin-explicit-synchronous-bell-gap-game
kind: claim
title: Lin's Bell-separation compiler gives an explicit synchronous commuting-versus-tensor gap game
artifacts:
  - research/artifacts/lin-mastel-slofstra-smooth-cover-ingestion-2026-08-23.md
distinct_from:
  kleene-mipco-self-destroying-game: that uses a recursion-theorem fixed point to force a tensor-product gap from the coRE game compiler; this uses Lin's later Bell-separation reduction directly on a machine already known not to halt and therefore needs no self-reference.
  mipstar-bcs-tracial-nonru-exists: that supplies a finite BCS algebra with a tracial but no RU model; this supplies an effectively named general synchronous game and does not linearize its predicates or construct a solution group.
---

There is an effectively specified finite synchronous nonlocal game `G_loop`
such that

```text
omega_co(G_loop)=1,
omega_*(G_loop)<=1/2.                                    (LBG1)
```

Moreover `G_loop` may be chosen from Lin's finite family of twelfth-level
conditionally-linear-samplable games.  It is explicit in the computability
sense: apply the effective reduction in the proof of the Bell-test separation
theorem to a fixed Turing machine whose program is an unconditional infinite
loop.

This is a theorem-level source of perfect commuting completeness and a fixed
finite-dimensional tensor-product gap.  It removes both an existential choice
of a separated game and the recursion-theorem selection used by
`kleene-mipco-self-destroying-game`.

It is not yet a nonhyperlinear group.  Lin's output is a general synchronous
game.  Passing to BCS syntax and then to LCS/solution-group syntax must preserve
the perfect commuting strategy and a quantitative tensor-product gap; no such
general BCS-to-LCS compiler is asserted here.

