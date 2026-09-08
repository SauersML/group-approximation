---
rg: 2
id: three-factor-finite-alphabet-ca-are-surjunctive
kind: claim
title: Every injective finite-alphabet CA with at most three unary factors per term is surjective
artifacts:
  - research/artifacts/gottschalk-stable-three-factor-reduction-2026-09-08.md
---

For every group G, every integer q>=2, and every positive finite track
count N, set R=Z/qZ. Let H:(R^N)^G -> (R^N)^G be a cellular automaton
whose coordinate rules are finite sums of terms

    c product_(l=1)^d phi_l(x_(j_l)(g s_l)),  0<=d<=3,

where c is in R and the phi_l:R->R are arbitrary unary functions.
If H is injective, then H is surjective.

This claim is open here. The attached stable reduction proves its
equivalence to Gottschalk's conjecture when quantified over all q
and N; it does not prove the claim. A bound on the number of unary
factors is not an ordinary polynomial degree bound over Z/qZ.
The reduction imposes no bipartite operand graph, preserved auxiliary
tracks, or known bijective fiber for block elimination.

## Attempts

2026-09-08: The [stable-reduction artifact](artifacts/gottschalk-stable-three-factor-reduction-2026-09-08.md)
expresses every local rule using unary lookup functions and cancels each
term with at least four factors by adding two identity tracks and applying
reversible local shears. A decreasing integer potential proves finite
termination while both injectivity and surjectivity are preserved. This
establishes the reduction to the stated class, not its surjunctivity.
The transformed auxiliary outputs depend on the old inputs; setting them
to zero recovers the original rule rather than a known bijective fiber.
The existing homogeneous block and quadratic elimination results do not
cover the resulting unrestricted cubic interactions. A surjectivity
argument for injective maps in this full class remains missing.
