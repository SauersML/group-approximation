---
rg: 2
id: comm-of-z-n-times-torsion-group-splits
kind: claim
title: Comm(Z^n x B) = GL_n(Q) x Comm(B) when B is a torsion group with trivial FC-centre, so these abstract commensurators are never finitely generated
distinct_from:
  fg-automorphism-hosts-contain-no-divisible-subgroup: that excludes automorphism groups of residually finite groups and of varieties; this is about abstract commensurators, which do contain GL_n(Q), and shows the product thickening of Z^n cannot make them finitely generated.
  gl-n-q-explicit-natural-fp-overgroup: that is the open Problem 2.7, whose host table lists abstract commensurators as untested; this settles the product-thickening test of that row.
artifacts:
  - research/artifacts/gq-gq-explicit-2-aut-comm-hosts.md
---

**ESTABLISHED** through `comm-of-z-n-times-torsion-group-splits-proof`. Lane proof,
not independently reviewed. No priority is claimed.

## Statement

Let `n >= 1` and let `B` be a group in which every element has finite order and
whose FC-centre (the elements with finitely many conjugates) is trivial. Then the
abstract commensurator splits:

    Comm(Z^n x B)  ≅  Comm(Z^n) x Comm(B)  =  GL_n(Q) x Comm(B).

Every commensuration restricts, on a finite-index subgroup `A_1 x B_1`, to a
product `α x β`.

## Consequences

1. **Never finitely generated.** `GL_n(Q)` is a direct factor, hence a quotient,
   and it is not finitely generated. So `Comm(Z^n x B)` is not finitely generated,
   and it is no host for Problem 2.7, however good `Comm(B)` is.
2. **Röver's thickening fails.** Take `B` to be Grigorchuk's group. It is torsion,
   and its FC-centre is trivial because it is just-infinite and not virtually
   abelian (argument in the route). Its commensurator is Röver's finitely presented
   simple group `V(B)` (Röver 1999; context only, not used). Then
   `Comm(Z^n x B) = GL_n(Q) x V(B)` contains `GL_n(Q)` and is not finitely
   generated. The same holds for every infinite finitely generated just-infinite
   torsion group, for example the Gupta--Sidki groups.

## Where the commensurator row of Problem 2.7 stands

- `Comm(Z^n) = GL_n(Q)` (standard; proved in the route). Not finitely generated.
- `Comm(SL_n(Z)) = PGL_n(Q) x| <transpose-inverse>` for `n >= 3`, a consequence of
  Margulis superrigidity and arithmeticity (context from
  `research/artifacts/gq-gq-k2-q-uniformity.md`, not re-derived). It contains
  `GL_{n-1}(Q)` and has finite-index subgroup `PGL_n(Q)`, so it is not finitely
  generated.
- `com(F)` for Thompson's `F`: "We show com (F) is not finitely generated"
  (Burillo--Cleary--Röver, arXiv:0711.0919v4, abstract). Not a host.
- The known finitely presented commensurators are commensurators of simple groups,
  where `Comm = Aut`, and those of branch groups (Röver). For branch groups the
  commensurator acts by almost-automorphisms of the tree. What is left is whether a
  branch or self-replicating group `Δ` can have a finitely generated `Comm(Δ)`
  containing `GL_n(Q)`. Consequence 2 shows that multiplying by `Z^n` does not do
  it.
