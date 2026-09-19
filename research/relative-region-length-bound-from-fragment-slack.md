---
rg: 2
id: relative-region-length-bound-from-fragment-slack
kind: claim
title: Fragment slack transfers the strict region-versus-boundary length bound to free-product syllables
distinct_from:
  greendlinger-free-product-lemma: that demands an external subword longer than half a relator and its torsion companion; this asks only for a strict relator-length-versus-total-boundary inequality.
  bespoke-routing-lemma: that constructs the full common quotient and all fields of DefectRoutingData; this is only a possible shorter engine for its protected-length and factor-injectivity checks.
  kazhdan-envelope-needs-a-bespoke-relative-router: that also needs a tie-relator family, surjectivity, finite presentation and torsion preservation; this addresses only the length/injectivity component.
---

OPEN.  Let a reduced relative van Kampen diagram over a free product have at
least two regions and no degree-one vertices.  Suppose its symmetrized
relators satisfy whole-syllable `C'(1/7)`, every relator has syllable length
at least `42`, and partial-syllable overlaps obey the repository's
`FragmentSlack` inequality

```text
(1/7) wlen(r)+1 <= (1/6) wlen(r).                       (RLB1)
```

Prove, for every region `D` labelled by a relator `r_D`,

```text
wlen(r_D) < sylLength(boundary diagram).                (RLB2)
```

The one-region case is handled directly.  In the multi-region case the
intended proof ports the ear-deletion induction used in Kapovich,
*Small Cancellation Stability and Isomorphism Rigidity for Generic Finitely
Presented Groups* ([arXiv:2608.17238](https://arxiv.org/abs/2608.17238)):
delete a boundary region, compare the new and old outer boundaries, and use
`(RLB1)` to pay the two possible partial end syllables.  The induction need
not preserve free reduction of the boundary word; only its syllable length
ledger matters.

If `(RLB2)` holds, any boundary word shorter than the least relator cannot
bound a nonempty reduced diagram.  That is the exact form needed for
short protected-set injectivity and for the factor words in the proposed
relative Kazhdan envelope.  It may therefore replace the full
Greendlinger conclusion in those consumers once their dependence is split.

## Attempts

**Ear-deletion induction.**  Choose a boundary region, delete it, and compare
the two outer boundary ledgers without freely reducing the intermediate
word.  Whole-syllable pieces pay the interior arcs and `(RLB1)` pays at most
two partial end syllables.  The point still requiring proof is that the
relative reduction cannot create a new end fragment whose charge was
already spent at the adjacent region; this is the precise bookkeeping case
to isolate before any formalization.

## Scope firewall

`(RLB2)` does **not** produce a more-than-half external relator arc, the two
disjoint pieces needed by the current `n>=3` Greendlinger induction, or the
torsion-into-factors theorem.  In particular it does not close
`greendlinger-free-product-lemma`, `RelativeTorsionLeaf`, or the occurrence
Pauli incidence-labeling problem.  Those obligations remain separate even
if the protected-length consumers move to this lemma.
