---
rg: 2
id: sharply-two-transitive-augmentation-lamp-host-audit
kind: claim
title: A simple property-T sharply 2-transitive actor gives the exact lamp backend, subject to two open gates
distinct_from:
  finitary-alternating-augmentation-lamp-global-rounding-no-go: that supplies a hyperlinear counterexample when the actor has no spectral rigidity; this identifies what the property-T sharply 2-transitive actor does prove.
  bounded-template-expanding-character-actor-family: that asks for finite actor families; this uses one infinite sharply 2-transitive action.
  infinite-character-actor-word-energy-interface: that asks for approximate word-energy transport; this proves only the exact orbit and representation facts.
---

ESTABLISHED, with explicitly open actor-effectivity and normalized-HS gates.

Let `A` be an infinite finitely generated simple group with property `(T)`
acting sharply 2-transitively on a countably infinite set `X`.  Put

```text
M={f in direct_sum_X F_2 : sum_x f(x)=0},
Gamma=M rtimes A.                                             (ST1)
```

Then the following exact statements hold.

1. `M` is cyclic as an `F_2[A]`-module: any pair lamp
   `m_xy=delta_x+delta_y`, `x != y`, normally generates it.
2. The dual action of `A` on `M_hat` has no nontrivial finite orbit.
3. Every finite-dimensional unitary representation of `Gamma` kills `M`.
4. For any fixed finite Kazhdan generating set of `A`, all nontrivial
   character orbits have one uniform positive Schreier spectral gap.
5. The diagonal action on `X^2` has exactly two orbits.

Thus this actor supplies exactly the **exact** infinite-character backend
needed by `one-seed-infinite-character-expansion-collapses-mark`: one lamp
seed has an infinite uniformly expanding character orbit, and no exact
finite-dimensional representation can retain that lamp.

The result of Andre--Guirardel (arXiv:2212.06020, Theorem 1.1 and Corollary
5.4) supplies such an `A`: it is 2-generated, simple, sharply
2-transitive, and has property `(T)`.

It does **not** close the group compiler.  For a direct finitely presented
lamp host, two load-bearing statements are not supplied by that paper:

- finite presentability of `A` and finite generation of a point stabilizer;
- a family-size-independent normalized-HS decoder producing the global
  spectral PVM for `M` from a microstate of a finite presentation.

The paper proves finite generation, not finite presentation.  Its final
group is constructed as a direct limit of an infinite chain of small-
cancellation quotients (proof of Theorem 5.3).  No assertion that the
limit is finitely presented, or that an involution centralizer/point
stabilizer is finitely generated, is made there.

However, direct finite presentation is stronger than necessary.
`higman-bypass-needs-only-fg-recursive-nonhyperlinear` shows that a finitely
generated recursively presented marked lamp group is enough: after proving it
nonhyperlinear, embed it in a finitely presented group.  Moreover
`recursive-permutational-lamp-presentation` shows that for the action on the
conjugacy class of an involution, the lamp extension is recursively presented
as soon as the actor is.  Its point stabilizer is a centralizer, whose word
preimage is recursively enumerable automatically.

The published construction is not currently verified effective in this
sense.  `andre-guirardel-recursive-presentation-audit` isolates the remaining
algebraic gate: the iterative existential HNN/small-cancellation choices do
not come with an algorithm enumerating the final kernel.  Thus the old two
finite-presentation hypotheses can be replaced by the strictly weaker open
claim that the actor can be chosen recursively presented.

The other omission is analytic rather than bibliographic.  Property `(T)`
gives a gap for **exact** unitary representations of `A`.  A matrix tuple
with small presentation defect is not thereby an exact representation,
and property `(T)` alone is not normalized-HS stability.  Therefore the
exact Schreier gap cannot be inserted into the PVM-energy argument until
`property-t-must-upgrade-global-augmentation-rounding` (and the separate
actor word-energy interface) is proved.

See `sharply-two-transitive-lamp-fd-invisibility-proof` and
`augmentation-lamp-finite-presentation-criterion` for the two exact
proofs used in this audit.
