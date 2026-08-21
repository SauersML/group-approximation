# André--Guirardel recursive-presentation audit

**Archived 2026-08-21.** This is a source audit identifying an unresolved
effectivity seam, not an active mathematical claim.

No non-recursiveness claim is made.

The André--Guirardel construction gives a two-generated simple property-`(T)`
sharply 2-transitive group, but the published proof does not state that the
marked group is recursively presented and does not provide the effective
choices needed to infer this automatically.

There are two successive direct-limit constructions.

1. In Section 4, elements and pairs are enumerated, but the next HNN step is
   selected according to semantic alternatives such as "maximal of type
   `D_Z`" and "maximal isolated".  The proof establishes existence of the
   relevant chain; it does not give algorithms deciding those alternatives or
   enumerating the resulting kernels.
2. In Theorem 5.3, the final actor is the direct limit of epimorphisms obtained
   by iterating Proposition 5.6.  That proposition in turn invokes an
   existential small-cancellation quotient theorem.  The text supplies no
   algorithm which, from finite marked data at stage `n`, outputs a finite or
   recursively enumerable presentation for the selected quotient at stage
   `n+1`.

Some apparent enumeration issues are harmless: one could enumerate cyclic
subgroups rather than recognize all virtually cyclic subgroups.  That does
not repair the load-bearing issue, which is effective production of the HNN
and small-cancellation quotient maps and their kernels.

Therefore the implication

```text
Andre--Guirardel actor  ==>  recursively presented actor            (AGR1)
```

is not currently justified by the cited source.  Nor does finite generation,
simplicity, property `(T)`, or having four conjugacy classes imply `(AGR1)`.

If `(AGR1)` is proved by an effective refinement of their construction, then
`recursive-permutational-lamp-presentation` gives the marked lamp group as a
finitely generated recursively presented group.  After the still-open global
normalized-HS rounding/word-energy theorem proves that marked group
nonhyperlinear, `higman-bypass-needs-only-fg-recursive-nonhyperlinear`
produces a finitely presented nonhyperlinear overgroup.  Hence the old finite
presentation and finitely-generated-stabilizer gates disappear entirely and
are replaced by this strictly weaker actor-effectivity gate.

Primary source checked: Simon André and Vincent Guirardel, *Finitely generated
simple sharply 2-transitive groups*, Compositio Mathematica 160 (2024),
1941--1957, arXiv:2212.06020, especially the proof of Theorem 4.1 and
Theorem 5.3 / Proposition 5.6.
