---
rg: 2
id: star-surjective-nonaffine-context-blocks-fano-empty-link-lift
kind: claim
title: A star-surjective nonaffine source context prevents universal Fano empty-link pruning after the R-star lift
distinct_from:
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that assumes cap ranges for a section of one isolated pp gadget; this proves that the proposed empty-link condition would force those cap ranges because every source assignment extends through the whole constraint neighborhood.
  distance-two-oracularity-does-not-force-fano-pruning: that gives an unrelated repeated-clause counterexample to the generic implication; this applies to the actual copied-clause geometry in CMPS Lemma 20 and the subsequent Culf--Mastel fixed-language lift.
  cmps-rstar-lift-has-line-hitting-empty-links: that is the universal positive assertion this theorem refutes.
---

**ESTABLISHED NO-GO FOR THE ACTUAL CMPS/CM LIFT.**  Call a source context
`i` with relation `C_i` *star-surjective* if, for every `phi in C_i`, one can
choose satisfying assignments for every context meeting `i` so that all of
the chosen assignments agree on every common variable.

Suppose a contextwise pp reduction replaces every source context by a finite
gadget over `R_*`, with private auxiliary variables between different source
contexts, and then only performs satisfaction-preserving subdivision and
replaces empty two-variable constraints by the non-TVF one-constraint
`R_*` gadget.  If `C_i` is star-surjective and nonaffine, then the final
`R_*` instance cannot satisfy

```text
for every target context c descended from gadget i and every Fano line L,
some a in L has Link(c,a)=empty.                         (SNE1)
```

In particular, there are a target context `c` and a translated Fano line
`L` such that every `a in L` has a nonempty compatible-neighborhood link.

## Proof

For every `phi in C_i`, choose a satisfying pp witness `sigma_i(phi)` in the
gadget replacing `i`.  By star-surjectivity, extend `phi` to mutually
overlap-consistent satisfying assignments of all source contexts meeting
`i`, and choose pp witnesses in their gadgets.  Private auxiliaries from
different source contexts do not overlap, so these witness assignments agree
wherever their gadgets meet.

Subdivision merely exposes conjuncts on subsets of the same variables.
Every newly introduced empty constraint is satisfied by every endpoint
pair; after Proposition 6.2 of Culf--Mastel, that pair extends to the replacing
`R_*` constraint because non-TVF supplies a witness for all four Boolean
endpoint pairs.  Thus the chosen assignments extend through every final
target context in the constraint-neighborhood of each target occurrence
`c` descended from gadget `i`.

Consequently, for every `phi in C_i`, the local tuple

```text
sigma_i(phi)|_c
```

belongs to the nonempty-link set

```text
T_c={a in R_* : Link(c,a) is nonempty}.                 (SNE2)
```

If `(SNE1)` held, `T_c` would miss at least one point of every translated
Fano line and hence would be a Fano cap.  Therefore the occurrence range

```text
S_c={sigma_i(phi)|_c : phi in C_i} subseteq T_c          (SNE3)
```

would be a Fano cap for every `R_*` occurrence in the pp gadget for `i`.
The theorem `fano-cap-range-sections-cannot-encode-nonaffine-relations`
would then imply that `C_i` is affine, contrary to hypothesis.  This proves
the no-go.

## Application to the CMPS construction

Lines 427--436 of Lemma 20 in Culf--Mastel--Paddock--Spirig,
*The quantum smooth label cover problem is undecidable*,
arXiv:2510.03477v3, give the needed source context explicitly.  For every
original 3SAT clause `u`, the construction introduces local copies `x_u` of
its three variables, copies the same clause on those local variables, and
connects each `x_u` to its global variable `x` by the two implication clauses

```text
x OR x OR NOT x_u,       x_u OR x_u OR NOT x.            (SNE4)
```

Take one copied proper 3SAT clause.  Its relation is a signed copy of
`F_2^3 \ {0}`, hence has seven points and is nonaffine.  Every satisfying
assignment of its three local variables extends through its whole source
constraint-neighborhood: use the same assignment on the other copies and
set each global `x` equal to its local `x_u`.  Both clauses in `(SNE4)` are
then satisfied, and these are all neighboring constraints by the incidence
construction in Lemma 20.  Thus this copied clause is star-surjective.

Culf--Mastel Corollary 6.7 uses fresh private auxiliaries between source
contexts; Definition 5.1 only subdivides the resulting conjunction; and
Proposition 6.2 replaces every empty pair by one non-TVF constraint admitting
all endpoint pairs.  These are exactly the transformations covered above.
Therefore the universal line-hitting assertion for the resulting fixed
`R_*` family is false.

