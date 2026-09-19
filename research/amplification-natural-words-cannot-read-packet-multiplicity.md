---
rg: 2
id: amplification-natural-words-cannot-read-packet-multiplicity
kind: claim
title: Authenticated words cannot read anonymous packet multiplicity under amplification
distinct_from:
  two-generator-amitsur-levitzki-dimension-oracle: that detects the PI degree of the full ambient matrix algebra when arbitrary algebra variables are available; this shows why a finite group-word tuple does not expose the anonymous multiplicity algebra as arbitrary variables.
  packet-natural-selectors-cannot-extract-one-bounded-copy: that rules out a natural bounded-rank projection inside a packet isotypic component; this rules out reading the total number of copies by authenticated word polynomial identities.
  fixed-packet-hall-atlas-has-no-julia-cutoff-gap: that uses density of rational multiplicity flows; this uses exact tensor-amplification invariance before taking any limit.
---

Let a fixed finite packet act on its selected isotypic corner as

```text
rho tensor I_k on C^r tensor C^k.                    (ANW1)
```

Let `a_1(U),...,a_s(U)` be any fixed finite collection of matrices obtained
from group-word evaluations, packet compressions and fixed matrix block
operations.  Under the permitted amplification `U -> U tensor I_l`,

```text
a_j(U tensor I_l)=a_j(U) tensor I_l.                 (ANW2)
```

Consequently the generated algebra changes from `A_U` to
`A_U tensor I_l`.  It has exactly the same polynomial identities and the
same PI degree.  Meanwhile the anonymous packet multiplicity in `(ANW1)`
changes from `k` to `kl`.

Thus no Amitsur--Levitzki test on finitely many authenticated word matrices
can report the raw multiplicity `k`.  It reports at most the largest simple
degree of the algebra those words actually generate.  In particular the
centralizer relations alone allow all proposed tape letters to be scalar on
`C^k`, so their first standard identity may vanish at degree one for every
`k`.

One may apply the standard polynomial to **arbitrary** matrices in the full
commutant `M_k(C)` and thereby recover its ambient PI degree.  But those
arbitrary variables are not group-word occurrences and have no authenticated
relation to the Fanizza mark or to the two Julia return products.  Transporting
their stopping flag back to the mark is precisely the missing compiler, not
a consequence of the dimension oracle.

Therefore a dimension-activated Julia selector cannot key its heat depth to
anonymous selected-packet multiplicity using only a fixed word tape.  A
surviving trigger must first force a word-generated algebra whose simple PI
degree grows, or supply a nonlocal coordinate/irreducibility test which
authenticates the full multiplicity algebra.  That additional step must also
survive spectator amplification.
