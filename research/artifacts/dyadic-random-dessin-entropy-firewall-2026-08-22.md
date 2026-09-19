# Dyadic random-dessin entropy firewall — 2026-08-22

The Iwahori edge is `B=Z*C_2`, with generator pair `(U,E)`, and its twist is

```text
(U,E) -> (U^(-1)E,U^(-1)EU).
```

This Nielsen map is a bijection of
`Sym(n) x {fixed-point-free involutions}` and therefore preserves the
uniform product law.  Two independent random edge actions remain far after
the twist: for every `epsilon<1/4`, the probability that any of the `n!`
point relabellings matches both generators within normalized Hamming error
`epsilon` is at most

```text
exp(-(1/2-2epsilon)n log n+O(n)).
```

The estimate is only a Hamming-ball count.  A permutation ball costs
`(1-epsilon)n log n`, an involution ball costs
`(1/2-epsilon)n log n`, and allowing all relabellings returns
`n log n`; one half of an `n log n` entropy scale remains.

Consequently the random-lift program cannot independently sample two
high-girth Iwahori Schreier graphs and hope that a relabelling makes their
edge data agree.  Randomness, if it works, must come after a deliberately
correlated choice in the two modular extension loci.  The unresolved seam
is exactly the entropy/correlation of those loci; the present count does
not address it.

