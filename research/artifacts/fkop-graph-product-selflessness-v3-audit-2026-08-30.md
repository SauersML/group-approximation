# Complement-connected graph-product selflessness: source and version audit

## Primary source and current version

Felipe Flores, Mario Klisse, Mícheál Ó Cobhthaigh, and Matteo Pagliero,
*Selfless reduced free products and graph products of C-star algebras*,
arXiv:2510.24675v3, <https://arxiv.org/abs/2510.24675>.

The arXiv record was checked on 30 August 2026.  Version 3 is dated 5 August
2026, is labelled the final version to appear in *Advances in Mathematics*,
and says explicitly that Theorem C and Corollary D were extended to infinite
graphs.  This matters here: the Cairn claim allows a countably infinite graph
and therefore cites v3, not v1 or v2.

## Exact theorem match

Theorem C (Theorem 2.2) assumes:

1. an undirected simple graph with at least three vertices;
2. connected complement graph;
3. a unital C-star algebra at each vertex with a GNS-faithful state; and
4. at every vertex, a unitary in the state's centralizer having state zero.

It concludes that the reduced graph-product C-star probability space is
**completely selfless**.  The proof treats infinite graphs explicitly at the
end of Theorem 2.2 by passing through finite full subgraphs whose complements
are connected.

For a nontrivial discrete group `G_v`, the canonical trace on `C*_r(G_v)` is
GNS-faithful and tracial, and any nonidentity regular unitary has trace zero.
Thus all four hypotheses match without an exactness, amenability, rapid-decay,
linearity, or vertex-selflessness assumption.  The usual graph-product
representation identifies the resulting reduced graph product with
`C*_r(graph_product G_v)`; the paper uses the Caspers--Fima reduced
graph-product model throughout.

Corollary D states the consequences used in the claim: in the tracial case
the graph product has unique normalized 2-quasitrace, strict comparison,
stable rank one, and a unique unital embedding of the Jiang--Su algebra up to
approximate unitary equivalence; the preceding sentence of the corollary also
gives the uniform Dixmier property and hence simplicity.

## Novelty and scope audit

Repository searches for `graph products selflessness`, `complement connected`,
and the arXiv identifier found no import of this theorem.  The nearest Cairn
claim, `stw91-cograph-products-preserve-selflessness`, is different: it covers
P4-free graphs by alternating free and tensor permanence, and requires exact
selfless vertex reduced algebras.  The v3 theorem covers arbitrary connected
complement graphs and needs only nontrivial vertex groups.

This is a positive class for STW Problem XCI and, through Corollary D, for STW
Problem LXIII.  It does **not** settle either universal root: not every
C-star-simple group is presented by such a graph product, and the Jiang--Su
uniqueness conclusion concerns these graph-product codomains only.
