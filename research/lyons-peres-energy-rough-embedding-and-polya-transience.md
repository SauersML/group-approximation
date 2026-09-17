---
rg: 2
id: lyons-peres-energy-rough-embedding-and-polya-transience
kind: claim
title: "Lyons–Peres import: finite-energy flows characterize transience, rough embeddings carry transience forward, and Z^3 is transient"
distinct_from:
  f-dyadic-action-is-not-recurrent: that proves one specific Schreier graph of F is transient (via Mishchenko); this imports the general electrical-network criteria that turn embedded transient subgraphs into transience.
---

**Source.** R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge
University Press (2016); text read from the authors' online version
`https://rdlyons.pages.iu.edu/prbtree/book.pdf` on 2026-09-17 (printed pages 26, 39,
41 and 44 of that file, Chapter 2).

**Networks, verbatim (p. 26).** "It will be convenient to allow more than one edge
between a given pair of vertices: each such edge has its own conductance. We'll also
allow loops (edges with only one endpoint), but these may be ignored for our present
purposes since they only delay the random walk. Strictly speaking, then, G may be a
multigraph, not a graph."

**Theorem 2.11, verbatim (p. 39).** "(Energy and Transience) Let G be a denumerable,
connected network. Random walk on G is transient iff there is a unit flow on G of
finite energy from some (every) vertex to ∞."

**Rough embedding, verbatim (p. 44).** "Given two networks G and G′ with resistances
r and r′, we say that a map ϕ from the vertices of G to the vertices of G′ is a rough
embedding if there are constants α, β < ∞ and a map Φ defined on the edges of G such
that (i) for every edge ⟨x, y⟩ ∈ G, Φ(⟨x, y⟩) is a nonempty, simple, oriented path of
edges in G′ from ϕ(x) to ϕ(y) with Σ_{e′ ∈ Φ(⟨x,y⟩)} r′(e′) ≤ α r(x, y) and
Φ(⟨y, x⟩) is the reverse of Φ(⟨x, y⟩); (ii) for every edge e′ ∈ G′, there are no more
than β edges in G whose image under Φ contains e′."

**Theorem 2.17, verbatim (p. 44).** "(Rough Embeddings and Transience) If G and G′
are roughly equivalent connected networks, then G is transient iff G′ is transient.
In fact, if there is a rough embedding from G to G′ and G is transient, then G′ is
transient."

**Pólya's Theorem (second part), verbatim (p. 41).** "Simple random walk on the
nearest-neighbor graph of Z^d is transient for all d ≥ 3."

(The symbols `α, β, Z, ≥, ∞` were garbled by text extraction and are restored from the
surrounding definitions; the displayed words are otherwise as printed.)

**Scope.** Citation import only. Used by
`recurrent-orbits-force-every-z3-to-meet-the-stabilizer`.
