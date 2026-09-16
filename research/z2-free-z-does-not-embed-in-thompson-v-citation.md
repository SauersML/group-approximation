---
rg: 2
id: z2-free-z-does-not-embed-in-thompson-v-citation
kind: route
title: Import Bleak--Salazar-Díaz Theorem 1.2 that Z^2 * Z does not embed in V
target: z2-free-z-does-not-embed-in-thompson-v
requires: []
---

Literature import. It was recorded on 2026-09-16 by the swarm lane working on
`zaremsky-2-01-thompson-f-amenable`.

## Sources

1. **C. Bleak and O. Salazar-Díaz**, *Free products in R. Thompson's group V*,
   arXiv:0911.0979v1 [math.GR], 5 Nov 2009. The PDF was fetched on 2026-09-16 and its text
   was extracted locally (zlib-decompressed content streams, since no PDF text tool was
   available). Ligatures and some symbols were lost in extraction. Quotations below restore
   `∗`, `≅`, `∈` and `≤`, which the extraction dropped, from the evident mathematical
   context.
2. **Journal version.** Trans. Amer. Math. Soc. 365 (2013), no. 11, 5967–5997. The journal
   page returned HTTP 403 on 2026-09-16, so the journal text was NOT compared with v1.
3. **Independent restatements already in the graph** (not re-fetched by this lane):
   Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356v3, Theorem 4.6(1), quoted in route
   `closed-mcg-v-nonembedding-via-koberda`, and Burillo–Cleary–Röver, arXiv:1402.3860v2,
   quoted in route `wreath-z-by-z2-does-not-embed-in-thompson-v-citation` ("Neither the
   free product $\Z*\Z^2$ nor ... are subgroups of $V$").

## Verbatim, arXiv v1

- **Abstract.** "We also show the somewhat surprising result that Z^2 ∗ Z does not embed in
  V, even though V has many embedded copies of ..."
- **Definition of FPV, page 2.** "Let FPV denote the class of groups which 1. admit
  decompositions as free products of pairs of non-trivial subgroups, and 2. embed into V."
- **Theorem 1.2.** "The group Z^2 ∗ Z does not embed in FPV." Read with the definition,
  this says `Z^2 ∗ Z ∉ FPV`. Since `Z^2 ∗ Z` is a free product of two non-trivial
  subgroups, the theorem says that `Z^2 ∗ Z` does not embed into `V`. The surrounding text
  asks the motivating question "Does Z^2 ∗ Z embed in Thompson's group V?"
- **Section 4.2, heading and set-up.** "4.2 Z^2 ∗ Z cannot embed in V. We now create an
  algorithm, whose net effect will be to show that Z^2 ∗ Z does not embed into V. We do
  this by taking a supposed embedding, and through a process of 'improvements,' we show
  that our embedded group actually admits torsion elements. Throughout the remainder of
  the paper, we will assume G = ⟨a, b, c | [a, b]⟩ ≅ Z^2 ∗ Z, and that φ : G → V is an
  embedding."
- **Conclusion of the proof.** "In particular, there can be no embedding of Z^2 ∗ Z in V".

## Matching

The group in the claim is `⟨a, b, c | [a, b]⟩`, which is exactly the `G` of §4.2, and
"not a subgroup of `V`" is "no embedding `G → V`". Nothing else is imported.

**Disambiguation.** The extraction renders both `Z^2` and `Z_2` as "Z 2" (for instance
"PSL(2, Z) ≅ Z 2 ∗ Z 3" in the introduction). The group of Theorem 1.2 is `Z^2 ∗ Z`, not
`Z_2 ∗ Z`, because of the presentation `⟨a, b, c | [a, b]⟩` in §4.2. Also `Z_2 ∗ Z` is a
free product of two members of the class `A` (finite groups and `Z`), so it lies in FPV by
Theorem 1.1 and could not be the subject of Theorem 1.2.

## Trust boundary

The proof in §4 (an algorithmic sequence of subgroup selections forcing torsion) was NOT
checked by this lane. The import rests on the theorem statement in v1, which is repeated
as a theorem in two surveys by specialists.
