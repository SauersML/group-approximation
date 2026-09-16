---
rg: 2
id: thompson-f-has-hilbert-space-compression-one-half-citation
kind: route
title: Import the Arzhantseva--Guba--Sapir computation of the Hilbert space compression of F
target: thompson-f-has-hilbert-space-compression-one-half
requires: []
---

Citation import. No proof is re-derived here.

G. Arzhantseva, V. Guba, M. Sapir, *Metrics on diagram groups and uniform
embeddings in a Hilbert space*, arXiv:math/0411605 (v1 26 Nov 2004, latest
version 19 Apr 2005). Abstract read verbatim on 2026-09-16 from the arXiv abstract
page. The abstract page shows no journal reference, and the journal version was
not checked.

- **Abstract, verbatim:** "We give first examples of finitely generated groups
  having an intermediate, with values in (0,1), Hilbert space compression (which
  is a numerical parameter measuring the distortion required to embed a metric
  space into Hilbert space). These groups include certain diagram groups. In
  particular, we show that the Hilbert space compression of Richard Thompson's
  group $F$ is equal to 1/2, the Hilbert space compression of the restricted
  wreath product $Z\wr Z$ is between 1/2 and 3/4, and the Hilbert space
  compression of $Z\wr (Z\wr Z)$ is between 0 and 1/2. In general, we find a
  relationship between the growth of $H$ and the Hilbert space compression of
  $Z\wr H$."

**Body checked (referee, 2026-09-16, text extracted from the arXiv PDF).**
Definition 1.2 of AGS ("cf. [17, Def. 2.2]", i.e. Guentner–Kaminker) defines the
compression `R(G)` as the supremum of `α ≥ 0` for which there is a uniform
embedding of `G` into a Hilbert space with lower control `ρ_1(n) = C n^α`
(`C > 0`) and linear upper control `ρ_2`. Theorem 1.3 reads: "The Hilbert space
compression of R. Thompson's group F equals 1/2."

This agrees with the definition in the target claim. Linear `ρ_2` on a word
metric (integer distances) is the same as Lipschitz. A lower bound
`C d^α - D` can be upgraded to `C' d^α` for all `x ≠ y` by adding the
Lipschitz, bounded-below component `x ↦ δ_x ∈ ℓ²(G)`. Conversely `C d^α`
trivially gives `C d^α - D`. So the two suprema coincide.

Guentner–Kaminker, *Exactness and uniform embeddability of discrete groups*,
arXiv:math/0309166, abstract verbatim (read 2026-09-16): "We define a numerical
quasi-isometry invariant of a finitely generated group, whose values parametrize
the difference between the group being uniformly embeddable in a Hilbert space
and the reduced C*-algebra of the group being exact."
