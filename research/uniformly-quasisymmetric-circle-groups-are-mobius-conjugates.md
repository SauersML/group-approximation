---
rg: 2
id: uniformly-quasisymmetric-circle-groups-are-mobius-conjugates
kind: claim
title: Every uniformly quasisymmetric group of circle homeomorphisms is quasisymmetrically conjugate to a Möbius group
---

Let `G` be a group of homeomorphisms of the circle `T` such that every `g ∈ G` is
`K`-quasisymmetric for one fixed `K` (in Markovic's normalization: `g` extends to a
`K`-quasiconformal self-map of the disc `D`). Then there is a quasisymmetric homeomorphism
`h` of `T`, with constant depending only on `K`, such that `h G h^{-1}` consists of
Möbius transformations.

Source: V. Markovic, *Quasisymmetric groups*, J. Amer. Math. Soc. 19 (2006), no. 3,
673–715, DOI 10.1090/s0894-0347-06-00518-2. The Crossref record summarizes the result as
"any K-quasisymmetric group is conjugate to a Möbius group with a constant depending on K",
and the abstract opens: "Let T denote the unit circle and D the unit disc. Suppose that
f : T → T is a homeomorphism... We say that a homeomorphism f : T → T is K-quasisymmetric
if there exists a K-quasiconformal map f̂ : D → D that extends f." Earlier cases:
A. Hinkkanen, *Uniformly quasisymmetric groups*, Proc. London Math. Soc. (3) 51 (1985),
318–338; A. Hinkkanen, *The structure of certain quasisymmetric groups*, Mem. Amer. Math.
Soc. 83 (1990), no. 422.

## Attempts

- 2026-09-13 (lane z2-18-f-h2-action): bibliographic data verified from Crossref and
  Semantic Scholar records. The theorem statement, its number and whether
  orientation-reversing maps are allowed have NOT been read from the paper (the AMS page and
  zbMATH returned 403). Needed to establish: read the main theorem verbatim and land
  `markovic-quasisymmetric-groups-citation` with `requires: []`. Consumer:
  `thompson-f-no-cobounded-qi-h2-action-via-markovic`, which uses it only for
  orientation-preserving groups.
