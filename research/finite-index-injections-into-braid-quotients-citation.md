---
rg: 2
id: finite-index-injections-into-braid-quotients-citation
kind: route
title: Import finite-index co-Hopf rigidity for mapping class groups of punctured spheres (Bell–Margalit, Behrstock–Margalit, Shackleton)
target: finite-index-injections-into-braid-quotients-are-geometric
requires: []
---

Citation import, not a reproof. The statements were read from the arXiv PDFs on
2026-09-13 by the z3-09 lane: first pages, introductions.

**Behrstock–Margalit**, *Curve complexes and finite index subgroups of mapping
class groups*, arXiv:math/0504328v2, §1. `Mod(S)` there is the extended mapping
class group. Verbatim:

> **Theorem 3.** If S is a surface which is not S_{0,2}, S_{0,3}, S_{0,4},
> S_{1,0}, S_{1,1}, S_{1,2}, or S_{2,0}, then every injection of a finite index
> subgroup of Mod(S) into Mod(S) is the restriction of an inner automorphism of
> Mod(S).

The same page credits the genus-zero case: "Bell–Margalit proved that the answer
is yes for S_{0,n} with n ≥ 5".

**Shackleton**, *Combinatorial rigidity in curve complexes and mapping class
groups*, arXiv:math/0503199v5 (Pacific J. Math.), Theorem 2. Verbatim, with its
complexity hypotheses: "Suppose that H is a finite index subgroup of the
mapping class group Map(Σ_1). Then, every injection of H into Map(Σ_2) is the
restriction of an inner automorphism of Map(Σ_1)". The introduction adds:
"Bell-Margalit [BelMar2] extend this to spheres with at least five holes."

**Bell–Margalit**, *Braid groups and the co-Hopfian property*,
arXiv:math/0403145v2, §1: `B_n / Z` is isomorphic to
`Mod(D_n) = π_0(Homeo^+(D_n))`. Main Theorem 3: for `n >= 4`, `B_n / Z` is
co-Hopfian. Its finite-index form for punctured spheres is the "BelMar2"
result cited above.

**Specialization.** Take `S = S_(0,n+1)` with `n >= 4`, which is not in the
exceptional list. Collapsing the boundary of `D_n` to a puncture identifies
`Mod(D_n)` with the stabilizer of that puncture in `Mod(S_(0,n+1))`. This has
finite index `n+1` in `Mod(S_(0,n+1))`, and index `2(n+1)` in the extended
group. A finite-index subgroup of `Q = B_n / Z` is therefore a finite-index
subgroup of `Mod^±(S)`, and an injection into `Q` is an injection into
`Mod^±(S)`. So Theorem 3 applies.
