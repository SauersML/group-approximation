---
rg: 2
id: polynomial-radial-recursions-realize-the-full-germ-tower
kind: claim
title: The affine group with finitely many Newton radial automorphisms is self-similar and realizes the polynomial full group as its RN group
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

**OPEN — submitted recursion and full-group identification pending independent review.**

Let `A`, `ν`, and `B_{d,r}` be as in the artifact. For `j≥1`, set
`ρ_j(y)=δ_q^{C(ν(y),j)}(y)` and `ρ_j(1)=1`; put `ρ_0=δ_q`.
Then `G_d=<A,ρ_1,…,ρ_d>` is finitely generated and self-similar on
the `b`-ary coset tree, and `V_{b,r}(G_d)=B_{d,r}` for every `r≥1`.
For `d≥1`, the displayed self-similar action is noncontracting.

## Attempts

The submitted recursion has zero-digit section `ρ_jρ_{j-1}` and identity
sections at other digits, with trivial root permutation for `j≥1`.
In particular the sections of `ρ_1` along `0^k` are the distinct
`δ_q^kρ_1`, precluding a finite nucleus. For equality with the full
group, one inclusion follows from generator germs; the other requires
a base map matching exceptional images and p-exponents, followed by
localized radial products matching all remaining polynomial germs.
Rational chart changes shift `ν` and preserve degree. Existence of
the matching maps, all localization steps, and the final full-group
membership require verification; a recursion formula alone proves
neither the equality nor type `F_∞`. See artifact §10.
