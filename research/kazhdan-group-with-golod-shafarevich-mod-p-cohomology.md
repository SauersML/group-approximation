---
rg: 2
id: kazhdan-group-with-golod-shafarevich-mod-p-cohomology
kind: claim
title: Some finitely presented Kazhdan group has mod-p second cohomology below a quarter of the square of its mod-p first cohomology
distinct_from:
  fpbs-power-p-deficiency-excludes-property-t: that excludes power p-deficiency for Kazhdan groups; this asks whether a Kazhdan group can satisfy the unweighted Golod-Shafarevich inequality on its mod-p cohomology
  sp21-golod-shafarevich-test-gives-infinite-pro-p-rank: that is the certificate for Sp(n,1) lattice subgroups and its consequence; this asks whether any Kazhdan group at all satisfies the certificate's hypothesis
  sp21-gs-certificate-shape-at-uniform-levels: that records necessary conditions on a certificate inside an Sp(n,1) lattice; this is the general existence question for finitely presented Kazhdan groups
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

Assert that there are a finitely presented group `G` with property (T) and a prime
`p` such that

```text
d = dim H^1(G;F_p) >= 2   and   dim H^2(G;F_p) < d²/4.
```

By universal coefficients such a `G` has `d >= 5`, since `H_1(G;Z)` is finite.

**Why it matters.**
- A certificate of `sp21-golod-shafarevich-test-gives-infinite-pro-p-rank`, at a
  finite-index subgroup of a cocompact arithmetic `Sp(n,1)` lattice, is an instance
  of this claim.
- So if this claim is false, that certificate never fires, and the open claim
  `sp21-lattice-pro-p-completions-have-finite-rank` cannot be refuted by it.
- The pro-p completion of such a `G` is Golod–Shafarevich. By Golod–Shafarevich
  and Zelmanov it has infinite rank and contains free pro-p subgroups, while (T)
  holds.

**Relation to GS-τ.**
- Lackenby, arXiv:math/0509036, Conjecture 1.5 (the GS-τ Conjecture, attributed to
  Lubotzky and Zelmanov; read from the PDF) says: if `⟨X|R⟩` presents `G` and
  `d_p(G)²/4 > |R| - |X| + d_p(G)`, then `G` does not have (τ) with respect to some
  infinite nested sequence of normal p-power-index subgroups.
- Kazhdan groups have (τ) with respect to every such sequence. So the conjecture
  says no *presentation* of a Kazhdan group satisfies that inequality.
- For every presentation, `dim H^2(G;F_p) <= |R| - |X| + d_p(G)`
  (`sp21-gs-certificate-shape-at-uniform-levels` (ii)).
  - An example realized by a presentation would refute Conjecture 1.5.
  - The homological strengthening of Conjecture 1.5 would make this claim false.

## Attempts

- **Known Kazhdan Golod–Shafarevich groups: weighted only.**
  - Ershov's survey arXiv:1206.0490 §12 (read from the PDF) gives `G_(p,d)`,
    Golod–Shafarevich for `p >= 3, d >= 9` and Kazhdan for `p > (d-1)²`.
  - Its presentation has `d` generators and `d²` relators: `d(d-1)` of degree 3
    and `d` of degree `p`, read off `1 - dτ + d(d-1)τ³ + dτ^p`.
  - With `d_p <= d`: `|R| - |X| + d_p >= d² - d > d²/4`. So the presentation
    inequality fails, and the Golod–Shafarevich property there is weighted.
  - Whether `dim H^2(G_(p,d);F_p) < d²/4` was not determined. Ershov's Kac–Moody
    examples were not checked.
- **Lattices in `Sp(n,1)`.**
  - By universal coefficients, a lattice example needs
    `b_2 + d_p(tors H_2) < d²/4 - d`.
  - By `sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel` it needs an infinite
    pro-p congruence kernel. By `sp21-pro-p-kernel-invisible-to-local-linear-reps`
    that kernel is invisible to local-field linear representations.
  - No explicit presentation of a cocompact arithmetic `Sp(2,1)` lattice was
    available, so no mod-p cohomology was computed.
- **Contrast with `SL_2(C)`.** For closed hyperbolic 3-manifold groups, Poincaré
  duality in dimension 3 ties `H^2` to `H^1`, and Lubotzky's certificate is
  `d >= 5`. (T) fails there, so it is not an instance of this claim. For `Sp(n,1)`
  the manifold has dimension `4n >= 8`, and duality ties `H^2` to `H^(4n-2)`
  instead.
