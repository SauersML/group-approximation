---
rg: 2
id: sp21-gs-certificate-shape-at-uniform-levels
kind: claim
title: A Golod-Shafarevich certificate on an Sp(n,1) lattice subgroup needs mod-p H^1 of dimension at least 5, and at a uniform level either a large excess over the p-adic dimension or dying cup products of congruence characters
distinct_from:
  sp21-golod-shafarevich-test-gives-infinite-pro-p-rank: that is the certificate and what it proves; this records necessary conditions for its hypothesis to hold on a Kazhdan lattice subgroup
  sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel: that characterizes a finite kernel through Betti numbers along the derived p-series; this bounds second cohomology from below at a single level through cup products
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**ESTABLISHED (item (iii) imports Lazard's theorem).** Let `Γ`, `p` and `Γ(p)` be as
in `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`, with `Δ <= Γ` of
finite index. Put `d = d_p(Δ) = dim H^1(Δ;F_p)` and `r = dim H^2(Δ;F_p)`. The
certificate of `sp21-golod-shafarevich-test-gives-infinite-pro-p-rank` is
`d >= 2` together with `r < d²/4`.

1. **(i) Universal coefficients.**
   - `H_1(Δ;Z)` is finite by (T), so `d = d_p(H_1(Δ;Z))` and
     `r = d + b_2(Δ) + d_p(tors H_2(Δ;Z))`.
   - So the certificate holds iff `b_2(Δ) + d_p(tors H_2(Δ;Z)) < d²/4 - d`. In
     particular `d >= 5`.
2. **(ii) Presentations.** For every finite presentation `⟨X|R⟩` of `Δ`,
   `r <= |R| - |X| + d`.
   - A presentation with `d²/4 > |R| - |X| + d` gives a certificate.
   - Such a presentation is exactly the hypothesis of the GS-τ Conjecture
     (Lackenby arXiv:math/0509036, Conjecture 1.5, attributed to Lubotzky and
     Zelmanov). For a Kazhdan group that hypothesis contradicts the conjecture,
     because (T) gives (τ) along every chain.
3. **(iii) Uniform levels, `p` odd.**
   - Suppose `Δ <= Γ(p)` has uniform closure `U` of dimension `D`. Let
     `V <= H^1(Δ;F_p)` be the inflated congruence characters, so `dim V = D`.
   - Put `e = d - D >= 0`, and let `t` be the dimension of the kernel of the cup
     product `Λ²V -> H^2(Δ;F_p)`.
   - Lazard (`H^*(U;F_p) ≅ Λ^* H^1(U;F_p)`) gives `r >= C(D,2) - t`. So a
     certificate needs `C(D,2) - t < (D + e)²/4`.
   - If `t = 0`, it needs `d > sqrt(2D(D-1))`. For `Sp(2,1)`, `D = 21·[k:Q]`.
4. **(iv) Dying cup products.**
   - Suppose a nonzero class of `H^2(U;F_p)` inflates to `0` on `Δ`, e.g. `t >= 1`
     in (iii). Then `Δ` has a finite p-quotient that does not factor through `U`:
     a non-split central extension, by `F_p`, of a finite quotient of `U`.
   - This needs no import. It gives a non-congruence p-quotient, i.e. a
     nontrivial pro-p congruence kernel. It does not give an infinite one.

**Where a certificate can live.** Combine with
`sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel` (excess `d_p` is forced
only at infinitely many levels of an infinite kernel) and
`sp21-pro-p-kernel-invisible-to-local-linear-reps` (the kernel has no linear
shadow). A certificate is a single cover where torsion-driven mod-p `H^1` is large
and `H^2` is small. Whether any Kazhdan group has such mod-p cohomology is the open
claim `kazhdan-group-with-golod-shafarevich-mod-p-cohomology`.

**Proof:** route `sp21-gs-certificate-shape-at-uniform-levels-proof`, artifact §5.
