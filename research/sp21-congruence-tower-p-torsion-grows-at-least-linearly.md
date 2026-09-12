---
rg: 2
id: sp21-congruence-tower-p-torsion-grows-at-least-linearly
kind: claim
title: Along uniform p-adic congruence towers of an Sp(n,1) lattice the p-part of H_1 is at least the index times p^D, and exceeds the congruence abelianization only through the pro-p congruence kernel
distinct_from:
  sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel: that is about mod-p Betti numbers along the derived p-series and when they detect a finite kernel; this bounds the order of p-primary torsion in H_1 along congruence towers
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**ESTABLISHED.** Setting as in
`sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel`: `Δ <= Γ(p)` has uniform
closure `U` of dimension `D`, `P = Δ̂_p`, and `N` is the pro-p congruence kernel.
Put `U_m = U^(p^m)`, `Δ_m = Δ ∩ U_m` and `P_m = π^(-1)(U_m)`. Then for every
`m >= 0`:

```text
p^D · [Δ:Δ_m]  <=  |U_m^ab|  <=  |H_1(Δ_m;Z)_(p)|  <=  |U_m^ab| · |N / closure[N,P_m]|.
```

Along the derived p-series `D_i` of `Δ`:
- `|H_1(D_i;Z)_(p)| >= p^(D(i+1))` for every `i`;
- if `N` is finite, then for all large `i`, `H_1(D_i;Z)_(p) ≅ U_i^ab` and
  `[Δ:D_i] = |N|·p^(Di)`.

**What it says about torsion growth.**
- **Unconditionally:** p-primary torsion in `H_1` grows at least linearly in the
  index along uniform congruence towers.
- **Under the congruence subgroup property at `p`** (a finite pro-p kernel): the
  p-part of `H_1` is the abelianization of the congruence group, up to the
  bounded factor `|N|`.
- **Refutation shape:** unbounded excess of `|H_1(Δ_m;Z)_(p)|` over `|U_m^ab|` would
  make `N` infinite, and so refute
  `sp21-lattice-pro-p-completions-have-finite-rank`. No finite computation shows
  unboundedness.
- **Consistency.** The lower bounds put `log|H_1(-;Z)_(p)|` at about the logarithm
  of the index, far below the index. That is compatible with the
  Bergeron–Venkatesh conjecture for `δ(Sp(n,1)) = 0` (arXiv:1004.1083, Conjecture
  1.3, read from the PDF), which predicts `o(index)` torsion.
  - No source read proves a torsion-growth statement for these lattices with
    trivial coefficients.
  - No upper bound on `|U_m^ab|` is proved here.

**Proof** (route `sp21-congruence-tower-p-torsion-grows-at-least-linearly-proof`,
artifact §3 (c)–(d)):
- By (T), `H_1(Δ_m;Z)` is finite. Its p-part is `P_m^ab`, which maps onto `U_m^ab`
  with kernel the image of `N`.
- `[U_m,U_m] <= U_(2m+1)` bounds `|U_m^ab|` below by `p^(D(m+1))`.

No novelty claimed.
