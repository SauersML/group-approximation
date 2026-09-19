---
rg: 2
id: monomial-renormalization-compiler-gives-dilation-groups-in-nv
kind: claim
title: Several SMART odometers under one product or block-rotating code put Z^d[1/M] semidirect <M> into a Brin-Thompson group for every odd monomial dilation M
distinct_from:
  bs-1-m-embeds-in-brin-thompson-3v-for-odd-m: that is d = 1; this is every block-companion matrix M of odd dilations, including several primes under one stable letter and radical dilations such as sqrt(3).
  bs-1-minus-m-embeds-in-brin-thompson-3v-for-odd-m: that treats the sign; this treats rank and several heights at once.
---

**ESTABLISHED** through `monomial-renormalization-compiler-proof`. Elementary lane proof
(bh-invent-08), not reviewed. It rests on the lane-proved SMART_m nodes and on
`brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups`. No priority claimed.

**Input.** For every odd `m >= 3`, `odd-smart-induced-map-has-height-m-renormalization` gives
`T_m ∈ 2V` that is an odometer of an `m`-ary brick code `e^{(m)}` on `C^2`, so `T_m^m e^{(m)}_i = e^{(m)}_i T_m`.

**Theorem.** Take odd `m_1, …, m_r >= 3` and integers `d_1, …, d_r >= 1`, with `d = Σ d_c`. Let `M` be
the block matrix `⊕_c Comp(x^{d_c} - m_c)`, where `Comp` is the companion matrix. Let `α_c` be a
root of `x^{d_c} = m_c` and `R_c = Z[x]/(x^{d_c} - m_c)`. Then the group

  `Γ_M = Z^d *_M ≅ (⊕_c R_c[1/m_c]) ⋊ ⟨t⟩`,  with `t` acting as multiplication by `(α_1, …, α_r)`,

embeds in `(2d+1)V ⋊ Sym(2d)`, and in `(2d+1)V` itself when every `d_c = 1`. So every `Γ_M`
satisfies permutational Boone–Higman.

**Instances.**
- **Diagonal (all `d_c = 1`).** For example `(Z[1/3] ⊕ Z[1/5]) ⋊ ⟨t⟩ ≤ 5V`, with `t` dilating the two
  summands by 3 and by 5. This puts two different odd primes under ONE stable letter, where before
  there was one `BS(1,p)` per prime.
- **Radical (`r = 1`, `d_1 = d`).** `Z[m^{1/d}, 1/m] ⋊ ⟨m^{1/d}⟩ ≤ (2d+1)V ⋊ C_d`, for example the
  `√3`-dilation group `Z[√3, 1/3] ⋊ ⟨√3⟩`. It contains `BS(1,m) = ⟨T_1, t^d⟩` with index `d`, and that
  subgroup lies in `(2d+1)V`.
- **Calibration.** `d = r = 1` is `BS(1,m) ≤ 3V`.

**Scope.** These groups are linear, so Boone–Higman itself was known for them. What is new is that
they sit in the untwisted Brin–Thompson family (up to a finite coordinate permutation), and the
mechanism: realizing `M` needs no new machine, only a new code built from existing odometers.

**Lesson for general BH.** Once one odometer has been compiled, a whole algebra of dilations is
free. Products of codes add heights (`diag`), and a global coordinate rotation composed with one code
realizes companion matrices, i.e. radical dilations. What remains hard is not rank but PARITY and
HIERARCHY:
- even heights (`BS(1,2)`) need an even-branching machine;
- stacked power-conjugacies (BS chains, Higman's and Baumslag–Gersten's cycles) are blocked for the
  compiler itself by `compiled-bs-stable-letters-are-never-rediagonalized`.
