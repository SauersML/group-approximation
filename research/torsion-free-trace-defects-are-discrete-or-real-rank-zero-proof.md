---
rg: 2
id: torsion-free-trace-defects-are-discrete-or-real-rank-zero-proof
kind: route
title: Subgroups of R containing Z are (1/m)Z or dense; the free product computes the projection traces, and density is real rank zero
target: torsion-free-trace-defects-are-discrete-or-real-rank-zero
requires:
  - free-product-kk-iff-trace-conjecture-for-factors
  - reduced-free-product-k0-generated-by-factor-images
  - selfless-real-rank-zero-iff-dense-k0-traces
  - non-dihedral-free-products-are-completely-selfless
  - amalgam-torsion-permanence-needs-no-cyclic-reduction
---

**Arithmetic.** `S` is a subgroup of `R` containing `τ_*[1] = 1`. A subgroup of `R` is either discrete, hence
cyclic, or dense. A cyclic subgroup containing `1` is `(1/m)Z` for some `m >= 1`. So exactly one of the
three cases occurs.

**Trace image of the free product.** By `reduced-free-product-k0-generated-by-factor-images`,
`τ_*(K_0(C*_r(G * Z))) = S + Z = S`.

**Cases 1 and 2.** By `free-product-kk-iff-trace-conjecture-for-factors`, the projection traces of
`C*_r(G * Z)` are `S ∩ [0,1]`.
- If `S = Z`, the only traces are `0` and `1`, and the faithful trace forces the projection to be `0` or `1`.
- If `S = (1/m)Z` with `m >= 2`, the traces are `k/m`. The trace `1/m` is attained, so some projection is
  nontrivial. `G * Z` is torsion-free by `amalgam-torsion-permanence-needs-no-cyclic-reduction`.
- In either case the projection traces are not dense in `[0,1]`. The element `λ(z) + λ(z)^*`, with `z` the
  generator of `Z`, has atomless arcsine spectral measure. So item 2 of
  `selfless-real-rank-zero-iff-dense-k0-traces` shows `RR(C*_r(G * Z)) != 0`. The algebra is selfless by
  `non-dihedral-free-products-are-completely-selfless`.

**Case 3.** `S` is dense, so `τ_*(K_0(C*_r(G * Z)))` is dense. The algebra is selfless, so item 1 of
`selfless-real-rank-zero-iff-dense-k0-traces` gives `RR(C*_r(G * Z)) = 0`.

**Corollary, (a) ⇒ (b).** If `S` is not discrete it is dense (case 3), and `G * Z` is a countable
torsion-free group with `RR(C*_r(G * Z)) = 0`.

**Corollary, (b) ⇒ (a).**
- Let `Λ` be countable torsion-free with `RR(C*_r Λ) = 0`. Then `Λ != 1`, since `C*_r(1) = C` has real rank
  zero but trace image `Z`. Discard that case, since it does not satisfy (a).
- Pick `g ≠ e`. The squeeze in item 2 of `selfless-real-rank-zero-iff-dense-k0-traces-proof` uses only
  `RR = 0`, the faithful trace of the von Neumann closure, and the atomless element `λ(g) + λ(g)^*`, not
  selflessness. So the projection traces of `C*_r(Λ)` are dense in `[0,1]`, and `τ_*(K_0(C*_r Λ))` is
  dense, hence not discrete.

**Both refute the root.** In case 3, and under (b), `C*_r` of a torsion-free group has projections with
traces dense in `[0,1]`, so it has nontrivial projections.

**Model tests.** `K_0(C*(C_n)) = Z^n`, spanned by minimal projections of trace `1/n`. The free product
`*_(n>=2) C_n` is a directed union of finite free products, and `K_0` and the trace pass to the limit. Its
trace image therefore contains every `1/n` and is dense.
