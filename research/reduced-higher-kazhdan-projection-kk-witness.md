---
rg: 2
id: reduced-higher-kazhdan-projection-kk-witness
kind: claim
title: Higher Kazhdan projections are the reduced analogue of Kazhdan projections, and a gapped Laplacian with non-integer l2-Betti number over a torsion-free group refutes Kadison--Kaplansky, Strong Atiyah and Baum--Connes at once
distinct_from:
  subgroup-average-projections-give-no-reduced-bc-obstruction: that shows classical Kazhdan projections of infinite subgroups vanish in C*_r; this records the degree-n projections that survive in M_k(C*_r G) under a reduced spectral gap, and what a non-integer trace of one would refute.
  fractional-matrix-trace-gives-projection-in-g-star-z: that is the general matrix-to-scalar passage; this is its sharpest geometric instance, where the matrix projection is a higher Kazhdan projection whose trace is an l2-Betti number.
  lueck-surjective-assembly-traces-lie-in-lambda-g: that is the trace ring under surjective assembly; this applies it, through Li--Nowak--Pooya, to l2-Betti numbers of groups with a spectral gap.
---

**ESTABLISHED** by `reduced-higher-kazhdan-projection-kk-witness-proof`.

**Setting.** `G` is of type `F_(n+1)`, and `Δ_n = d_n^* d_n + d_(n-1) d_(n-1)^* ∈ M_k(Z[G])` is the
degree-`n` Laplacian of a `K(G,1)` with finite `(n+1)`-skeleton.

**What lives in `C*_r`.** Classical Kazhdan projections do not survive:
- for infinite `G`, `λ(p_0) = 0` in `C*_r(G)`;
- more generally Kazhdan projections of infinite subgroups vanish, by
  `subgroup-average-projections-give-no-reduced-bc-obstruction`.

What survives are Li--Nowak--Pooya's higher Kazhdan projections:
- if `0` is isolated in `spec(Δ_n)` in `M_k(C*_r G)`, then `p_n = χ_{0}(Δ_n) ∈ M_k(C*_r G)`;
- `τ_*[p_n] = β^n_(2)(G)`, and `[p_n] ≠ 0` whenever `β^n_(2)(G) ≠ 0`.

**Theorem.** Let `G` be torsion-free of type `F_(n+1)`, with `0` isolated in the reduced spectrum of
`Δ_n` and `β^n_(2)(G) ∉ Z`. Then:
1. `C*_r(G * Z)` contains a projection of trace `β^n_(2)(G) - floor(β^n_(2)(G))`, so
   `kadison-kaplansky-torsion-free` fails on the torsion-free group `G * Z`;
2. if `C*_r(G)` is selfless, `C*_r(G)` itself contains such a projection;
3. `G` refutes Strong Atiyah over `Q`, since `Δ_n` is an integral matrix with kernel dimension
   `β^n_(2)(G) ∉ Z`;
4. assembly is not surjective for `G`.

So a higher-Kazhdan witness to Kadison--Kaplansky is a simultaneous counterexample to three
conjectures. It must live outside every class where Strong Atiyah over `Q` is established for
torsion-free groups.

**Model tests.**
- `F_m`, `n = 1`: Li--Nowak--Pooya record that `p_1 ∈ M_k(C*_r F_m)` exists, with
  `β^1_(2)(F_m) = m - 1 ∈ Z`. No counterexample, as it must be.
- For infinite `G`, degree `0`: `p_0 = 0` and `β^0_(2)(G) = 0`.
- A spectral gap alone does not suffice: every known torsion-free example with a gap has integer
  `l²`-Betti numbers.

**Credit.** The higher Kazhdan projections, their traces and the Baum--Connes consequence are
Li--Nowak--Pooya (arXiv:2006.09317). Items 1 and 2 add the Kadison--Kaplansky conclusion through
`fractional-matrix-trace-gives-projection-in-g-star-z` and
`selfless-projection-traces-equal-k0-trace-image`.
