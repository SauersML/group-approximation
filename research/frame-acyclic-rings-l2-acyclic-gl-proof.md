---
rg: 2
id: frame-acyclic-rings-l2-acyclic-gl-proof
kind: route
title: Frame stabilizers are unipotent-by-GL with infinite abelian radical, so the stabilizer count applies
target: frame-acyclic-rings-have-low-degree-l2-acyclic-gl
requires: [l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers, l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup]
artifacts:
  - research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md
---

Artifact Section 2, then Theorem D with `m = r-3`.
- **Lemma 2.1.** `g e_i = e_i` for `i <= k` forces `g = [[I_k, b],[0, d]]` with
  `d in GL_(r-k)(A)`. The kernel of `g ↦ d` is `U ≅ (M_(k x (r-k))(A), +)`, abelian, and
  infinite once `k <= r-1`. Cheeger--Gromov gives `β_*^(2)(J) = 0`.
- **Lemma 2.2.** A frame `(v_1..v_k)` with complement `C ≅ A^(r-k)` is `g(e_1..e_k)` for the
  matrix `g` sending the standard basis to `v_1..v_k` and a basis of `C`, so its stabilizer is
  `gJg^(-1)`. Ordered frames are fixed pointwise.
- A `p`-simplex with `p <= r-3` has `k = p+1 <= r-2` vectors. So every `E^1` term in total
  degree `<= r-3` comes from a stabilizer with all L²-Betti numbers zero.
