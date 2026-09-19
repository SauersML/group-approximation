---
rg: 2
id: thompson-f-z-wr-z-cosets-have-a-canonical-form
kind: claim
title: "The subgroup H = <x0, h> = Z wr Z of Thompson's F is the stabilizer of the tiling by x0-translates of [1/2,3/4] decorated with standard bumps, so every coset Hg has a unique computable representative in F"
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that shows F/H is amenable for every H containing an end-rigid stabilizer; this H = Z wr Z contains no rigid stabilizer at all, and the node is a normal form for its cosets, not an amenability statement.
  thompson-f-rigid-stabilizer-schreier-graphs-are-amenable: same distinction; H here is amenable and nowhere rigid.
  thompson-f-norm-bound-from-epg-32-term-moments: that bounds ||P_F|| from Cayley return moments; this node supplies the coset arithmetic that makes Schreier windows over an amenable subgroup computable, and records their measured price.
artifacts:
  - experiments/thompson-f-schreier-cosets-2026-09-17/cosets.py
  - experiments/thompson-f-schreier-cosets-2026-09-17/test_cosets.py
  - experiments/thompson-f-schreier-cosets-2026-09-17/test_cosets.json
  - experiments/thompson-f-schreier-cosets-2026-09-17/schreier_bfs.py
  - experiments/thompson-f-schreier-cosets-2026-09-17/bfs_R13.json
  - experiments/thompson-f-schreier-cosets-2026-09-17/window_eig.py
  - experiments/thompson-f-schreier-cosets-2026-09-17/window_eig_R13.json
  - experiments/thompson-f-schreier-cosets-2026-09-17/compare_cayley.py
  - experiments/thompson-f-schreier-cosets-2026-09-17/compare_cayley.json
  - experiments/thompson-f-schreier-cosets-2026-09-17/greedy_live.py
  - experiments/thompson-f-schreier-cosets-2026-09-17/greedy_live_f01.json
  - experiments/thompson-f-schreier-cosets-2026-09-17/greedy_live_f03.json
---

**ESTABLISHED** by `thompson-f-z-wr-z-cosets-have-a-canonical-form-proof` (by hand). The code is a direct
transcription of the normal form and is checked against an independent membership test.

**Setting.** `F` acts on `[0,1]`; `x_0` is `t/2` on `[0,1/2]`, `t − 1/4` on `[1/2,3/4]` and `2t − 1` on `[3/4,1]`.
The *tiles* are `I_k = x_0^k [1/2,3/4]`, `k ∈ Z`:
- `I_0 = [1/2,3/4]`;
- `I_k = [2^{−k−1}, 2^{−k}]` for `k ≥ 1`;
- `I_{−m} = [1 − 2^{−m−1}, 1 − 2^{−m−2}]` for `m ≥ 1`.

They tile `(0,1)` and `x_0` maps each `I_k` affinely onto `I_{k+1}`. For an interval `I` let `b_I` be the *standard
bump* on `I`: the conjugate of `x_0` by the affine increasing map `[0,1] → I`, extended by the identity. Put
`h = b_{I_0}` and `h_k = x_0^k h x_0^{−k} = b_{I_k}`. Then `H = ⟨x_0, h⟩ = (⊕_k ⟨h_k⟩) ⋊ ⟨x_0⟩ ≅ Z ≀ Z`,
which is metabelian, hence amenable.

**Theorem.** Let `ξ = {(I_k, h_k) : k ∈ Z}` and let `F` act on such decorated tilings by
`f·(J, a) = (f J, f a f^{−1})`.
1. `Stab_F(ξ) = H`.
2. `Hg ↦ g^{−1}·ξ` is a bijection from `H\F` onto the orbit `F·ξ`, intertwining right multiplication by `s` on
   cosets with the action of `s^{−1}` on tilings.
3. (Normal form.) Every left coset `fH` contains exactly one `f̂` such that
   - (N1) `f̂(I_0)` is the tile of `f·ξ` that contains `1/2` in its half-open interval `[p, q)`; and
   - (N2) for every `k`, the right slope of `f̂` at the left end of `I_k` equals
     `2^{⌊log_2(|f̂(I_k)| / |I_k|)⌋}`.

   It is `f̂ = f x_0^{k*} ∏_k h_k^{n_k}`, where `f^{−1}(1/2) ∈ I_{k*}` (half-open) and `n_k` is an explicit integer that
   vanishes on every tile on which `f x_0^{k*}` is affine. So `Hg ↦ (g^{−1})^` is a canonical, hashable form of the
   coset, computed with at most two compositions in `F`.

**The key step.** A PL dyadic homeomorphism `φ` of a tile `I` that commutes with `b_I` is a power of `b_I`. Compose
with the power of `b_I` that makes the slope at the left end equal to 1. The result is the identity near that end,
and `b_I`-orbits accumulate there. No root argument is needed, because the slopes are powers of 2.

**Checks (`test_cosets.py`, `test_cosets.json`).** 300 random checks of invariance, `canon(fη) = canon(f)` for random
`η ∈ H`, together with idempotence and membership of `canon(f)^{−1} f` in `H` by an independent tile test. By brute
force over the Cayley ball, the number of cosets met by `B_r` is 3, 9, 26, 74, 205, 562, 1523, 4109 for `r = 1..8`.
This agrees exactly with a BFS of the Schreier graph run on normal forms.

**Measured price, correcting the live-bus estimate.** `|H ∩ B_r|` is 3, 5, 7, 9, 11, 15, 25, 43 for `r = 1..8`. The
Schreier balls of `Sch(H\F, {x_0^{±1}, x_1^{±1}})` have sizes (`bfs_R13.json`)

`1, 3, 9, 26, 74, 205, 562, 1523, 4109, 10996, 29336, 77823, 205950, 542749` for `r = 0..13`.

The sphere ratio at `r = 13` is `2.63`, against about `2.8` in the Cayley graph at `r = 11`. It is not `1.85`: the
estimate `2.774/1.48` behind need 6a72890d divides growth rates, which is not how the size of a quotient ball
behaves. A Schreier ball of radius 27 would have about `10^11` vertices, not `10^7`.

**What the quotient does buy (floating point, scouting only).** `H` is amenable, so `ℓ²(H\F)` is weakly contained in
`λ_F`. Hence every Dirichlet eigenvalue of a finite window in the Schreier graph is a lower bound for `‖P_F‖`, and it
is at least the value on the corresponding Cayley ball.
- *Balls.* Schreier `B_11` gives `0.884556` on 77823 vertices, while Cayley `B_11` gives `0.86482` on 244823
  (`window_eig_R13.json`, `compare_cayley.json`). Schreier `B_13` gives `0.892944` on 542749 vertices.
- *Greedy Perron windows.* These grow `S` by the boundary vertices of largest Perron score (`greedy_live.py`,
  `greedy_live_f01.json`). They reach `0.896639` at `4·10^5` vertices.
- *Rate.* The gain is `0.0040` per e-fold of `|S|` and decays by about 5–10% per e-fold.
- *Extrapolation.* Crossing the certified `0.910677` would take roughly `10^7`–`5·10^7` vertices. That is out of reach
  in Python but plausible in compiled code. It is possible only if `‖P_{H\F}‖ > 0.910677`, which is not known.
- *Status of these numbers.* None of the window values is certified, and none beats the existing bound, so no
  certificate was produced.
