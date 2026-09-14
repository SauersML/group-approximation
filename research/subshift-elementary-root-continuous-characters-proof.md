---
rg: 2
id: subshift-elementary-root-continuous-characters-proof
kind: route
title: Split a root element into Kakutani–Rokhlin blocks, apply the Carderi–Thom lemma inside SL_n(F_{2^k}), and use simplicity
target: subshift-elementary-root-continuous-characters-are-trivial
requires:
  - carderi-thom-almost-invariant-psd-on-sl-n-is-near-trivial
  - simple-kazhdan-lef-group-from-minimal-subshift
artifacts:
  - research/artifacts/sk-characters-root-continuity-2026-09-13.md
---

The full derivation is in `research/artifacts/sk-characters-root-continuity-2026-09-13.md` §2. Outline, for a fixed nonempty clopen `B`:
1. **Blocks.** Take a Kakutani–Rokhlin partition whose base `b` has `‖b‖ ≤ 1/J`, refined so that each level lies in `B` or is disjoint from it. In each column, split the levels inside `B` into `K = kK'` classes of equal size. This gives `K` pairwise equivalent clopen pieces covering `B' ⊆ B`, and a remainder `E = B ∖ B'` with `‖E‖ ≤ K/J`.
2. **A finite group.** The partial isometries `e_{T^{a'}C}u^{a'−a}` between levels give matrix units `v_{ij}`, `1 ≤ i,j ≤ K`. The resulting copy of `GL_{3K}(F_2)` lies in `G`: transvections are `e_pq(v_{ij})` or `[e_pr(v_{ij}), e_rp(v_{jj})]`.
3. **Two elements of S.** Group the pieces in blocks of `k` and write `S = SL_{3K'}(F_{2^k})` by restriction of scalars. Then `e_12(e_{B'})` lies in `S`, and so does the non-central transvection `e_12(e_P)`, where `P` is one block and `‖P‖ ≤ 1/K'`.
4. **Lemma 1.4.** Apply Carderi–Thom's lemma to `χ` restricted to `S`, a class function. It gives `|1 − χ(e_12(e_{B'}))| < 9(2ε + 16/2^k)^{1/2}` whenever `|1 − χ(e_12(e_P))| < ε`.
5. **The remainder.** The positive-definite inequality `|ψ(g) − ψ(h)|² ≤ 2(1 − Re ψ(g^{-1}h))` compares `e_12(e_B)` with `e_12(e_{B'})` through `e_12(e_E)`.
6. **The limit.** Let `ε → 0`, `k → ∞`, `K' → ∞` and `J → ∞`, keeping `J > 2K/inf_μ μ(B)` so that `P ≠ ∅`. Then `χ(e_12(e_B)) = 1`.
7. **Kernel.** In the GNS representation `π(e_12(e_B)) = 1`, so `ker π` is a normal subgroup containing a non-central element. Simplicity gives `ker π = G`, so `χ ≡ 1`.
