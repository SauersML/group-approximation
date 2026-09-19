---
rg: 2
id: sofic-normalization-fails-for-finite-index-kazhdan-pairs
kind: claim
title: In a sofic group a normally generating index-8 Kazhdan subgroup can have a centralizer its overgroup does not normalize, so the extrinsic-defect survivor needs a Kazhdan envelope of the whole compressor chain
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is the normalization theorem for infranormal Kazhdan pairs; this shows it fails once infranormality is dropped, already for an index-8, normally generating pair, and in the universal sofic group itself.
  sofic-groups-kill-rigid-compression-defects: that is the group-level kill for infranormal pairs; this is the matching calibration for the non-infranormal pair formed by a compressed subgroup and its overgroup, together with the closure lemma the kill yields for one compressor at a time.
  sofic-defect-cores-have-non-kazhdan-compressor-hull: that shows a surviving core has a non-Kazhdan compressor hull; this shows the compressed pair itself (both members Kazhdan, finite index) admits no normalization theorem, and identifies the Kazhdan envelope of the compressor chain as the hypothesis a kill must use.
  compression-defects-grow-under-centralizer-closure: that reduces extrinsic-defect witnesses to closed sources whose centralizer K does not normalize; this refutes the pairwise normalization theorem that node named as the missing input, and proves that closed sources are Kun--Thom saturated.
  sofic-non-mf-witness: that is soficity and non-MF of the Clifford witness W; this reads off from W the failure of pairwise centralizer normalization.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the open construction problem; this bounds which sofic normalization theorems could kill its survivors.
artifacts:
  - research/sofic-normalization-fails-for-finite-index-kazhdan-pairs-proof.md
  - research/sofic-non-mf-witness.md
  - research/sofic-groups-kill-rigid-compression-defects.md
  - research/compression-defects-grow-under-centralizer-closure.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED** (calibration plus reduction; proof: `sofic-normalization-fails-for-finite-index-kazhdan-pairs-proof`).

Notation.
- `Z(X) = C_G(X)`.
- `Comp_G(L) = {u : u L u^-1 <= L}`.
- The defect generators at a compressor `u` are `[u c u^-1, l]` with `c in C_G(L)` and `l in L`.

## Part A: calibration in the sofic Clifford witness

- `Gamma = Z^3 ⋊ SL_3(Z)`, written as affine pairs `(v, A)`.
- `alpha(v, A) = (2v, A)`.
- `Gamma' = alpha(Gamma) = 2Z^3 ⋊ SL_3(Z)`.
- `W = Cl(X) ⋊ V` is the finitely generated sofic witness of `sofic-non-mf-witness`, where
  - `V` is the ascending HNN extension of `Gamma` along `alpha`, with stable letter `t`;
  - `X = V/Gamma`;
  - `Cl(X)` is the Clifford lamp group.

Then:

1. **(F1) The pair.** `Gamma` and `Gamma'` have property (T), and `[Gamma : Gamma'] = 8`.
   - `<<Gamma'>>^Gamma = Gamma`.
   - `Comp_Gamma(Gamma') = Gamma'`, so `Gamma'` is not infranormal in `Gamma`.
2. **(F2) Group-level failure.**
   - `C_W(Gamma') ≠ C_W(Gamma) = C_W(<<Gamma'>>^Gamma)`.
   - `Gamma` does not normalize `C_W(Gamma')`.
   - Explicitly, let `x_0 = Gamma` be the root coset and `a = (e_1, I)`. Then `c_(t x_0)` centralizes `Gamma'`, but `a c_(t x_0) a^-1 = c_(a t x_0)` does not.
3. **(F3) Ultraproduct failure.** Let `σ : W -> S_U` be any injective homomorphism into the universal sofic group; one exists because `W` is sofic.
   - `σ(Gamma)` does not normalize `C_(S_U)(σ Gamma')`.
   - `C_(S_U)(σ Gamma') ≠ C_(S_U)(σ <<Gamma'>>^Gamma)`.
4. **(F4) No Kazhdan envelope.** No Kazhdan subgroup of `W` contains the compressor chain `T_alpha = ⋃_n t^-n Gamma t^n`.

So Kun--Thom Theorem 4.1 does not extend to Kazhdan pairs once infranormality is dropped, even under all three of the following:
- the index is finite;
- the small group normally generates the large one;
- the pair is `L_1 = u L u^-1 <= L`, cut out by a compressor.

The closure identity `C(Gamma') = C(<<Gamma'>>^Gamma)`, which drives every sofic kill in the extrinsic-defect lane, fails in the same way.

## Part B: what soficity does give, one compressor at a time

Let `G` be a countable sofic group and `L <= G`.

1. **(H) The Kun--Thom hull.** Let `Hull_G(L)` be the smallest subgroup `H >= L` with the following property: whenever `Gamma <= H` is Kazhdan, `Delta <= G` is Kazhdan, and `Gamma` is infranormal in `Delta`, then `<<Gamma>>^Delta <= H`. Then
   ```text
   C_G(Hull_G(L)) = C_G(L),   hence   Hull_G(L) <= C_G(C_G(L)).
   ```
2. **(HK) Per-compressor kill.** Let `u in Comp_G(L)`, and suppose `u^-n L u^n <= Hull_G(L)` for some `n >= 1`.
   - Then `u` normalizes `C_G(L)`.
   - So every defect generator at `u` is trivial.
3. **(HS) Closed sources are Kun--Thom saturated.** Let `G` have a normal Kazhdan subgroup `K` with `G/K = Z`, and let `L = C_K(C_G(L))` be a closed source in `K`.
   - Then `Hull_G(L) = L`.
   - So for every Kazhdan `Gamma <= L` and every Kazhdan `Delta` in which `Gamma` is infranormal, `<<Gamma>>^Delta <= L`.
   - In particular, if `L` is Kazhdan, then every Kazhdan subgroup in which `L` is infranormal normalizes `L`.
   - A strict compressor `u` satisfies `u^-n L u^n ⊄ L`, hence `⊄ Hull`, for every `n >= 1`.
4. **Calibration of (HK).** In `W`, the compressor `t` of `Gamma` carries the nontrivial generator `[t c t^-1, a]`. So `t^-n Gamma t^n ⊄ Hull_W(Gamma)` for every `n`, and (HK) is sharp.

## Consequence for the extrinsic route

Let `G = K ⋊ Z` be a sofic mapping torus with Kazhdan kernel, and let `L <= K` be Kazhdan. Every compressor chain `⋃_n u^-n L u^n` lies in the Kazhdan group `K`.

`W` has every other feature of such a configuration:
- a sofic ambient group;
- a Kazhdan source `L`;
- a compressor with `[L : u L u^-1] < ∞` and `<<u L u^-1>>^L = L`;
- a nontrivial defect.

What `W` lacks is exactly a Kazhdan envelope of the chain (F4). Therefore any kill of the survivors of `compression-defects-grow-under-centralizer-closure` must use the following statement, or something at least as strong:

```text
(CKN) If G is sofic, L <= G is Kazhdan, u in Comp_G(L), and ⋃_n u^-n L u^n lies in a
      Kazhdan subgroup of G, then u normalizes C_G(L).
```

No statement about the pairs `u^k L u^-k <= u^j L u^-j` alone can serve, because (F2)–(F3) refute every such statement. (CKN) would give `D_G(L) = 1` for every Kazhdan `L` in every sofic Kazhdan-kernel mapping torus, and would kill route (EK1) outright. (CKN) is OPEN.
