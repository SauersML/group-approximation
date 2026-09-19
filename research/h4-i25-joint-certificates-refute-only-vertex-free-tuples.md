---
rg: 2
id: h4-i25-joint-certificates-refute-only-vertex-free-tuples
kind: claim
title: A joint I_2(5)-shadow certificate can refute a Case 1 tuple only if, for each hexagon vertex u_P, some shadow puts ρ_a(c_P) outside F_Y; double ejection is common, but every genuine tuple searched has a vertex pure centre, so no Π_ab mismatch occurs
distinct_from:
  h4-i25-two-flat-joint-centres-reduce-to-pencil-loops: that reduces a two-flat joint centre to matching of Π_ab-classes of the single-flat solution sets; this shows which tuples can fail the matching at all (vertex-free ones only) and runs the mismatch search.
  h4-i25-shadow-centre-forms-hold-only-up-to-rotation: that asks for vertex centres of the single-flat image hexagon; this gives the exact criterion for a vertex to be a pure centre in P, and its shadow form, and applies it to all three flats jointly.
---

**Setting.** Notation is as in `h4-i25-two-flat-joint-centres-reduce-to-pencil-loops` and
`h4-case1-pure-normal-form-and-fibred-obstruction`.
- A Case 1 tuple is `α_1, α_2 ∈ F`, `β_1, β_3 ∈ N` with
  `(*)  β_3^{-1}(α_1α_2)β_3 = α_1β_1α_2β_1^{-1}`, `α_1α_2 ≠ 1`, `β_1β_3 ≠ 1`.
  So `g_1 = 1`, `g_2 = α_1`, `g_3 = α_1β_1α_2` and `x_i = g_iA_X`.
- The hexagon vertices are `u_01 = 1`, `u_12 = α_1β_1`, `u_20 = β_3^{-1}`, each already adjacent (as `u_PA_Y`)
  to two of the `x_i`. Put
  `c_01 = β_1α_2β_1^{-1}`, `c_12 = β_1^{-1}α_1β_1`, `c_20 = β_3α_1β_3^{-1}`.
- `ρ_a : P → G_a = F_6 ⋊ B_a` (`a = 0,1,2`) are the three fibred `I_2(5)` shadows, and `F^{(a)}_Y = ρ_a(F)`.
- Double ejection: `p_{a+1}` is ejected in `V_a` and `p_{b+1}` in `V_b` (ejection-arc lemma of
  `h4-i25-shadow-hexagons-have-image-layer-centres`); `O_a` is the set of pairs that eject `p_{a+1}` in `V_a`.

**Theorem.**

**(V) Vertex criterion.** `u_PA_Y` is a pure centre (adjacent to `x_1, x_2, x_3`) iff
`c_01 ∈ P_YP_X`, `c_12 ∈ P_XP_Y`, `c_20 ∈ P_YP_X` respectively, where `P_YP_X = F·P_X`.
In particular `c_P ∈ F` suffices, and then `u_PA_Y = b_PA_Y` with
`b_01 = 1`, `b_12 = β_1`, `b_20 = β_3^{-1}`, all in `P_X`.
**Shadow form.** Each `ρ_a(c_P)` lies in the fibre `F_6`, and `F_6 ∩ F^{(a)}_Y B_a = F^{(a)}_Y`. So in the
`(★)` language of w10: `ρ_a(b_P) ∈ Sol_a` iff `ρ_a(c_P) ∈ F^{(a)}_Y`.

**(R) Reduction of every joint certificate.** Let `𝒱` be any family of the shadows. If one `P` has
`ρ_a(c_P) ∈ F^{(a)}_Y` for every `V_a ∈ 𝒱`, then `b_P ∈ P_X` is a joint centre for `𝒱`. The single-flat
solution sets then meet at `ρ_{ab}(b_P)` in every `B_{ab}`, and in particular in `Π_{ab}`. So the
`𝒱`-joint certificate can refute a tuple only if the tuple is **shadow-vertex-free**:
- for each `P ∈ {01,12,20}` some `a` has `ρ_a(c_P) ∉ F^{(a)}_Y`.

This covers the two-flat pencil-loop matching (ii) of w10 and its three-flat version. Being shadow-vertex-free
implies `c_P ∉ F` for all `P`.

**Computation (the step's search).** The brief asked for tuples with `p_c` ejected in both `V_a` and `V_b`,
and for a mismatch of the pinned `Π_ab`-classes.
- **Double ejection is common.** In the exact Garside searches:
  - `|α| ≤ 1`, `|β| ≤ 2`: 9312 genuine tuples, 1224 doubly ejected in `(V_1,V_2)`.
  - `|α| ≤ 2`, `|β| ≤ 1`: 2064 genuine tuples. Of these, 1328 are doubly ejected in `(V_1,V_2)`,
    40 in `(V_0,V_1)` and 64 in `(V_0,V_2)`, and 32 are ejected in all three flats.
  - Searches with `α_1` or `α_2` a zero-winding length-4 commutator `[p_i^{±1}, p_j^{±1}]`, the natural source
    of split patterns (every nonzero-winding ejection observed has `|O_p| = 3`): 280 + 88 genuine tuples,
    all doubly ejected in `(V_1,V_2)` (`E111.log`, `E211.log`).
- **No split pattern and no mismatch.** Every doubly ejected tuple has a common ejecting pair,
  `O_a ∩ O_b ≠ ∅`. On the 44 doubly ejected records tested with curver (`vcent.py`, `VIN.log`), some vertex
  `ρ_a(u_P)` is a centre in all three shadows. So the `Π_ab`-classes meet at `ρ_{ab}(b_P)` for every pair.
- **No vertex-free tuple.** `vsearch.py` hashes both sides of `(*)` by Burau matrices in all three shadows.
  Here `β` runs over words in the 9 N-letters visible in some shadow. Burau is a homomorphism, so there are
  no false negatives. It confirms each hit in the Artin action on
  `F_7`, then in `H_4` by Garside, then tests `c_P ∈ F` by Garside. Results:
  - `|α| ≤ 1`, `|β| ≤ 2`: 10160 genuine tuples (`VS12.log`).
  - `|α| ≤ 2`, `|β| ≤ 2`: 91360 genuine tuples, in three complete chunks (`VS22_{0,1,2}.log`).
  - `|α| ≤ 3`, `|β| ≤ 1`: 53156 genuine tuples, all with `c_01 ∈ F` (`VS31_{0,1}.log`).
  - `|α| ≤ 1`, `|β| ≤ 3`, partial: two of the three `α_1`-chunks, covering 4 of the 6 values of `α_1`, give
    14832 genuine tuples (`VS13_{1,2}.log`). The remaining chunk did not finish within the 1200 s limit.
  - Every genuine tuple found has a Garside-verified `c_P ∈ F`, hence a genuine pure centre.
    **0 vertex-free tuples.**
- **All solutions are the commuting family or its rotations.** At shadow level with `|α| ≤ 2`, `|β| ≤ 1`, all
  6908 solutions of `(*)` lie in the commuting family `β_1 ∈ C_N(α_2)`, `β_3 ∈ C_N(α_1α_2)` (centre
  `u_01 = 1`). With `|α| ≤ 1`, `|β| ≤ 2`, 1828 genuine solutions are not commuting, 168 of them nondegenerate. Each of
  these 168 has
  `c_12` or `c_20 ∈ F`: a centre at a rotated vertex.

**Consequence for the target.** The step's candidate mechanism, a pinned-class mismatch under double
ejection, does not occur in the searched range. The structural reason is (V) plus (R): each such tuple is
resolved by a hexagon vertex, which is a joint centre in every shadow at once. Multi-flat shadow
certificates are therefore confined to shadow-vertex-free tuples. The vertex-centre statement (VC), "every
genuine Case 1 tuple has a pure centre among `u_01, u_12, u_20`", would prove Case 1 of the target, and it
holds on everything searched. In the braid-group model it is known to need rotation
(`h4-i25-shadow-centre-forms-hold-only-up-to-rotation`), and here it holds after rotation.

**Status.**
- (V) and (R) are proved: direct proof in the `-proof` route.
- The computation is exact where it reports positives: Garside normal forms in `H_4`, and curver for the
  shadow centres.
- Its completeness within the stated word lengths rests on the Burau hash, which is necessary for `(*)`, and
  on `(*)` in `P` implying `(*)` in each shadow.
- Open: whether vertex-free tuples exist at all, at any length. (VC) is the concrete conjecture.

Lane w11-042, 2026-09-18.
