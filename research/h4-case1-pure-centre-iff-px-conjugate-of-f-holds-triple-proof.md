---
rg: 2
id: h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple-proof
kind: route
title: Coset algebra with the homomorphism ρ_X turns pure upper bounds into conjugates of F, and an exact Garside test for F settles the transporter data
target: h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple
requires:
  - h4-case1-pure-normal-form-and-fibred-obstruction
artifacts:
  - experiments/h4-vertex-centre-2026-09-18/fmem.py
  - experiments/h4-vertex-centre-2026-09-18/gens4.py
  - experiments/h4-vertex-centre-2026-09-18/transp.py
  - experiments/h4-vertex-centre-2026-09-18/triangle.py
  - experiments/h4-vertex-centre-2026-09-18/pairtr.py
  - experiments/h4-vertex-centre-2026-09-18/tri_diag.py
  - experiments/h4-vertex-centre-2026-09-18/vsearch3.py
---

Notation is as in the target. `θ : A → W` is the projection, so `P = ker θ`. Adjacency of `gA_X` and `hA_Y` means
`gA_X ∩ hA_Y ≠ ∅`, i.e. `g^{-1}h ∈ A_XA_Y`.

**Facts used.**
- (F1) `ρ_X : P → P_X` is a homomorphism restricting to the identity on `P_X`. It is induced by
  `M(𝒜) ⊂ M(𝒜_X)`, as in `h4-case1-pure-normal-form-and-fibred-obstruction`; it is also the Godelle–Paris
  retraction.
- (F2) `F = ker(ρ_X|P_Y)` and `P_Y = F ⋊ P_Z`, from the same node. Since `P_Z ⊆ P_X`, this gives
  `P_XP_Y = P_X F P_Z = P_X F` (as `F` is normal in `P_Y`, `FP_Z = P_ZF`). Likewise `P_YP_X = FP_X`.
- (F3) `N ⊆ P_X`. Hence `ρ_X(β) = β` for `β ∈ N`, and `ρ_X(α) = 1` for `α ∈ F`.

**Step 1: (M).**
- **`P ∩ A_XA_Y = P_XP_Y`.** Let `c = ab ∈ P` with `a ∈ A_X` and `b ∈ A_Y`. Then `θ(a) = θ(b)^{-1}` lies in
  `W_X ∩ W_Y = W_Z`. Choose `z ∈ A_Z` with `θ(z) = θ(a)`. Then `c = (az^{-1})(zb)`, where `az^{-1} ∈ P_X` and
  `zb ∈ P_Y`. The reverse inclusion is clear.
- **The criterion.** If `c = xf` with `x ∈ P_X` and `f ∈ F`, then `ρ_X(c) = x` by (F1) and (F3). So
  `ρ_X(c)^{-1}c = f ∈ F`. Conversely, `c = ρ_X(c)·(ρ_X(c)^{-1}c)`. The `F·P_X` case is the mirror image.

**Step 2: adjacency to `x_1` puts every pure bound in `P_X`.** Let `h ∈ P` with `hA_Y ~ x_1 = A_X`.
- By Step 1, `h = γf` with `γ = ρ_X(h) ∈ P_X` and `f ∈ F ⊆ A_Y`, so `hA_Y = γA_Y`.
- Conversely every `γA_Y` with `γ ∈ P_X` is adjacent to `x_1`.

So the pure bounds are the `γA_Y`, `γ ∈ P_X`, that are adjacent to `x_2` and `x_3`.

**Step 3: the two remaining adjacencies.** Write `g_2 = α_1` and `g_3 = α_1β_1α_2`, both pure.
- **`γA_Y ~ x_2`.** This holds iff `α_1^{-1}γ ∈ P_XF`. Now `ρ_X(α_1^{-1}γ) = γ`, so by Step 1 it holds iff
  `γ^{-1}α_1^{-1}γ ∈ F`, i.e. `e_0 ∈ γFγ^{-1}`.
- **`γA_Y ~ x_3`.** This holds iff `g_3^{-1}γ ∈ P_XF`. Now `ρ_X(g_3^{-1}γ) = β_1^{-1}γ`, so it holds iff
  `γ^{-1}β_1g_3^{-1}γ ∈ F`. Here `β_1g_3^{-1} = β_1α_2^{-1}β_1^{-1}α_1^{-1} = (e_0e_1)^{-1} = e_2`, so the condition is
  `e_2 ∈ γFγ^{-1}`.

Since `e_1 = e_0^{-1}e_2^{-1}`, the three memberships `e_0, e_1, e_2 ∈ γFγ^{-1}` follow from any two of them. This
proves (H).

**Step 4: (C) and (V′).**
- **`e_0` and `e_1`.** `e_0 = α_1 ∈ F = F_0`, and `e_1 = β_1α_2β_1^{-1} ∈ F_1`.
- **`e_2`.** Apply Step 3 with `γ = β_3^{-1}` (Step 3 used only `γ ∈ P_X`). So `x_3 ~ y_3` iff `e_2 ∈ F_2`. Under
  `(*)`, `β_3 e_2^{-1} β_3^{-1} = β_3α_1β_1α_2β_1^{-1}β_3^{-1} = α_1α_2 ∈ F`, so `e_2 ∈ F_2`.
- **`ρ_X(c_P) = 1`.** Each `c_P` is a `P_X`-conjugate of an element of `F`, so `ρ_X(c_P) = 1` by (F3). Step 1 then
  reduces `c_P ∈ F·P_X` (and `c_P ∈ P_X·F`) to `c_P ∈ F`.
- **`y_1` and `y_3`.** These are `γA_Y` with `γ = 1` and `γ = β_3^{-1}`.
- **`y_2 = α_1β_1A_Y`.** It is adjacent to `x_1` iff `α_1β_1 ∈ P_XF`. We have `ρ_X(α_1β_1) = β_1`, so this holds
  iff `c_12 = β_1^{-1}α_1β_1 ∈ F`. In that case `α_1β_1 = β_1c_12`, so `y_2 = β_1A_Y`.
- **Adjacency to `x_2`, `x_3`.** `y_2` is adjacent to both whatever `c_12` is: `β_1 ∈ A_X` and `α_2 ∈ A_Y`.
- **Conclusion.** Every hexagon vertex that is a pure centre is `γA_Y` with `γ ∈ {1, β_1, β_3^{-1}}`, and that
  `γ` satisfies (H). Conversely, if `γ ∈ {1, β_1, β_3^{-1}}` satisfies (H), then `γA_Y` is adjacent to `x_1, x_2, x_3`.
  For `γ = β_1` this uses `c_12 = β_1^{-1}e_0β_1 ∈ F`, so `γA_Y = y_2`.
- **The failure condition.** For `γ = 1` we already have `e_0 ∈ F_0`, so `γ = 1` fails iff `e_1 ∉ F_0`. For
  `γ = β_1` we have `e_1 ∈ F_1`, so it fails iff `e_0 ∉ F_1`. For `γ = β_3^{-1}` we have `e_2 ∈ F_2`, so it fails iff
  `e_0 ∉ F_2`. This proves the stated form of VC-failure.

**Step 5: exact test for `F` (`fmem.py`).** Let `g ∈ P` have left normal form infimum `inf g`, and put
`K = ⌈max(0, −inf g)/2⌉`.

(a) **`g ∈ A_Y` iff `Δ_Y^{2K}g ∈ A_Y^+`.**
- The "if" direction is clear.
- For "only if", let `g = a^{-1}b` be the unique left-coprime fraction with `a, b ∈ A^+`. If `g ∈ A_Y`, its
  `A_Y`-fraction is left-coprime in `A` as well, because `A_Y^+` is closed under divisors in `A^+`. So by uniqueness
  `a, b ∈ A_Y^+`.
- Next, `a` divides `Δ^{−inf g}`, so `sup(a) ≤ −inf g ≤ 2K`. Normal forms of `A_Y^+`-elements agree in `A_Y` and `A`,
  so `a` divides `Δ_Y^{2K}` in `A_Y^+`. As `Δ_Y^2` is central in `A_Y`, `Δ_Y^{2K}a^{-1}b` is positive.
- Finally, a positive element is in `A_Y^+` iff every factor of its normal form has support in `Y`.

(b) **Membership in `F`.** On `P_Y`, `ρ_X` agrees with forgetting strand 1 of the pure braid group `P_4 = P_Y`.
Both kill `p_1, p_2, p_3` and fix `P_Z`, and `P_Y = ⟨p_1, p_2, p_3⟩ ⋊ P_Z`. So `g ∈ F` iff (a) holds and the
3-strand braid left after forgetting strand 1 is trivial. The script decides this in Garside normal form in `A_2`.

The self-test in `fmem.py` confirms `p_1`, `p_2`, `p_3` and `p_1p_2^{-1}p_3 ∈ F`. It also confirms `s_4^2 ∉ F`,
`s_2^2 ∉ F` and `p_1s_2^2 ∉ F`, which checks the expected answers of the test.

**Step 6: (T).** Run `fmem.py`: `x_0p_3x_0^{-1}, x_0p_2x_0^{-1} ∈ F` and `x_0p_1x_0^{-1} ∉ F`, for `x_0 = s_4^2 ∈ N`.
- **Why this breaks the free-product argument.** Suppose `F_i ≠ F_j` were free factors of a free product. Then
  `e_0e_1e_2 = 1` with the `e_i` in distinct factors forces all `e_i = 1`. If two of the `F_i` coincide, it forces the
  third `e_i` to be trivial, so all three lie in one `F_j`.
- **Why it fails here.** (T) exhibits `F ≠ x_0Fx_0^{-1}` with nontrivial intersection, which no free-factor system
  allows.

**Step 7: searches (evidence only).** `transp.py LG LF` lists transporters `T(g) = {f : gfg^{-1} ∈ F}` over short
words.
- **Transporter census (LG = 2, LF = 1, `T21.log`).** Of the 900 words of length ≤ 2 in `N ∪ Z`-meridians, 176 have
  nontrivial `T`.
  - `p_1` is transported only by `x_1z_3` (together with `p_3`) and by `x_4z_{23}`.
  - `p_2` is transported by `x_{11}z_2`, `x_4z_2`, `x_5z_2` and by `x_0`-words.
- **Triangle search (`triangle.py 2 1`).** It builds VC-failures from `q ∈ F_0∩F_1∖F_2`, `p ∈ F_0∩F_2∖F_1` and
  `β_1fβ_1^{-1} ∈ F_1∩F_2∖F_0`, then re-verifies `(*)` and all three `c_P ∉ F`.
  - Result: **0** hits.
  - The obstacles (`tri_diag.py`): the `q/p` step fails 29008 times, `T(β_3β_1)` is empty 1904 times, and `r ∈ F_0`
    occurs 64 times.
- **Pair-twist search (`pairtr.py 2`).** It looks for conjugators transporting a two-letter `u^{±1}v^{±1}` but
  neither `u` nor `v`, which a flower needs. Result: **0** among 900 conjugators (`PAIR2.log`).
- **Vertex search `|α| ≤ 1`, `|β| ≤ 3` (`vsearch3.py`).** This is `vsearch.py` of
  `experiments/h4-two-flat-pencil-matching-2026-09-17` with the loops over `α_2` and `β_1` chunked. Its centre test uses
  `F`-words of length ≤ 5, so a reported vertex centre is certified, and an unreported one would only be a candidate.
  - **Earlier runs.** `VS13_1.log` and `VS13_2.log` covered `α_1` indices `1, 4` and `2, 5`.
  - **This run.** `VS13_a{0,3}_b*.log` covers the 10 off-diagonal pairs with `α_1 ∈ {0, 3}`: 2040 genuine tuples, each
    with a vertex centre (`c_01` 224, `c_12` 1488, `c_20` 328), and 0 `NOVERTEX`.
  - **Not finished.** The pairs `(0,0)` and `(3,3)`, i.e. `α_1 = α_2 = a^{±1}`, time out even when `β_1` is split four
    ways. For `β_1, β_3` in the centraliser `C(a)`, `(*)` holds identically and `c_01 = a ∈ F`, so these runs are
    dominated by tuples that trivially have a vertex centre.
