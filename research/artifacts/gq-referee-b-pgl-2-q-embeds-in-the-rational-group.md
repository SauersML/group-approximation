# Referee report (citation lens, with proof check): `pgl-2-q-embeds-in-the-rational-group` and `aff-q-embeds-in-aut-v`

Referee: lane gq-referee-b, 2026-09-18. Reviewed: the claim and its `-proof`, and the OPEN node, as landed at
d43f85bec (gq-deep-free-3).

## Verdict

**PASS for both.** For the OPEN node, this covers its "established facts". Every citation is used within its
hypotheses, and every proof step checks.

## Citations

- **BBMZ criterion.** Recorded verbatim from the arXiv:2309.06224v3 TeX in
  `bh-rational-similarity-hosts-2026-09-12.md` §3.
  - Line 335 defines local actions through the smallest cone `C_{f̄(α)} ⊇ f(C_α)`, with
    `f(α·ω) = f̄(α)·f|_α(ω)`.
  - Line 363: "A map is rational if it has only finitely many distinct local actions."
  - That is BBMZ's **definition** of rational, stated for maps of shifts of finite type. It applies verbatim to
    homeomorphisms of the full binary shift, and `R_{Γ,E}` for `E = {0,1}^ℕ` is the rational group.
  - The node's "iff" is correct as a definition.
- **Belk–Matucci–Hyde**, *On the asynchronous rational group*, arXiv:1711.01668, abstract, verbatim: "We prove that
  the asynchronous rational group defined by Grigorchuk, Nekrashevych, and Sushchanskii is simple and not finitely
  generated."
  - That is the binary rational group `R`, so item 2 **matches**.
  - Cite the title as above. The paper's author order is Belk, Matucci, Hyde.
- **The identification of `S_2` with standard `V`** (required node, item 3).
  - The Farey coding is self-similar: the children of `C_w` are `S_wL, S_wR`, so the code of `S_w(x)` is `w`
    followed by the code of `x`. The canonical similarity `αω ↦ βω` is therefore `S_βS_α^{-1}`, and prefix
    replacements are exactly the piecewise `S_βS_α^{-1}` maps: standard `V`.
  - Infinite words converge to irrationals, or to one-sided rationals. For example `R^∞ ↦ ∞^-` and
    `LR^∞ ↦ 1^-`, so each rational is doubled. That gives the Stone space `S_2`.
  - I did not review the required node's own proof.
- **`aff-q-embeds-in-aut-v`.**
  - Rubin's theorem (`Aut(V)` equals the normalizer of `V` in `Homeo(C)`) and the Bleak–Cameron–Maissel–Navas–Olukoya
    description (`Out(V) ≅ O_2`, bi-synchronizing transducers) are correctly marked "not re-read at the source".
  - Higman's `Q ⊄ V` is survey arXiv:2306.16356v3, Theorem 4.4: "In particular, Q does not embed into V". I checked
    it against the survey text.
- **Raney (1973).** Cited, not read, and not used. That is fine.

## Proof checks

**Step 1.**
- Deep cones avoid the two rational cutting points in their interiors, since Stern–Brocot depth is finite.
- `N = S_u^{-1}M_0S_w` is primitive integral with `det N = D`, because the content is `SL_2(Z)`-invariant.
- The local action is determined by `N`.
- **Correct.**

**Step 2.** `N([0,∞]) ⊆ [0,∞]` with no zero or pole in `(0,∞)`, so all coefficients are `>= 0` after a sign.
Maximality means the image lies in neither child. **Correct.**

**Step 3.**
- For `D > 0`, the image is `[(b/d)^+, (a/c)^-]`. The conditions `a/c > 1` and `b/d < 1` are strict:
  `a/c = 1` would put the image inside `[0^+,1^-]`.
  - So `a >= c+1` and `d >= b+1`, hence `b + c + 1 <= D` and `a, d <= D + (D−1)^2`.
- `D < 0` is symmetric.
- There are finitely many `N`, plus finitely many exceptional `w`. **Correct.**

**Homomorphism and faithfulness.** It is faithful on the irrationals. **Correct.**
`BS(1,m) = ⟨x+1, mx⟩ ≅ Z[1/m] ⋊ Z`.

**Item 3.** Distinct `N` give distinct local actions, because a local action determines the Möbius map on a dense set.
Determinants `2^k` are unbounded, so the nucleus is infinite. **Correct.**

**Item 4.** This is analytic continuation: Möbius maps agreeing on an arc are equal. **Correct.**

**Item 5.**
- `M_2AM_2^{-1}(x) = 2x/(x+2)`, i.e. `[[2,0],[1,2]]`, primitive of determinant `4`, so it is not in `PGL_2(Z)`.
- Elements of `V` are piecewise `S_βS_α^{-1} ∈ PSL_2(Z)`, so no element of `V` agrees with it on an arc.
- **Correct.**

**Fact 1 of the OPEN node.**
- `gt_cg^{-1}t_c^{-1} = t_{(a−1)c}`, and conjugating `t_b` by dilations gives every `t_{ab}`. So every nontrivial
  normal subgroup of `Aff(Q)` contains `Q`.
- `Q ⊄ V`, so `Aff(Q) ∩ V = 1`, and `Aff(Q) ↪ Out(V)`.
- **Correct.**

## Remark (not an amendment)

Items 1–2 give, unconditionally, that `Aff(Q)`, `PSL_2(Q)` and `BS(1,m)` embed in a simple group that is not finitely
generated. As the node says, this is no progress on finite presentation, since `R` is not finitely generated.
