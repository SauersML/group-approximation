# Referee report (gq-referee-a, proof-gap lens): SL_2(Q) through a Hecke overgroup and BLIW

**Reviewed:** the route `sl-2-q-via-hecke-overgroup-and-bliw` (lane gq-infinite-primes, 39b37d26f)
and the hypotheses (H1)–(H4) of `sl-2-z-localized-has-fp-hecke-overgroup`, read on origin/main.

**Verdict: PASS for the implication.** (H1)–(H4) imply that `SL_2(Q)` embeds in a finitely presented
simple group. The hypothesis claim itself is OPEN.

## Conventions
- `Z_(l)` inverts every prime except `l`.
- With `α = diag(1, l)`, `α [[a,b],[c,d]] α^{-1} = [[a, b/l],[lc, d]]`. So `A ∩ A^α = Γ_0(l)` and
  `α^{-1} Γ_0 α = Γ^0`, matching the definitions.
- The amalgam `SL_2(Q) = A *_{Γ_0} A^α` is Ihara–Serre for the `l`-adic valuation on `Q`, with valuation
  ring `Z_(l)`.

## Step 1 (BLIW)
- `K` lies in `BS_Λ`. It is the HNN extension with vertex group `Λ` and edge group `C_1`, and both
  edge maps `C_1 → Λ` and `φ: C_1 → C_2 ≤ Λ` have finite index. Hence all groups involved are
  commensurable with `Λ`.
- Theorem C of BLIW, as quoted verbatim in `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`,
  needs exactly two things: `Λ` finitely presented, and some nontrivial `H ∈ BS_Λ` acting faithfully
  on its Bass–Serre tree. The second is (H4).
- Conclusion: every `K ∈ BS_Λ` embeds in a finitely presented simple group. The hypotheses match.

## Step 2 (injectivity)
- **The map is well defined.** For `z ∈ Γ_0`, `y = α^{-1} z α ∈ Γ^0`, so `ι(y) ∈ C_1` by (H1). Then
  `t ι(y) t^{-1} = φ(ι(y)) = ι(z)` by (H3).
- **The amalgam `Λ *_{C_2} tΛt^{-1}` embeds in `K`.** In a reduced word, the odd letters lie in
  `Λ \ C_2` and the even ones in `Λ \ C_1`.
  - A pinch `t^{-1} c t` needs `c ∈ C_2`, and a pinch `t c t^{-1}` needs `c ∈ C_1`, so there are none.
  - Britton's lemma then applies, and words of length 1 are trivially nontrivial.
- **The intersections match.** `ι(A) ∩ C_2 = ι(Γ_0)` by (H2). Also
  `tι(A)t^{-1} ∩ tC_1t^{-1} = tι(Γ^0)t^{-1}` by (H1), and this equals `ι(Γ_0)` by (H3).
- **Sub-amalgam lemma.** It is standard: an alternating word in `X \ Z` and `Y \ Z` is reduced.
- **Conclusion.** `Ψ` restricts to isomorphisms on both factors that agree on `Γ_0`. So it is the
  isomorphism onto `ι(A) *_{ι(Γ_0)} tι(A)t^{-1} ≤ K`. Correct.

## On the OPEN hypothesis (not a verdict)
- The necessary conditions stated are correct. `Λ` must be residually finite, because vertex
  stabilizers of a faithful action on a locally finite tree embed in a profinite group, and
  commensurability preserves this. `Λ` must also be non-linear, by the reviewed obstruction in the
  companion report.
- The Serre calibration with `SL_2(Z)` and `Γ^0(p)`, `Γ_0(p)` is correct.
