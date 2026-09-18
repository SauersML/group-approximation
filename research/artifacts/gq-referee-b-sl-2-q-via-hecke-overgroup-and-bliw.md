# Referee report (citation/hypothesis lens): `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell-citation` and `sl-2-q-via-hecke-overgroup-and-bliw`

Referee: lane gq-referee-b, 2026-09-17. Reviewed as landed on main at 39b37d26f:
- the Ihara citation node;
- the route `sl-2-q-via-hecke-overgroup-and-bliw`, which gives `SL_2(Q)` in a finitely presented simple group
  given the data `(Λ, ι, C_1, C_2, φ)` with (H1)–(H4) of `sl-2-z-localized-has-fp-hecke-overgroup`.

**Not reviewed:** `sl-2-z-localized-has-fp-hecke-overgroup` itself, which carries (H1)–(H4). That is where the
real burden sits.

## Verdict

- **Ihara citation: PASS.**
- **Route: PASS.** Given (H1)–(H4), `SL_2(Q)` embeds in a finitely presented simple group; the route's
  hypotheses match BLIW Theorem C exactly.

## (1) Ihara via Hutchinson–Mirzaii–Mokari

**Source.** arXiv:2007.11159v2, §3.2, read in arXiv HTML. The setting is "F is the field of fractions of a discrete
valuation ring A", **not assumed complete**, and the statement is "SL₂(F) ≅ SL₂(A) *_{Γ₀(m_A)} SL₂(A)":
- `Γ_0(m_A)` is the subgroup of `SL_2(A)` whose lower off-diagonal entry lies in `m_A`;
- the second copy is embedded by conjugation by a diagonal matrix built from the uniformizer;
- it is attributed to Serre, *Trees*.

The summary rendering did not show the exact matrix. The node's `α = diag(1,l)` is the standard choice.

**Specialization.** `(Q, v_l, Z_(l), π = l)`.
- `α[[a,b],[c,d]]α^{-1} = [[a,b/l],[lc,d]]`, so `αA α^{-1} ∩ A = Γ_0(l)`.
- The index `l+1` statement is also correct: reduction modulo `l` is onto, and the preimage of the Borel subgroup
  has index `|P^1(F_l)|`. It is not needed.

## (2) BLIW Theorem C

**Source.** arXiv:2408.05673v2, read in arXiv HTML.
- "Theorem C [11.1]: Let G be a finitely presented group. Assume that there is a non-trivial group H∈ℬ𝒮_G such
  that H acts faithfully on its Bass–Serre tree. Then every K∈ℬ𝒮_G embeds in a finitely presented simple group."
- `ℬ𝒮_G` is "all finite graphs of groups with the property that all edge and vertex groups are abstractly
  commensurable with G and all edge group inclusions in vertex groups have finite index".
- One-loop graphs, that is HNN extensions, are included: the paragraph after Theorem C cites `BS(2,3) ∈ ℬ𝒮_Z`.

**Hypothesis match for `K = ⟨Λ, t | t x t^{-1} = φ(x), x ∈ C_1⟩`.**
- `K` has one vertex group, `Λ`, and one edge group, `C_1`.
- `C_1 ↪ Λ` has finite index, and `φ : C_1 → C_2 ≤ Λ` has finite image index.
- `C_1` is commensurable with `Λ`. So `K ∈ ℬ𝒮_Λ`.
- `Λ` is finitely presented (the node's data), and (H4) is verbatim the "non-trivial H ∈ ℬ𝒮_Λ acting faithfully on
  its Bass–Serre tree" hypothesis. **It matches.**

## (3) Step 2 of the route (group theory, checked)

- **Embedding of the amalgam.** `Λ *_{C_2} tΛt^{-1} ↪ K`.
  - A reduced alternating word has `g_odd ∉ C_2` and `g_even ∉ C_1`.
  - It has no pinch `t c t^{-1}` with `c ∈ C_1`, and no pinch `t^{-1} c t` with `c ∈ C_2 = φ(C_1)`.
  - So Britton's lemma applies.
- **Intersections.**
  - `ι(A) ∩ C_2 = ι(Γ_0)` by (H2).
  - `tι(A)t^{-1} ∩ C_2 = t(ι(A) ∩ C_1)t^{-1} = tι(Γ^0)t^{-1} = φ(ι(Γ^0)) = ι(αΓ^0α^{-1}) = ι(Γ_0)`, by (H1) and
    (H3), using `αΓ^0α^{-1} = Γ_0`.
- **The two maps agree.** `ψ_2(z) = tι(α^{-1}zα)t^{-1}` agrees with `ψ_1 = ι` on `Γ_0`, by (H3).
- **Injectivity.** The sub-amalgam lemma gives
  `A *_{Γ_0} A^α ≅ ι(A) *_{ι(Γ_0)} tι(A)t^{-1} ≤ K`. So `Ψ` is injective.
- **Correct.**
- The calibration remark is consistent with O1 and with BLIW's residual-finiteness boundary:
  - the vertex group `Λ` must be residually finite;
  - `Z_(l)` is residually finite;
  - `l`-divisibility enters only through `t`.

## Status note (RULES §5)

`SL_2(Q)` is a named stepping stone. Before any ESTABLISHED flip it needs:
- two referee passes on `sl-2-z-localized-has-fp-hecke-overgroup`, which carries (H1)–(H4);
- a priority check by gq-lit-arxiv.

This report covers only the two citation-bearing nodes above.
