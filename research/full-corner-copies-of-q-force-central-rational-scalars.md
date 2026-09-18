---
rg: 2
id: full-corner-copies-of-q-force-central-rational-scalars
kind: claim
title: If a full corner eRe of a ring R contains Q unitally, then R contains Q centrally and unitally, so corner embeddings of GL_n(Q) do not escape the rational-scalar obstruction
distinct_from:
  rational-scalars-obstruct-fp-elementary-hosts: that assumes a unital map Q -> R and bounds the elementary rational scalars of PE_N(R); this shows the hypothesis is automatic as soon as Q sits unitally in any full corner, so that node applies to corner designs too.
  full-corners-must-kill-rational-k2-symbols: that starts from a unital map Q -> R and a full idempotent e and constrains K_2 of the corner eRe; this goes the other way, from Q in a corner to Q in the centre of R.
  q-embeds-in-a-corner-of-a-fp-toeplitz-ring: that is one finitely presented ring with Q in a non-full corner (its vacuum), which is exactly why that ring is not simple; this is the general statement for full corners.
---

**ESTABLISHED** (lane proof, elementary, inline below; not reviewed; no novelty claimed —
this is the Morita invariance of the centre, written out so the graph can use it).

## Statement

Let `R` be a unital ring and `e ∈ R` an idempotent with `ReR = R` (a *full* idempotent;
in a simple ring every nonzero idempotent is full). Suppose there is a unital ring map
`Q -> eRe`, i.e. `m·e` is invertible in `eRe` for every integer `m >= 1`.

1. **Centres agree.** The map `ζ: Z(R) -> Z(eRe)`, `z ↦ ze`, is an isomorphism of unital rings.
2. **Q is central in R.** Hence there is a unique unital ring map `Q -> Z(R) ⊆ R`, `q ↦ c_q`,
   with `c_q e = q·e` for every `q ∈ Q`. In particular `R` has characteristic `0` and
   contains `Q` centrally and unitally.
3. **Consequence.** Every statement on main whose hypothesis is "a unital map `Q -> R`"
   applies to `R`, in particular `rational-scalars-obstruct-fp-elementary-hosts`: if
   `PE_N(R)` (`N >= 3`) is finitely presented, then
   `Λ_N(R) = {λ ∈ Q^x : c_λ I_N ∈ E_N(R)}` is finitely generated.

## Why it matters for `gl-n-q-embeds-in-fp-simple-group`

A tempting way around the rational-scalar obstruction is to embed `GL_n(Q)` through a
corner: `g ↦ g_e + (1-e)I`, where `g_e` is `g` with entries `q ↦ q e`. The image of a
scalar matrix `λ I_n` is then `λe + (1-e)`, which is **not** central in `E_N(R)` when
`e` is not central, so `GL_n(Q)` meets the centre of `E_N(R)` trivially and embeds in
`PE_N(R)` (via `SL_(n+1)(Q)`, no `K_1` condition is needed for that).

This does not help. If the host `PE_N(R)` is simple, `R` is simple (for `N >= 3`, any
nonzero proper ideal `I` gives the proper normal subgroup `E_N(R, I)`, and it is not
central), so `e` is full and part 2 puts `Q` in the centre of `R` anyway. The *central*
rational scalars `c_λ I_N`, not the corner scalars, are what `rational-scalars-obstruct-fp-elementary-hosts`
counts, and they are present regardless of how `GL_n(Q)` itself is embedded. So a
corner design meets exactly the same `K_1` budget (`Λ_N(R)` finitely generated) and, by
`full-corners-must-kill-rational-k2-symbols`, the same `K_2` budget as a unital design.
Non-full corners (as in `q-embeds-in-a-corner-of-a-fp-toeplitz-ring`) require a non-simple
`R`; a simple quotient `R/I` in which `e` survives has `ē` full, and part 2 applies to
`R/I`.

**Scope.** The remark about simple quotients assumes the host is `PE_N` of a simple
quotient ring. Simple quotients of `E_N(R)` that are not of the form `PE_N(R/I)` are not
covered; for rings without a sandwich classification of normal subgroups of `E_N` this is
a genuine gap, recorded here and not claimed.

## Proof

Write `1 = Σ_(i=1)^k x_i e y_i` with `x_i, y_i ∈ R` (possible since `ReR = R`).

*`ζ` is a unital ring map into `Z(eRe)`.* For `z ∈ Z(R)`, `ze = eze ∈ eRe` commutes with
every `ere`. Additivity is clear, `1 ↦ e`, and `(zz')e = z z' e e = (ze)(z'e)` because
`z` is central.

*Injective.* If `ze = 0` then `z r e r' = r (ze) r' = 0` for all `r, r'`, so
`z·1 = Σ z x_i e y_i = 0`.

*Surjective.* Let `w ∈ Z(eRe)` (so `w = ewe`). Put `z = Σ_i x_i w y_i`. For `r ∈ R`,
using `1 = Σ_j x_j e y_j` and `w = we = ew`,

    z r = Σ_i x_i w e y_i r · Σ_j x_j e y_j
        = Σ_(i,j) x_i w (e y_i r x_j e) y_j
        = Σ_(i,j) x_i (e y_i r x_j e) w y_j        (w is central in eRe)
        = Σ_j (Σ_i x_i e y_i) r x_j e w y_j = r Σ_j x_j w y_j = r z.

So `z ∈ Z(R)`. And `z e = Σ_i x_i w y_i e = Σ_i x_i w (e y_i e) = Σ_i x_i (e y_i e) w
= (Σ_i x_i e y_i) e w = e w = w`, using again that `w` commutes with `e y_i e ∈ eRe`.
This proves part 1.

*Part 2.* The image of `Q -> eRe` is central in `eRe`: `m e` is central, and the inverse
of a central unit is central. Compose with `ζ^(-1)`. Uniqueness follows from injectivity
of `ζ`. Characteristic `0` follows since `m·1 = ζ^(-1)(m e)` is a unit.

*Part 3.* Immediate from part 2.
