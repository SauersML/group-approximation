---
rg: 2
id: measure-rf-class-iff-measured-subshifts-window-periodic
kind: claim
title: A group lies in the Kerr–Nowak measure class 𝔑 iff every measured subshift over it has periodic window models realizing all its patterns
distinct_from:
  rf-subshifts-are-periodic-window-approximable: that characterizes residual finiteness of one perfect subshift; this characterizes membership of the acting group in 𝔑 by testing all measured subshifts, with no perfectness assumption.
artifacts:
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be countable. Call a subshift `X ⊆ A^Γ` ( `A` finite) *window-periodic*
if for every finite `W ⊆ Γ` the window SFT `X_W = {c : (g^(-1)·c)|_W ∈ L_W(X) for all g}` contains a finite
`Γ`-invariant set `O` with `{c|_W : c ∈ O} = L_W(X)`.

Then `Γ ∈ 𝔑` (every Cantor `Γ`-system with a full-support invariant probability measure is residually finite in
the Kerr–Nowak sense) **iff** every subshift over `Γ` carrying an invariant probability measure of full support is
window-periodic.

- (⇐) Code the Cantor system by the names of a fine clopen partition; periodic window models of the name subshift
  transport back by Lemma 1 of `un-rf-beyond-free`.
- (⇒) Multiply the subshift by a Cantor space with trivial action and Bernoulli measure; a finite RF model gives
  finite-orbit configurations with legal windows, as in Proposition S.

Route: `measure-rf-class-iff-measured-subshifts-window-periodic-proof`.
