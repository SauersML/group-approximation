---
rg: 2
id: rf-subshifts-are-periodic-window-approximable
kind: claim
title: A perfect subshift is residually finite iff at every window its window SFT has finitely many finite orbits realizing all of its window patterns
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: that is the obstruction for subshifts inside an SFT without finite orbits; this is the two-sided criterion for every perfect subshift, whose sufficiency half builds Kerr–Nowak models from periodic configurations.
  periodic-approximable-subshifts-host-no-fp-simple-group: that defines pointwise periodic approximations with stabilizer avoidance, for a full-group obstruction; this characterizes Kerr–Nowak residual finiteness by window SFTs with covering finite orbits.
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be countable, `A` finite, and `X ⊆ A^Γ` a subshift without isolated
points. For finite `W ⊆ Γ` let `L_W(X) = {x|_W : x ∈ X}` and let
`X_W = {c ∈ A^Γ : (g^(-1)·c)|_W ∈ L_W(X) for all g ∈ Γ}` be the window SFT.

Then `Γ ↷ X` is residually finite in the sense of Kerr–Nowak (Ma, arXiv:2209.00580,
`defn: residually finite action`) iff for every finite `W` there is a finite `Γ`-invariant `O ⊆ X_W`
with `{c|_W : c ∈ O} = L_W(X)`.

**Consequences.**
- Every exact finite model of an RF subshift is a finite union of periodic configurations whose windows are
  windows of `X`, and conversely. A commented-out proposition in Ma's TeX source asserting that every subshift
  over a residually finite group is RF is therefore false (Labbé's shift, `z2-containing-groups-have-non-rf-measure-actions`).
- Used to prove `rf-toeplitz-subshifts-over-residually-finite-groups`.

Route: `rf-subshifts-are-periodic-window-approximable-proof`.

**Correction (review 2026-09-13).** Ma's commented-out proposition is specifically for binary subshifts: "Let $\Gamma$ be a residually finite group and $\Sigma \subset 2^\Gamma$ a subshift of $\Gamma\curvearrowright 2^\Gamma$. Then $\Sigma$ is residually finite." (arXiv:2209.00580 `main.tex` l.1293–1297, commented, proof unfinished). Labbé's shift has 19 letters, so it does not refute that literal statement. It is still false: the binary Z-subshift consisting of the orbit of `0^∞.1^∞` together with `0^∞` and `1^∞` is not residually finite under Kerr–Nowak's general definition, since finite models cannot move the clipped transition position back into the window. A perfect binary witness would need an equivariant embedding of an aperiodic Z^2-subshift into `2^(Z^2)` (Lightwood, recalled).

**Review (un-verify-measure, 2026-09-13): PASS on Proposition S; GAP on the Ma quote, corrected with a binary witness.** See `research/artifacts/un-review-measure-2026-09-13-part5.md` §R7.
