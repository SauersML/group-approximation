---
rg: 2
id: labbe-shift-derived-full-group-is-lef
kind: claim
title: The derived full group of Labbé's Wang shift is LEF
invalidates:
  - fp-simple-amenable-via-labbe-shift-full-group
distinct_from:
  labbe-shift-derived-full-group-is-finitely-presented: That asks for a finite presentation; this asks for local embeddability into finite groups, which for an infinite simple group rules out a finite presentation (finitely presented and LEF imply residually finite).
  simple-model-weak-soficity-with-small-defect-is-lef: That is a general implication from small-defect weak soficity to LEF; this is the LEF question for the one group D([[Omega_U]]).
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
---

**OPEN.** Let `Omega_U` be Labbé's 19-tile minimal aperiodic Wang shift, and `Gamma = D([[Z^2 ~ Omega_U]])`. Is `Gamma` LEF?

- **If yes.** `Gamma` is infinite, simple and LEF, so it is not finitely presented: finitely presented and LEF imply residually finite (Grigorchuk--Medynets arXiv:1105.0719, as recorded in `labbe-shift-derived-full-group-is-finitely-presented`).
  - That refutes `labbe-shift-derived-full-group-is-finitely-presented`, and it kills `fp-simple-amenable-via-labbe-shift-full-group`.
- **If no.** Some word nontrivial in `Gamma` lies in the finite residual of a truncated presentation `<S | trivial words of length <= n>` (artifact, Section 0).

**On no live path to a root, by design.** This claim is an obstruction. It acts through `invalidates:`, and Cairn counts reachability only through `requires:`. No live route needs LEF of `Gamma` as a premise, and the question tests the fp route rather than being a program question, so it is not root-marked.

## Attempts

- **Kakutani--Rokhlin towers (Grigorchuk--Medynets, arXiv:1105.0719, Theorem `TheoremLEF`, read from source).**
  - Mechanism: factor `Q = S_Q R_Q` into an `n`-permutation and an `n`-rotation, and send `Q` to `S_Q`.
  - Failure point: with cylinder bases, this wraps towers into legal cycles, which is a collared periodisation. An aperiodic `Z^2`-SFT has no collared periodisation (artifact, Section 2, Lemma L2).
- **Periodic SFT approximations (Cornulier, arXiv:2002.09342, Proposition `sdlef` and the proof of `clef`, read from source).**
  - Mechanism: write `X = ∩ X_n` with `X_n` SFTs having dense periodic points. Then `lim [[X_n]]⊙ ≅ [[X]]⊙`, and each `[[X_n]]⊙` is residually finite.
  - Failure point: a decreasing sequence of SFTs whose intersection is an SFT stabilises, so `X_n = Omega_U` eventually, and `Omega_U` has no periodic points.
  - The factor step of `clef` gives nothing new. The cocycles of a large ball of `Gamma` determine the tile at the origin, so the factor is a conjugacy (artifact, Section 2.2).
- **Residually finite actions (Ma, arXiv:2209.00580, Theorem C, read from source).**
  - Mechanism: a finite `epsilon`-dense model carrying a genuine action gives the LEF maps.
  - Failure point: no extension of `Omega_U` is residually finite (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`).
- **Relator shifts with one extension for all `n`.**
  - Mechanism: apply `zd-subshift-full-group-lef-via-periodic-relator-shifts` with a fixed extension of the generators.
  - Failure point: `Gamma` acts on `Z_∞ = ∩ Z_n`, and an infinite simple group fixes every finite orbit. So periodic points of `Z_∞` carry no large legal patch (artifact, Section 3).
- **Rational perturbation of the toral polygon exchange (Labbé arXiv:1903.06137, abstract only).**
  - Mechanism: replace the toral `Z^2`-rotation coded by `P_U` with a rational one, and act on a finite grid, as for interval exchanges.
  - Failure point: every rational rotation creates sliver atoms that code forbidden adjacencies, and every generic orbit meets one (artifact, Section 4).
- **Schreier rigidity.**
  - Mechanism: a finite model whose Schreier balls all look orbital yields charts, commuting moves and a legal periodic colouring.
  - Failure point: this only shows that some vertex of every finite model is non-orbital (artifact, Section 5). LEF models act regularly on finite groups, and they are not refuted.
- **Still open.** Two routes remain:
  - (C1) the spatial crux, `labbe-relator-shifts-carry-patch-rich-periodic-points`;
  - (C2) non-spatial finite groups exact on large balls.
- **fp methods.** The artifact, Section 7, checks Brin's `2V`, the `Sigma`-invariants and Matte Bon. The first rests on compression, which a full-support invariant probability forbids. The `Sigma`-invariants are vacuous for a perfect group. Matte Bon's two papers have no finite presentation criterion.
