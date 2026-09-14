---
rg: 2
id: rf-groups-embed-in-simple-kazhdan-lef-groups
kind: claim
title: Every finitely generated residually finite group is a subgroup of an infinite finitely generated simple Kazhdan LEF group
distinct_from:
  residually-finite-group-toeplitz-elementary-groups-lef-kazhdan: that builds one simple Kazhdan LEF group per residually finite acting group; this embeds a given group itself, which needs a commutator overgroup because the acting group's units are not elementary.
  simple-kazhdan-lef-hosts-all-countable-locally-finite: that hosts countable locally finite groups; this hosts every finitely generated residually finite group, one envelope per group.
artifacts:
  - research/artifacts/sk-universal-embedding-a-rf-embedding-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Every finitely generated residually finite group `Γ` is a subgroup of an infinite,
finitely generated, simple group with property (T) that is LEF, hence sofic and hyperlinear.
- Explicitly, take a finitely generated residually finite `Δ ⊇ Γ` with `Γ ≤ [Δ,Δ]` and its RF Toeplitz subshift
  `X_Δ`.
- The envelope is `EL_3(LC(X_Δ,F_2) ⋊ Δ)`, and `γ ↦ diag(u_γ,1,1)` embeds `Γ` in it.

**Examples.** Every finitely generated linear group (Malcev), `SL_n(Z)`, surface groups, and the Grigorchuk group.

**Prior art.** Without (T) this is Kionke–Schesler, arXiv:2304.09307, Theorem 1.2 (= Theorem 9.14), quoted verbatim
in `research/artifacts/sk-questions-ggt-literature-2026-09-13-part1.md` §1 B1. So every finitely generated residually
finite group lies both in an amenable simple LEF group (Kionke–Schesler) and in a Kazhdan simple LEF group.

**Open extension.** The LEF case, `lef-groups-embed-in-simple-kazhdan-lef-groups`.

Route: `rf-groups-embed-in-simple-kazhdan-lef-groups-proof`.

**Review (sk-verify-3, 2026-09-13): PASS.** Reduction to infinite Γ, the overgroup, Corollary T with q = 2 and trivial centre, Whitehead's lemma with `diag([a,b],1,1) ∈ E_3`, and injectivity of `γ ↦ diag(u_ρ(γ),1,1)` re-derived; the self-contained tower proof over Δ (artifact Proposition 5) also PASS. The Kionke–Schesler quote was not read at source. See `research/artifacts/sk-review-3-2026-09-13-part3.md` §A.

**Review (sk-verify-4, 2026-09-13): PASS, independent concurrence.** Reduction to infinite Γ, Corollary T over Δ, trivial centre via Z(R) = F_2, Whitehead products multiplied out, and the embedding re-derived. See `research/artifacts/sk-review-4-2026-09-13-part1.md` §5.
