# Kourovka 17.60 in Lean: what an unconditional proof needs (lane pal-k1760, 2026-09-19)

**Verdict:** `kourovka_17_60` in `Palomar/BooneHigmanChallenge.lean` cannot become an
unconditional Palomar theorem with the Lean infrastructure on main, or in any one lane
session. Both proofs on main use two large pieces of mathematics that are not formalized:
- spatial realization (Matui, a Rubin-type theorem);
- continuous eigenvalues of compact rotations (Pontryagin duality).

Until those exist, the Solution keeps the owed form `kourovka_17_60_of (h : Kourovka1760Owed)`,
and `Kourovka1760Owed` is the whole theorem.

## The proofs on main and what each step needs

The statement is `P = Q` whenever `CT_P(ℤ) ≃* CT_Q(ℤ)`. The main proof is
`research/ct-p-z-groups-are-pairwise-nonisomorphic.md` (referee PASS). The finite-`P`
second proof is `research/artifacts/gq-bh-bh-free-11-ct-p-z-second-proof.md`.

| Step | Mathematics | In Mathlib / on main? | Size |
|---|---|---|---|
| S0 | `CT_P(ℤ)` acts on `X_P = ∏_{p ∈ P ∪ {2}} ℤ_p` by piecewise box maps; `ℤ` is dense; restriction is injective | `PadicInt` and the product topology exist; the action does not | medium, about 1–2k lines |
| S0′ | every box-piecewise map with `P'`-smooth moduli lies in `CT_P` | elementary proof on main (0e0c97d15); in Lean only the `Kourovka1759/*` pieces for `CT(ℤ)` | medium |
| S1 | an isomorphism `F_P ≃* F_Q` is spatial, `Φ α = φ α φ⁻¹` (Matui, Theorem `spatial`) | **no**; see below | very large |
| S2 | germ groups at rational points are the groups `Γ_y` of `P'`-smooth rationals | no | medium |
| S3 | prime axes as minimal contracting sets | no | medium |
| S4 | each axis's prime is the unique `ℓ` with infinitely many `ℓ`-power continuous eigenvalues (dual of a closed subgroup of `ℤ_q^×`) | **no**: eigenfunctions of minimal rotations and duals of closed subgroups of `ℤ_q^×` are missing | large |

## The shared bottleneck: a Lean Rubin theorem

- **SK's flip converse.** `Manuscript/SimpleKazhdanSofic/FlipConverse/*` (60 files) has
  the same missing piece, for `[[T]]` of Cantor minimal ℤ-systems:
  - `SpatialRealize.lean` reduces `SpatialRealizationStatement` to
    `RigidStabilizerTransportStatement`, still an owed `def`;
  - the Stone-duality step is done there (`SpatialStone.lean`, `RubinRegOpen*`).
- **One theorem for both.** A Lean Rubin theorem would discharge both targets: an isomorphism
  of locally moving groups of homeomorphisms of compact zero-dimensional Hausdorff spaces
  maps rigid stabilizers of clopen sets to rigid stabilizers. It would serve S1 for 17.60
  and the flip-converse row, and likely 17.57's normalizer argument. Give it one dedicated
  lane, not three partial ones.

## Elementary shortcuts checked and ruled out

- **Torsion and finite subgroups:** `Sym(m)` sits in `CT_∅(ℤ)` for every `m`, so every
  finite group embeds in every `CT_P(ℤ)`.
- **Higman–Thompson subgroups:** every `V_n` already embeds in `V ≅ CT_∅(ℤ)`.
- **The relation `h g h⁻¹ = g^q`:**
  - Counting germ multipliers at fixed points on `X_P` rules out every `g` with finitely
    many nontrivial-germ fixed points, whether or not `q ∈ P ∪ {2}`.
  - So this relation does not separate primes without the full dynamical picture.
- **Result:** every invariant found so far reads `P` from germs at points, and points are
  recovered from the abstract group only through S1.

## Recommendation for the READY config

- Leave `kourovka_17_60` out of the unconditional submission (bh-pal-surface's rule: drop
  what cannot be made unconditional). Keep the proof in the research graph, where it is
  established and refereed.
- If 17.60 must go in, the order of work is:
  1. the Rubin lane (S1, shared with SK flip converse);
  2. then S0/S0′;
  3. then S2–S4, which needs a Pontryagin-duality layer for closed subgroups of
     `ℤ_q^×`. Mathlib has `PontryaginDual` but not these results.

## Lesson

Isomorphism invariants of full groups are dynamical, and their Lean cost is Rubin's
theorem. Any Palomar statement "these full groups are non-isomorphic" needs a formalized
spatial realization first, however elementary its paper proof looks.
