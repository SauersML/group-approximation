---
rg: 2
id: atlas-steinberg-spare-index-independence
kind: claim
title: The spare-l object commutes with its own factors at every monomial length
distinct_from:
  atlas-steinberg-transfer-identity: that is the identity equating adjacent spare definitions GIVEN three commutations; this is the missing supply of those commutations at length three and beyond — the two are deliberately separate because the identity is proved and this is not.
  atlas-steinberg-rank-five-translation: that is the whole usable-list program; this is the single lemma it now blocks on, extracted so the frontier shows exactly one hole where "completeness" used to be.
artifacts:
  - research/artifacts/atlas-completeness-derivation-2026-08-15.md
---

**Lemma X.**  In the group `G₀` presented by the emitted family of
`atlas-steinberg-rank-five-translation`, for pairwise distinct
`i, j, l` and a monomial `w` with first letter `a`, the spare-`l` object

```text
D^l_ij(w) = [Ê_il(a), Ê_lj(w')]        (w = a·w')
```

commutes with `Ê_il(a)` and with `Ê_lj(w')`.

**What it buys.**  With Lemma X, the transfer identity
(`atlas-steinberg-transfer-identity`) has its hypotheses at every
length, spare-index independence follows by induction, split
independence and ring consistency are already closed, and
`G₀ ≅ St₅(L)`: the emitted `T_St` is a complete presentation and the
usable-list chain of the translation program finishes with no
literature import beyond Kervaire–Steinberg centrality.

**Status.**  Length 2: PROVED — σ-independence at length two is an
emitted relation, so the object may be represented with `σ ≠ l`, where
the needed commutations are emitted (St2) instances.  Length ≥ 3: OPEN.
The obstruction in one sentence: bilinearity in the first argument
needs `[U_il, U_ij] = 1`, which is available only for spare-`σ`
presentations with `σ ≠ l` — and the one presentation the transfer
argument produces is the spare-`l` presentation, so the representative
switch that would finish is exactly the independence being proved.
This is not an index shortage (`n = 5` has a third spare, and all three
commutations hold FOR the `ρ`-presentation); it is a transport problem
between presentations.

## Attempts

- **Length-2 base (works, instructive).**  The emitted family equates
  all three spare chains at length two, so the representative switch is
  free there; the induction stalls precisely because at length ≥ 3 the
  switch IS the conclusion.
- **Five rejected routes (details in the artifact §5; do not retry):**
  (1) decomposing `X` through a fourth index — a factor lands at root
  `(m,l)` and collides with `V`'s root `(l,j)` at the shared `l`, an
  (St3) situation, not (St2); (2) decomposing `V` — symmetric collision;
  (3) routing through the third spare `ρ` — relating `D^ρ` to `D^l` by
  the transfer identity reintroduces the clash one index over; (4)
  Hall–Witt — equates the two spare definitions only up to `Y`- and
  `Z`-conjugations whose discharge needs the same length-`t`
  commutations; (5) de-nesting via `e^*e = 1` — genuine, but raises
  length `t → t+1` and cannot power an induction on length.
- **Structural pruning (available, insufficient alone).**  Every
  nonzero word in `L` is normal, `αβ^*` with `α, β ∈ {e,f}^*` — starred
  adjacencies collapse or kill — so only normal words need handling;
  this prunes the case space, not the length.
- **Open ideas queued to a fresh derivation agent:** joint induction
  (Lemma X for all spares + σ-independence proved together, mirroring
  how the length-2 base uses the emitted switch); the α/β^* boundary as
  the only spare-change point; one-sided transfer through the
  `ρ`-presentation, checking whether the identity truly needs `T`'s
  commutations on both sides.
- **Graceful degradation (the safety net).**  Enlarging `T_St` is
  always safe: if the lemma needs finitely many chain-difference or
  commutation relators at bounded length as extra axioms, they can be
  emitted and machine-verified in `R̄` like everything else, and the
  chain closes with a slightly larger — still finite, still verified —
  list.  The lemma is therefore a technical core, not a viability risk;
  it is also, per the derivation artifact, the exact item a targeted
  page-level read of [KrM, Theorem 3] should be aimed at.
