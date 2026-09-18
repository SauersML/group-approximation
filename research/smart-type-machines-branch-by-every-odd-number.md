---
rg: 2
id: smart-type-machines-branch-by-every-odd-number
kind: claim
title: For every odd m >= 3 an explicit reversible two-shape machine on m symbols has exactly m-fold crossing timings T(L+1) = m T(L) + m + 1
distinct_from:
  crossing-move-hierarchies-have-odd-branching: that proves branching numbers of all-crossing hierarchies are odd; this constructs a machine for each odd branching number.
  smart-induced-map-has-brick-local-height-3-renormalization: that is the m = 3 case for SMART itself, including the renormalization; this supplies the machines for m = 5, 7, 9, ..., without the renormalization.
  bs13-embeds-in-brin-thompson-3v: that is BS(1,3); this is the first step toward BS(1,m) for every odd m.
artifacts:
  - research/artifacts/gq-affq-odd-branching-machines.md
---

**OPEN.** Let `m = 2j+1 ≥ 3` and let `M_m` be the moving-head machine in SMART's format with shapes `F`, `H`,
alphabet `{0, …, 2j}`, and rules:
- `F0 → (1, H, flip)`;
- `F_i → (i+1, H, flip)` for `1 ≤ i ≤ j−1`;
- `F_j → (0, F, pass)`;
- `F_{j+1} → (0, H, flip)`;
- `F_i → (i−1, H, flip)` for `j+2 ≤ i ≤ 2j`;
- `H0 → (2j, H, pass)`;
- `H_s → (s, F, flip)` for `s ≥ 1`.

The map `(shape, s) ↦ (shape', s')` is a bijection, so `M_m` is reversible. Start in `(F, right, phase 2)` on
cell 0 holding `s+ ≠ 0`, with zeros to the right. Then the first arrival at cell `L+1` happens at time
`T(L) = (2m^{L+1} − (m+1))/(m−1)`, and at that moment the tape is restored. Equivalently, `T(0) = 1` and
`T(L+1) = m·T(L) + (m+1)`.

**Evidence** (`research/artifacts/gq-affq-odd-branching-machines.md`).
- *Verified by exact simulation* for `m = 3, 5, 7, 9, 11`, `L ≤ 7`, and `s+ = 1`, with every arrival clean. For
  `m = 3` the timing is SMART's (`3^{L+1} − 2`, Callard–Salo `prop:smart-moves`).
- *Level 1 by hand.* The head crosses cell 1 exactly `m` times, `→ ← → ⋯ →`. The mark there counts
  `0 → 1 → ⋯ → j → 0`, and the head bounces on `s+` by the rule `H_s`.
- *How the family was found.* The quintic table came out of a calibrated search of reversible two-shape machines:
  - exhaustive on `2×3` (46k tables), `2×4` (10.3M) and `3×3` (186M), finding branching 3 only;
  - lazy depth-first on `2×5`, finding 1422 quintic tables.

  So with two shapes, branching 5 needs at least 5 symbols. The family generalizes the smallest quintic table.

**Pipeline evidence for m = 5** (artifact §4): SMART's inducing set gives exactly `5^L` induced steps per
level-`L` crossing, and the induced map has locally readable eigenvalues `-1` (radius 0), `e^{2πi/5}` (radius 1) and
`e^{2πi/25}` (radius 2), exactly SMART's pattern with 3 replaced by 5.

**What would settle it.** A move lemma for `M_m`, analogous to Callard–Salo's `prop:smart-moves`, giving the
recursive decomposition of the filled and hollow crossings for general `j`, proved by induction on `L`.

**Why it matters.** With that lemma, SMART's pipeline would transfer:
- induce on the genuine level-0 moves (`smart-induced-on-genuine-moves-has-exact-tripling`);
- a brick-local height-`m` renormalization (`smart-induced-map-has-brick-local-height-3-renormalization`);
- then `renormalizable-thompson-elements-give-baumslag-solitar`.

Together these would give **`BS(1,m) ≤ 3V` for every odd `m`**. Even `m` stays blocked for all-crossing hierarchies
by the parity lemma.
