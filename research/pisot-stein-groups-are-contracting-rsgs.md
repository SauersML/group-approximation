---
rg: 2
id: pisot-stein-groups-are-contracting-rsgs
kind: claim
title: For an algebraic unit β > 1 with property (F), the Stein group V(Z[β],⟨β⟩,1) acts on the β-shift as a contracting rational similarity group, so every subgroup of every V(Z[β],⟨β⟩,ℓ) embeds in a finitely presented simple group
requires:
  - contracting-rsgs-embed-in-fp-simple-groups
distinct_from:
  stein-v-groups-act-with-type-a-on-breakpoints: that needs finite presentation of the Stein group (Cleary's theorem, degree 2 only) and passes through twisted Brin--Thompson groups; this needs no finiteness input for the Stein group, works in every degree where a unit with (F) exists, and passes through BBMZ's contracting RSGs.
  quadratic-rotation-iet-groups-satisfy-boone-higman: that (bh-free-03) codes quadratic Sturmian rotations by substitutions; its artifact (§6) proposed β-adic coding for rank ≥ 3 interval exchanges and left it open at a uniform level-defect bound. That bound is supplied here (step 3 of the route), with scalings as well as translations.
  substitution-subshift-full-groups-satisfy-boone-higman: that is the substitution-subshift theorem; the groups here are Stein groups, which contain interval exchange groups of rank up to deg β, most of them not coming from substitutions.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (route `pisot-stein-groups-are-contracting-rsgs-proof`; lane proof, not reviewed; no priority
claimed). Inputs:
- BBMZ's host theorem, imported at `contracting-rsgs-embed-in-fp-simple-groups`;
- standard β-numeration: the greedy algorithm, Parry's admissibility criterion, and "β-shift is of finite type
  iff d_β(1) is finite" (Parry; Ito--Takahashi). The first two were read at source in Frougny's survey; see the
  artifact.
- property (F) (Frougny--Solomyak, ETDS 12 (1992)): cited, not read at source.

## Definitions

- `β > 1` is an **algebraic unit with property (F)**: every element of `Z[β] ∩ [0,1)` has a finite greedy
  β-expansion. (For a unit, `Z[β^{-1}] = Z[β]`.)
  - (F) forces `d_β(1)` to be finite, so the β-shift is a subshift of finite type.
  - It also forces `β` to be Pisot (Frougny--Solomyak). We assume Pisot explicitly anyway: all other
    conjugates `σ(β)` satisfy `|σ(β)| < 1`.
- **Examples.**
  - `β² = mβ + 1` (`m ≥ 1`), whose inverses are the metallic means;
  - every root `β > 1` of `x^d − a_1x^{d−1} − … − a_d` with `a_1 ≥ a_2 ≥ … ≥ a_d = 1`, such as the
    tribonacci number and all d-bonacci numbers (Frougny--Solomyak's sufficient condition).
  So there are such fields in every degree `d ≥ 2`.
- `V_β := V(Z[β],⟨β⟩,1)` is the Stein group of `stein-derived-groups-need-computable-modules`.

## Statement

1. Let `X_β` be the one-sided β-shift (an irreducible SFT) and `π : X_β → [0,1]` the value map. Then:
   - `π` identifies `X_β` with `[0,1)` Cantorized at `Z[β] ∩ [0,1)`;
   - `V_β` acts on `X_β` by rational homeomorphisms;
   - the image contains the Matsumoto--Matui Thompson group `V_{X_β}`;
   - it has finite nucleus.
   So it is a contracting RSG.
2. Hence `V_β` embeds in a finitely presented simple group (`contracting-rsgs-embed-in-fp-simple-groups`), and so
   does every subgroup of it.
3. For every `ℓ ∈ Z[β]_{>0}`, `V(Z[β],⟨β⟩,ℓ)` embeds in `V_β`. So every subgroup of it also embeds in a finitely
   presented simple group.

Consequences for interval exchange groups: `pisot-interval-exchange-groups-satisfy-boone-higman`.
