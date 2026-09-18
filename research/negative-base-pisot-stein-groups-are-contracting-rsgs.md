---
rg: 2
id: negative-base-pisot-stein-groups-are-contracting-rsgs
kind: claim
title: If β > 2 is a Pisot unit whose negative-base map y ↦ {−βy} sends every point of Z[β] ∩ [0,1) to 0, the group of piecewise maps y ↦ ±β^k y + c (c ∈ Z[β]) is a full contracting RSG; so it is finitely presented and it, with all its subgroups, embeds in a finitely presented simple group
requires:
  - contracting-rsgs-embed-in-fp-simple-groups
distinct_from:
  pisot-stein-groups-are-contracting-rsgs: that codes by the positive β-shift and needs (F), which forces an isolated-sign unit; this codes by the negative-base map T'(y) = {−βy} and needs its finiteness (F−₀), which by `algebraic-interval-exchange-groups-satisfy-boone-higman` holds for suitable units in every real field.
  flip-codings-remove-the-sign-obstruction-for-iet-groups: that isolated the open step (a negative-base RSG theorem on the right coset); this is that theorem, with the normalization y ↦ {−βy} on [0,1), whose boundary set is exactly Z[β].
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (route `negative-base-pisot-stein-groups-are-contracting-rsgs-proof`; lane proof, not reviewed; no
priority claimed).

## Setting

- `β > 2` is a Pisot unit, and `ρ_σ := |σ(β)| < 1` for the non-identity embeddings `σ`. The bound `β > 2` is used
  only for strong connectivity; every unit used downstream has `β ≥ 2.6`.
- `T'(y) = {−βy}` on `[0,1)`. On `((k−1)/β, k/β]` it is `y ↦ −βy + k`, for `k = 1, …, ⌈β⌉`: orientation reversing,
  with `T'(k/β) = 0` and `T'(0) = 0`.
- **(F−₀):** for every `z ∈ Z[β] ∩ [0,1)` there is `n` with `T'^n(z) = 0`.
- `G^±_β` is the group of all homeomorphisms of `[0,1)`, Cantorized at `Z[β] ∩ (0,1)`, that on each piece of a finite
  partition into intervals with endpoints in `Z[β]` are `y ↦ sβ^k y + c`, with `s = ±1`, `k ∈ Z`, `c ∈ Z[β]`.
- **What `G^±_β` contains:**
  - the Stein group `V(Z[β],⟨β⟩,1)`, where `s = +1`;
  - every interval exchange group with data in `Z[β]`, with or without flips;
  - via rescaling, every `V(Z[β],⟨β⟩,ℓ)`, as in step 6 of `pisot-stein-groups-are-contracting-rsgs-proof`.

## Statement

Assume (F−₀).
1. The `T'`-codings of points form a sofic shift. Let `Γ` be its finite, deterministic follower-set graph (finite
   because `β` is Pisot).
   - The paths of `Γ` starting at the full-interval vertex `v_0` identify `C_{v_0} ⊆ Σ_Γ` with the Cantorized
     `[0,1)`.
   - The cylinder boundary set is exactly `Z[β] ∩ [0,1)`.
   - `Γ` is strongly connected.
2. `G^±_β` acts on `C_{v_0}` by rational homeomorphisms, contains the Thompson group `V_{Γ,C_{v_0}}`, and has
   finite nucleus.
   - So it is a contracting RSG.
   - It is full, so it is finitely presented (BBMZ Theorem A).
   - It and all its subgroups embed in finitely presented simple groups
     (`contracting-rsgs-embed-in-fp-simple-groups`).

## Lesson for general BH

The positive-base finiteness theorem transfers to orientation-reversing codings with no loss:
- boundary points are the preimages of a fixed point;
- offsets are lattice points with bounded conjugates;
- the slope defect is bounded by the same conjugate-growth length lemma.

The only input is a digit-system finiteness property. For `T'` that property is an SRS condition with `α = 0`,
which a simple witness argument checks. So finiteness of full-group hosts over algebraic data is a property of
the *coding*, and the coding can be chosen with flips to fit any real field.
