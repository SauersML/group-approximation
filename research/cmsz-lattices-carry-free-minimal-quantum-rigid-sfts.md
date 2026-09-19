---
rg: 2
id: cmsz-lattices-carry-free-minimal-quantum-rigid-sfts
kind: claim
title: Every torsion-free CMSZ group, a Kazhdan one-ended lattice acting simply transitively on the vertices of a thick Ã2 building, carries a free minimal quantum-rigid SFT, namely the Busemann transplant of the causal SW minimal crossing-wire shift
artifacts:
  - research/artifacts/gq-bh-invent-04-germ-primitivity-check.md
distinct_from:
  f2-times-f2-has-a-quantum-rigid-free-minimal-sft: that is gate G2(c) over the non-Kazhdan group F_2 x F_2; this is the same object over Kazhdan lattices.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that gives rigid, minimal, only topologically free SFTs over these lattices; this gives free ones, still minimal.
  sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices: that gives free rigid SFTs without minimality; this adds minimality.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `busemann-transplant-minimality-is-horospherical-minimality`, `a2-busemann-transplants-preserve-quantum-rigidity`, `sw-minimal-crossing-wire-shift-is-rigid`, `minimal-crossing-wire-shift-finite-factors-are-3-groups`, `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`.

**CONDITIONAL** (lane bh-invent-04, 2026-09-18; not reviewed; no priority claimed). It is conditional
only on the lane proofs in `requires`. The rigidity step of the fibre is with referee bh-ref-engines. The
germ primitivity used here is proved in general for `θ ≠ 0` by the cited node, and it is recomputed in the
artifact for two explicit groups.

## Statement

Let `T` be a CMSZ triangle presentation over `PG(2, q)` with `(x,x,x) ∉ T` for all `x`. Examples are the
two cyclic Fano presentations of the artifact. Let `Γ_T` be its group. It acts simply transitively and
type-rotatingly on the vertices of a thick Ã2 building. It is torsion-free (CMSZ criterion, recalled),
finitely presented, one-ended, and Kazhdan (Cartwright–Młotkowski–Steger, recalled).

Then there is an SFT `X` over `Γ_T` such that:
- `Γ_T` acts **freely** and **minimally** on `X`;
- `X` is `D`-quantum rigid over every field for all large `D`.

Consequently `LC(X, k) ⋊ Γ_T` is finitely presented (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`)
and central simple (`free-minimal-cantor-crossed-products-are-central-simple`).

## Proof

1. **The fibre.**
   - Let `Ω_min = Ω_SW` be the minimal crossing-wire shift in the causal diagonal-time layout
     (`sw-minimal-crossing-wire-shift-is-rigid`, §2; tile level in
     `research/artifacts/gq-bh-g2-fixedpoint-a-diagonal-time-layout.md`). It is free, minimal, quantum
     rigid and SW-deterministic. A generic one-way zone is excluded by that node's causality lemma.
   - Shear it: `Y = Ω_min ∘ M^(-1)` with `M(−e_1) = 2ω_1 + ω_2` and `M(−e_2) = ω_1 + ω_2`, which has
     determinant 1. Then `Y` is cone-deterministic.
2. **The skeleton.** Use `P` from `a2-lattice-boundary-skew-shifts-are-quantum-rigid`. Since `θ ≠ 0`,
   Step 5.1 of `a2-lattices-embed-in-fp-simple-groups` allows any sufficiently large rescaling `n`: it only
   needs two loops of each colour at every object, and primitivity gives that. Take **`n` a large power of 2**.
3. **Type rotation.** `a2-busemann-transplants-preserve-quantum-rigidity` is written for type-preserving
   `Γ`; the proof runs verbatim for type-rotating `Γ` acting simply transitively on all vertices, with `L` the
   vertex (coweight) lattice. The reason is that a type-rotating automorphism acts on the apartment through
   the extended affine Weyl group `P^∨ ⋊ W`.
   - So it acts on the building at infinity through `W`, preserving points and lines, and the Busemann
     cocycle is a translation cocycle into `P^∨`.
   - Every other step (Determination Lemma, cylinder transport, coherence, section family) is local
     and type-blind.
4. **Rigid and free.** The transplant `X = P ×_β Y` is an SFT that is quantum rigid and free
   (`a2-busemann-transplants-preserve-quantum-rigidity`, items 1–4; freeness from freeness of `Ω_min`).
5. **Minimal.**
   - The Robertson–Steger matrices of `Γ_T` are primitive (`a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`,
     item 2, `θ ≠ 0`). For the two cyclic Fano groups, the artifact recomputes this: `M_1 M_2 > 0` fails, but
     `M_1 M_2^3 > 0` and `M_1^2 M_2^2 > 0` hold.
   - That gives (GP), so the zero-lag relation is minimal on `Ω` and `P = Ω × L/nL`
     (`busemann-transplant-minimality-is-horospherical-minimality`, items 4 and 6).
   - `nZ^2` acts minimally on `Y`, since `3 ∤ n` and a shear preserves minimality. The input here is
     `minimal-crossing-wire-shift-finite-factors-are-3-groups`, which is stated for the two-way layout. Its author reports
     that the proof (blank rank-`K` blocks recur in every rank-`(K+1)` macrotile, with zooms `3^(C^k)`) covers
     the SW layout verbatim. That extension is not written on main.
   - By item 4 there, `X` is minimal. ∎

## What remains

- **Review.** The chain is conditional only on lane proofs, and none of them is independently reviewed:
  - the fibre (crossing-wire rigidity with DR minimality, and the causal diagonal-time layout under
    verification by bh-free-35);
  - the Ã2 transplant (Determination Lemma, cylinder transport);
  - the minimality criterion.
- **Programmability.** The zone is universal, so decorated versions stay free, minimal and rigid provided
  the decoration's finite factors are also 3-groups. That hands gate E2 of the master route a Kazhdan
  base, and E1 and E3 are the next gates.

## Lesson for general BH

- **Four independent layers stack over a Kazhdan group:**
  - co-location makes the fibre rigid;
  - aperiodicity of the fibre makes the action free;
  - horospherical mixing (primitive boundary 2-graph) makes it minimal;
  - cylinder transport carries all three through the building.
- **The only coupling is arithmetic.** The rescaling of the skeleton must be prime to the fibre's zoom
  base, and type-rotating lattices leave that choice free.
- **Consequence.** The master route's G2 object, a free minimal quantum-rigid SFT, now exists over a
  finitely presented Kazhdan group, conditional on reviewable lane proofs. Rigidity was never the
  obstruction on non-amenable groups; the missing ingredients were design choices.
