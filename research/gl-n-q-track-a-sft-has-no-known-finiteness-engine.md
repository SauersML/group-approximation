---
rg: 2
id: gl-n-q-track-a-sft-has-no-known-finiteness-engine
kind: claim
title: None of the three finite-presentation engines for V-times-subshift hosts on main reaches the GL_n(Q) Track A SFT; Garside codings fail by freeness, tree and Bruhat-Tits shadow codings fail on St_10(R_L), and contraction fails by variable zoom; the linear route is exhausted, so rigidity implies E3' there only through a new nonlinear engine, most plausibly a fixed-zoom M2 witness
requires:
  - gl-n-q-track-a-finiteness-needs-only-fp-and-rigidity
  - quantum-family-representations-are-exhausted-at-rigidity
  - free-sft-hosts-admit-no-finite-type-coding
  - locally-finite-tree-end-shifts-are-quantum-rigid-sfts
  - kazhdan-simple-groups-act-only-on-exotic-2d-buildings
distinct_from:
  quantum-family-representations-are-exhausted-at-rigidity: that shows no quantum-family (linear) argument can prove rigidity ⇒ finite presentation once X is rigid; this checks the three NONLINEAR engines on main against the one host that matters for 5.3(5) and finds each blocked, for three different reasons.
  one-scale-filling-decides-fp-of-v-times-subshift-hosts: that reduces finite presentation to one-scale filling and supplies it by finite shadow bases; this shows shadow bases on trees and Bruhat-Tits buildings cannot carry St_10(R_L).
  gl-n-q-track-a-finiteness-needs-only-fp-and-rigidity: that reduces the group-side gates over (St_10(R_L)*Z) x Z^2 to rigidity plus the rigidity-to-fp theorem; this asks which known proof of that theorem could apply there.
---

**ESTABLISHED as a case check** (lane bh-gln-tracka, 2026-09-18). Items 2a–2c are proved from the cited nodes,
which are unreviewed lane proofs except where marked. Item 3 is a proposal.

## Setting

- `Λ_0 = (St_10(R_L) * Z) × Z^2`.
- `X` is the free minimal SFT over `Λ_0` obtained by keyed-slot Durand–Romashchenko lifting
  (`free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2`).
- `F = F(G_V × (Λ_0 ⋉ X))`.

By `gl-n-q-track-a-finiteness-needs-only-fp-and-rigidity`, E3′ for `F` is: quantum rigidity of `X` plus
"rigidity ⇒ one-scale filling". The question is which proof of the second part could apply.

## Statement

1. **Linear arguments are excluded.** Once `X` is rigid, every quantum-family representation of a local
   presentation of `F` factors through `F` (`quantum-family-representations-are-exhausted-at-rigidity`). So
   linearization cannot decide one-scale filling. That node answers "does the linear statement imply the
   nonlinear one?": not by any argument through quantum families.
2. **The three nonlinear engines on main, checked against `X`.**
   - **(a) Finite-type (Garside) codings** (`cuntz-stabilized-garside-full-groups-are-f-infinity`, after Li).
     *Blocked.* `X` is free, and V times a free transformation groupoid has no finite-type coding
     (`free-sft-hosts-admit-no-finite-type-coding`).
   - **(b) Finite shadow bases, i.e. compression** (`one-scale-filling-decides-fp-of-v-times-subshift-hosts`,
     `cocompact-tree-end-shift-hosts-are-f-infinity`).
     - *Blocked in both known geometries.* No `Λ ⊇ St_10(R_L)` acts topologically freely on the boundary of a
       locally finite tree or of a Bruhat–Tits building.
     - *Trees.* `St_10(R_L)` has (FA), so it fixes a vertex. Topological freeness puts the vertex stabilizer inside
       a profinite group, so it is residually finite (`locally-finite-tree-end-shifts-are-quantum-rigid-sfts`,
       item 4). But `St_10(R_L)` is infinite with no nontrivial finite quotient.
     - *Bruhat–Tits buildings.* Every finitely generated group with (FA) and no nontrivial finite quotient acts
       trivially (`kazhdan-simple-groups-act-only-on-exotic-2d-buildings`), so topological freeness fails.
     - The same holds for every finite product of such geometries. The only compression geometries left are
       exotic 2-dimensional buildings.
     - For an overgroup of `GL_n(Q)` not containing `St_10(R_L)`, tree compression needs (SL)
       (`end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups`, part 5, and
       `z-semilocalized-embeds-in-fp-rf-group`).
   - **(c) Internal contraction** (Nekrashevych's FP2 in `rover-nekrashevych-finite-presentation-criteria`;
     renormalized hosts `⟨F, S⟩` in `research/artifacts/gq-bh-bh-invent-03-groupoid-higman.md` §5).
     *Blocked for this `X`.*
     - FP2 needs the self-similarity inside the group: one desubstitution `S` with contracting sections.
     - `X` comes from Durand–Romashchenko simulation of an arbitrary effective subshift, which uses variable zoom.
       So it has no single `S`, and the renormalized host is not finitely generated (bh-invent-03 §5,
       Consequence 3).
     - For `F` itself the self-similarity would only be an outer automorphism, with the contraction-saturated,
       L-presentation-like behaviour of `one-scale-filling-decides-fp-of-v-times-subshift-hosts` Part 5.
3. **Proposal: the one engine that is not excluded in principle for 5.3(5).**
   - The PSPACE cap on fixed-zoom (ω-automatic) hosts (`definable-parameter-hosts-cap-simple-subgroups-at-pspace`)
     is harmless for this input: finitely generated subgroups of `GL_n(Q)` have polynomial-time word problem.
   - So engine (c) could apply to a *redesigned* Track A object: a fixed-zoom, recognizable, self-similar
     minimal free SFT over an fp overgroup of `GL_n(Q)`.
   - That needs an (M2) witness on `St_10(R_L) * Z` whose hierarchy has fixed zoom (an ω-automatic one), and
     word problem for `St_10(R_L)` in PSPACE.
   - Then finite presentation of the renormalized host would follow from an FP2-type contraction argument, up to
     the codimension-one fault locus of bh-invent-03. By bh-invent-03 §5 that host also forces rigidity, so rigidity
     would be proved rather than assumed.

## Proof of 2(b)

- *Trees.* `Λ` acts on a locally finite tree `T`, topologically freely on `∂T`. `St_10(R_L)` is Kazhdan
  (`steinberg-groups-of-r-l-are-quasisimple`), hence (FA), so it lies in some vertex stabilizer `Λ_v`.
  Topological freeness makes the action on `T` faithful, so `Λ_v` embeds in the profinite group `Aut(T)_v` and is
  residually finite (bh-star-a, item 4). Subgroups of residually finite groups are residually finite. But
  `St_10(R_L)` is infinite and has no nontrivial finite quotient: it is generated by divisible root subgroups
  (`decidable-fp-groups-have-effective-minimal-free-subshifts`, item 5).
- *Bruhat–Tits buildings and products.* `St_10(R_L)` is finitely generated, with (FA) and no finite quotient. So it
  acts trivially on every locally finite tree and Bruhat–Tits building (813bff6dd), and hence on the boundary.
  In a finite product, it acts trivially factor by factor. A nontrivial element acting trivially has
  `Fix = ` everything, contradicting topological freeness.

The other items are the cited nodes read for this `X`. ∎

## Lesson for general BH

Rigidity is the linear shadow of finite presentation. The nonlinear upgrade has so far come only from one of three
finite combinatorial structures:
- a finite-type coding (Garside);
- a finite shadow basis (compression);
- an internal contraction (Nekrashevych).

Each is killed by a different feature of hard inputs:
- **freeness** kills finite-type codings;
- **(FA) without finite quotients, and divisibility** kill compression on trees and Bruhat–Tits buildings;
- **variable zoom**, which simulation of arbitrary effective inputs requires, kills contraction.

So "rigidity ⇒ finite presentation" for simulation-built SFTs needs a fourth engine, one that fills loops across a
variable-zoom hierarchy. For inputs of low complexity such as `GL_n(Q)`, a fixed-zoom (automatic) design would let
Nekrashevych-type contraction do the job. That is the concrete redesign to try.
