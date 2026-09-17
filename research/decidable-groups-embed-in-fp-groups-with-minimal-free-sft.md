---
rg: 2
id: decidable-groups-embed-in-fp-groups-with-minimal-free-sft
kind: claim
title: Every finitely generated group with solvable word problem embeds in an infinite finitely presented group carrying a nonempty minimal free subshift of finite type
distinct_from:
  permutational-boone-higman-conjecture: that asks for an overgroup with a faithful action with finitely generated stabilizers and finitely many orbits of pairs; this asks for an overgroup carrying a minimal free shift of finite type, a symbolic-dynamical existence statement with no stabilizer or presentation condition on any action.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that proves finite presentation of a subshift full group forces finite type; this asks that shifts of finite type which are minimal and free exist over an overgroup of every decidable input.
---

**OPEN.** Premise (P1) of route
`boone-higman-via-v-times-aperiodic-sft-full-groups`.

**Statement.** For every finitely generated group `K` with solvable word problem
there are:
- an infinite finitely presented group `Λ` containing `K`;
- a finite alphabet `A` and a nonempty subshift of finite type `X ⊆ A^Λ`,

such that `Λ` acts freely and minimally on `X`.

**Why it can fail, and why it must consume decidability.**
- A nonempty minimal free SFT is strongly aperiodic. By Jeandel
  (arXiv:1501.06831; context only, not re-read at source), a finitely presented
  group with a nonempty strongly aperiodic SFT has solvable word problem.
  - So the statement is false for every input with unsolvable word problem.
  - Unlike the Higman embedding theorem, which the input satisfies without
    decidability, the statement cannot hold for all recursively presented inputs.
- `Λ` must be one-ended (Cohen, context only: groups with at least two ends carry
  no strongly aperiodic SFT). This constraint is harmless, since `Λ x Z` is
  one-ended.
- The statement is subgroup-closed in `K`. By
  `boone-higman-iff-simple-kazhdan-decidable-inputs`, the route needs it only for
  infinite simple Kazhdan inputs.

## Attempts

**Attempt 1 (2026-09-17): strongly aperiodic SFTs on products, then pass to a
minimal subsystem.** Sketch only; the sources were not re-read.
- By Clapham, `K` lies in a finitely presented `Λ_0` with solvable word problem.
- For products of two infinite finitely generated groups with solvable word
  problem, Barbieri--Sablik--Salo construct nonempty strongly aperiodic SFTs
  (self-simulable groups, arXiv:2104.05141). So `Λ = Λ_0 x Z` would carry a
  nonempty free SFT `Y`.
- A minimal subsystem `X ⊆ Y` exists by Zorn and is free. It need not be of
  finite type.
- *Dies at minimality of an SFT.* The missing step is that some strongly aperiodic
  SFT on `Λ` is itself minimal. This is known for `Z^2`, where Labbé's Wang shift
  is minimal (`labbe-shift-derived-full-group-is-finitely-presented`), but no
  general construction is recorded here.

**Attempt 2 (2026-09-17): pull back a minimal free SFT of `Z^2`.** Let `Y` be a
minimal free SFT on `Z^2` and `Λ = Λ_0 x Z^2`. Take `X` to be the configurations
constant along `Λ_0`-cosets whose `Z^2` shadow lies in `Y`.
- `X` is of finite type and minimal.
- *Dies at freeness.* `Λ_0` acts trivially on `X`, so the transformation groupoid
  is not effective and `Λ_0` does not embed in the full group. Replacing the
  trivial factor by a free minimal SFT on `Λ_0` is the statement itself.

**Attempt 3 (2026-09-17, swarm-0917-w5-bh-simple-fa): split into existence and
minimal simulation.** Route `minimal-free-sft-via-plane-constant-minimal-simulation`.
The implication is complete; two OPEN premises remain.
- **(M2)** `decidable-fp-groups-have-effective-minimal-free-subshifts`. The
  Clapham envelope `Λ_0 = Λ_1 x Z` carries an effectively closed minimal free
  subshift `Y`.
- **(M1)** `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`.
  `Y` is a `Z^2`-invariant, `Λ_0`-equivariant factor of a minimal SFT over
  `Λ_0 x Z^2` with free `Z^2`-subaction. This is the group form of
  Durand--Romashchenko (arXiv:1802.01461, abstract quoted at source).
- **Freeness.** It passes from `Y` to `X` through plane invariance, which is
  what Attempt 2 lacked.
- **Established along the way.**
  `plane-constant-minimal-sft-factors-are-effective-minimal` (unreviewed): every
  plane-invariant equivariant factor of a minimal SFT over `Λ_0 x Z^2` is
  effectively closed, minimal, and has decidable language. So every design with
  a free plane-invariant `Λ_0`-factor must prove (M2) for `Λ_0` first.
- **Dead sub-idea.** A minimal subsystem of the Aubrun--Barbieri--Thomassé
  effective strongly aperiodic subshift gives (M2) only if that subsystem is
  effectively closed, and Zorn gives no control.
- **Where it stops.** Neither premise is proved.
  - (M2) is known by hand for `Z^d` and products, but for no simple Kazhdan
    envelope.
  - (M1) is known only for `Λ_0 = Z^d`, in the DR form without plane invariance.
    Its named risk is exponential reading pressure for `Λ_0` of exponential
    growth.

**What would kill (P1) outright.** A finitely presented group `Λ` with solvable
word problem such that no finitely presented overgroup of `Λ` carries a minimal
free SFT. No invariant separating minimal SFTs from strongly aperiodic SFTs over
one-ended groups with solvable word problem is recorded in this graph.
