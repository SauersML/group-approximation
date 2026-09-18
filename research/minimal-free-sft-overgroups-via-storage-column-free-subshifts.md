---
rg: 2
id: minimal-free-sft-overgroups-via-storage-column-free-subshifts
kind: route
title: Clapham, a storage column Z giving a decidable free subshift, tree gluing over one more Z, and the keyed-slot lift over Z^2 put every decidable group inside a finitely presented group with a minimal free SFT
target: decidable-groups-embed-in-fp-groups-with-minimal-free-sft
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-groups-times-z-have-decidable-free-subshifts
  - free-products-with-z-inherit-m2-from-decidable-free-subshifts
  - free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2
---

**Route. COMPLETE modulo its premises.** All four premises are on main as lane proofs,
none independently reviewed:
- Clapham is an import;
- the (D) instance is by bh-g1-bss (this pass);
- the tree gluing, (D) ⇒ (M2) for `A * Z`, is by bh-g1-universal-point, 876c511de;
- the keyed-slot lift over `Z^2` is by bh-g1-simulation, 695a89096. It is a design-level
  proof: the Durand–Romashchenko frames are adapted, not re-derived.

If the premises stand, gate E1 of the master route (existence of a minimal free SFT over a
finitely presented overgroup of every decidable input) is established.

## Proof

Let `K` be finitely generated with solvable word problem.
1. **Envelope.** `K x F_2` embeds in a finitely presented `Λ_1` with solvable word problem
   (`clapham-fp-embedding-preserves-word-problem`).
2. **Storage column.** Put `A = Λ_1 x Z`. It is finitely presented, infinite, has solvable
   word problem, and contains `K`. By
   `decidable-groups-times-z-have-decidable-free-subshifts`, `A` carries a
   nonempty free subshift with decidable language. This is premise (D) for `A`.
   - *Conventions.* That node uses the left action `(g·y)(x) = y(g^{-1}x)`, and the gluing node
     uses `(λ·z)(μ) = z(μλ)`. The map `y ↦ (x ↦ y(x^{-1}))` conjugates the two. It moves
     patterns on `F` to patterns on `F^{-1}`, so it preserves freeness and decidability of the
     language.
3. **Tree gluing.** By `free-products-with-z-inherit-m2-from-decidable-free-subshifts`,
   `A' = A * Z` carries an effectively closed minimal free subshift `Y_1`. `A'` is finitely
   presented, has solvable word problem (normal forms), and contains `K`.
4. **Lift.** By `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2`, applied with
   `Λ_0 = A'` and `Y = Y_1`, the group `Λ = A' x Z^2` carries a nonempty minimal free SFT.
   - It is free for all of `Λ`, not only for `A'`.
   - `Λ` is finitely presented, infinite, and contains `K`.

So `Λ = ((Λ_1 x Z) * Z) x Z^2` witnesses the target for `K`. ∎

## Where each Z is spent

- **The first `Z`: storage.** It gives every point of `Λ_1` a private Toeplitz column. Each
  aperiodicity scale then lives on its own rows, and every constraint is greedily completable.
  This is decidability.
- **The second `Z`: gluing.** Its Bass–Serre tree glues computable library points into one
  minimal system. This is minimality.
- **The `Z^2`: finite type.** It carries the Durand–Romashchenko hierarchy with keyed slots.
  This turns an effective minimal free input into a minimal free SFT.

## Checks

- **Necessity is respected.**
  - `Λ` has solvable word problem, as Jeandel requires.
  - `Λ` is one-ended, as Cohen requires: it contains `Z^2` as a direct factor of an infinite
    group, and a direct product of two infinite finitely generated groups is one-ended.
  - `Λ` contains `F_2`, so the non-amenability that later gates need (E3, SYNTHESIS v4) is
    present.
- **Downstream.** Topological freeness suffices downstream (bh-g3-topfree, 2914b739e). The
  lift gives full freeness anyway.
- **What a referee should check first.**
  - The keyed-slot lift's transfer of the Durand–Romashchenko frame properties. It is
    flagged as not re-derived in its own node.
  - The finite-search claim in Step 3 of the (D) proof: maximal nets extend from any
    admissible patch plus one annulus.

## Lesson for general BH

Gate E1 splits into three independent resources, each bought with one cheap factor.
- Decidability is bought with a storage `Z`: independent scales give greedily completable
  constraints.
- Minimality is bought with a gluing `Z`: the Bass–Serre tree.
- Finite type is bought with `Z^2`: the fixed-point hierarchy with keyed slots.

None of them needs anything from the input beyond a solvable word problem. So the existence
side of the master route is now closed modulo review, and all remaining weight sits on the
rigidity gate E2 and the combinatorial gate E3.

## Referee (bh-ref-e1-a, 2026-09-18): Steps 1–3 PASS; Step 4 not refereed here

- **Step 1.** Clapham 1967 is the standard import. Its Theorem 6 construction was read at
  source by bh-invent-14 (0d6bf2845). `K x F_2` is finitely generated with solvable word
  problem.
- **Step 2.** (D) holds for `Λ_1 x Z` by `decidable-groups-times-z-have-decidable-free-subshifts`
  (PASS). The conjugation of conventions is correct.
- **Step 3.** `free-products-with-z-inherit-m2-from-decidable-free-subshifts` holds (PASS),
  with the B-top Sturmian-window repair recorded there.
- **Step 4** rests on `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2`
  (695a89096). That proof is design-level and was not refereed here. So gate E1 is
  established **conditional on that lift**. The (D) → (M2) half of E1 is now referee-checked.
- **The second (D) route is not needed.** It is `identifier-markers-give-decidable-free-subshifts`
  (f9ae89eb9), and its Lemma (E) is not established. This route suffices without it.

## Referee (bh-ref-e1-b, 2026-09-18): composition PASS; SFT-lift premise PASS conditional on repair G1

Independent referee 1 of 2, for the SFT-lift half and the composition. The (D) premise and the tree
gluing are refereed separately (bh-ref-e1-a).

**Interfaces, checked step by step.**
- **Clapham → storage column.** `A = Λ_1 x Z` is finitely generated and finitely presented, has
  solvable word problem, is infinite, and contains `K`.
- **(D) → gluing.** The gluing node needs `A` finitely generated with solvable word problem, and a
  nonempty free subshift over a *finite* alphabet with decidable language. The (D) node supplies
  exactly this, after the inversion map `y ↦ y∘inv` that the route records.
- **Gluing → lift.** The gluing output is a nonempty minimal free subshift of `Γ = A * Z` with
  *decidable language*, so its forbidden patterns are recursively enumerable and it is effectively
  closed. `Γ` is finitely generated with solvable word problem (normal forms).
  - The same inversion map is needed here too, because the gluing node uses `(λ·z)(μ) = z(μλ)` and
    the lift uses the left action. The route mentions it only at step 2.
  - The map conjugates the actions (with `y(h) = z(h^{-1})`, `λ·z` goes to `λ·y`), so it preserves
    minimality and freeness. Effective closedness is preserved because `F ↦ F^{-1}` is computable.
  - Cosmetic: add the sentence at step 3.
- **Lift → target.** `Λ = (A * Z) x Z^2` is finitely presented, infinite, contains `K`, and
  carries a nonempty minimal SFT on which all of `Λ` acts freely. That is exactly
  `decidable-groups-embed-in-fp-groups-with-minimal-free-sft` for `K`.
- **Consistency with necessity.**
  - Jeandel: `Λ` has solvable word problem.
  - Cohen: `Λ` is one-ended.
  - No known obstruction is violated.

**Status of the lift premise.** PASS at design level, conditional on repair G1 recorded on
`keyed-diversification-slots-give-plane-constant-minimal-lifts`. Slot keys must be the full input
field `(τ_K, τ_K^{(s)}, τ_{K+1})`, not `τ_K` alone. This is a local change, with an adjusted growth
condition.

**Verdict.** If the (D) and gluing premises pass their own review, and G1 is written in, this route
establishes gate E1 (P1). Credit is due to Clapham (1967), to Durand–Romashchenko(–Shen) for the
fixed-point and slot machinery, and to Jeandel and Cohen for the necessity checks.
