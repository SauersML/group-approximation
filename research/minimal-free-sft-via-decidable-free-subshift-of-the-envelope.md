---
rg: 2
id: minimal-free-sft-via-decidable-free-subshift-of-the-envelope
kind: route
title: A decidable-language free subshift on the Clapham envelope, plus minimal self-simulation of squares, gives a minimal free SFT over an fp group containing the input
target: decidable-groups-embed-in-fp-groups-with-minimal-free-sft
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-groups-carry-free-subshifts-with-decidable-language
  - free-products-with-z-inherit-m2-from-decidable-free-subshifts
  - nonamenable-products-have-minimal-sft-extensions-of-free-inputs
---

**Route. OPEN.** The implication is complete, and it fires once its two open premises hold:
- (D) `decidable-groups-carry-free-subshifts-with-decidable-language`, needed for one
  envelope;
- (MSS) `nonamenable-products-have-minimal-sft-extensions-of-free-inputs`.

It replaces the (M2) premise of `minimal-free-sft-via-minimal-self-simulation-of-squares`
by (D), which asks for no minimality, recurrence or universal point. Lane proof, unreviewed.

## Proof of the implication

Let `K` be finitely generated with solvable word problem.
1. **Envelope.** `K' = K × F_2` embeds in a finitely presented `Λ_1` with solvable word
   problem (`clapham-fp-embedding-preserves-word-problem`).
2. **(D) ⇒ (M2) one step up.** Put `Λ_1' = Λ_1 * Z`. It is finitely presented, has solvable
   word problem (normal forms), is non-amenable, and contains `K`. By (D) for `Λ_1` and
   `free-products-with-z-inherit-m2-from-decidable-free-subshifts`, `Λ_1'` carries an
   effectively closed minimal free subshift `Y_1`.
3. **Square.** Put `Λ = Λ_1' × Λ_1'`. It is finitely presented, decidable, a product of two
   f.g. non-amenable groups, and contains `K`. The product subshift `Y = Y_1 × Y_1` (each
   letter constant along the other factor) is effectively closed, minimal and free. These are
   steps 4–6 of `minimal-free-sft-via-minimal-self-simulation-of-squares`, with `Λ_1'` in
   place of `Λ_1`.
4. **(MSS).** It gives a nonempty minimal SFT `Z → Y` over `Λ`. `Z` is free, because a
   stabilizer of a point fixes its image.

So the finitely presented `Λ ⊇ K` carries a nonempty minimal free SFT. ∎

## What the substitution changes

- **Minimality leaves the envelope.** It was the part of (M2) that no attempt on main made
  effective: Zorn, greedy towers, the local lemma. Now it comes from the Bass–Serre tree of
  `Λ_1 * Z`. The only property asked of `Λ_1` is that some free subshift has a decidable
  extension problem.
- **The premise is necessary one level up.** The final `Z` is minimal and effectively
  closed, so it has decidable language. It is therefore itself an instance of (D) for `Λ`.
  Every route to E1 through an SFT on `Λ` passes through (D) for `Λ`. This route asks for
  (D) only on the smaller group `Λ_1`, where the input sits.
- **Caution for E2.** `Λ_1 * Z` has infinitely many ends. So the E2 necessary condition of the master route, "no single free branch over a factor with at least two ends", now applies to both factors of `Λ`. The SFT that (MSS) produces must pass the single-branch determinism check before it can feed E2; this route only settles existence. E3 is unaffected, since `Λ` is still a non-amenable product.

## Lesson for general BH

The existence gate E1 now has no dynamical premise on the input side, beyond BSS's
minimal-simulation question. Its input premise is a single effectivity statement, a
decidable `Π⁰₁` free subshift on some fp overgroup of `K × F_2`. The free factor `Z` is
the whole cost of trading minimality for decidability.
