---
rg: 2
id: minimal-free-sft-via-minimal-self-simulation-of-squares
kind: route
title: The square of the Clapham envelope of K x F_2 carries a minimal free SFT, given (M2) for the envelope and minimal self-simulation for the square
target: decidable-groups-embed-in-fp-groups-with-minimal-free-sft
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-fp-groups-have-effective-minimal-free-subshifts
  - nonamenable-products-have-minimal-sft-extensions-of-free-inputs
artifacts:
  - research/artifacts/gq-bh-bh-g1-simulation.md
---

**Route. OPEN.** The implication below is complete; it fires once its two open premises
hold:
- (M2) `decidable-fp-groups-have-effective-minimal-free-subshifts`, needed for the
  envelope `Λ_1`;
- (MSS) `nonamenable-products-have-minimal-sft-extensions-of-free-inputs`, needed for
  the square `Λ_1 x Λ_1`.

This is a lane proof, elementary and unreviewed.

## Proof of the implication

Let `K` be a finitely generated group with solvable word problem.
1. **Make the input non-amenable.** Put `K' = K x F_2`. It is finitely generated, has
   solvable word problem, contains `K`, and is non-amenable.
2. **Envelope.** By `clapham-fp-embedding-preserves-word-problem`, `K'` embeds in a
   finitely presented `Λ_1` with solvable word problem. `Λ_1` is infinite and
   non-amenable, since it contains `F_2`.
3. **Square.** `Λ = Λ_1 x Λ_1` is finitely presented. It has solvable word problem,
   because normal forms split into coordinates. It contains `K` in the first factor, and
   it is a product of two finitely generated non-amenable groups.
4. **(M2).** Take an effectively closed, minimal, free subshift `Y_1 ⊆ B^{Λ_1}`, and put
   `Y = {(λ,μ) ↦ (y(λ), y'(μ)) : y, y' ∈ Y_1} ⊆ (B x B)^Λ`.
   - `Y` is effectively closed. Two families of patterns are forbidden:
     - nearest-neighbour patterns in which the first letter changes along a generator of
       the second factor, or the second letter along a generator of the first (finite
       type);
     - the r.e. forbidden patterns of `Y_1`, placed in each coordinate along the
       corresponding factor.
   - `Y` is minimal: the orbit of `(y,y')` is `(Λ_1·y) x (Λ_1·y')`, a product of dense
     sets.
   - `Y` is free: the stabilizer of `(y,y')` is `Stab(y) x Stab(y') = 1`.
5. **(MSS).** It gives a nonempty minimal SFT `Z` over `Λ` and a factor map `Z -> Y`.
6. **Freeness.** `Z` is free, since a point's stabilizer fixes its image in `Y`.
7. **Conclusion.** The finitely presented `Λ ⊇ K` carries a nonempty minimal free SFT.
   This is (P1) for `K`.

## Comparison with the Z^2 route

The Z^2 route is `minimal-free-sft-via-plane-constant-minimal-simulation`.
- **What is the same.** The same (M2) premise, now for `Λ_1` rather than `Λ_1 x Z`.
- **What is absent.**
  - no plane-invariance and no hierarchy requirement on the simulation;
  - the design class of `plane-constant-minimal-sft-factors-are-effective-minimal` is
    never entered;
  - there is no reading pressure: the BSS coherence rules compare each cell with `|S|`
    neighbours only (read at source).
- **The price.**
  - (MSS) is open for every non-amenable product; it is BSS's printed Question
    `Q:minimal`, restricted.
  - It carries its own diversification crux, a phase field on unanchored grids, recorded
    on the premise node.
- **What this route does not give.** (P1) is existence only. Quantum rigidity (gate G2)
  is not addressed.

## Lesson for general BH

The non-amenable factor supplies, for free, the geometry that the amenable direction had
to build hierarchically: bounded 2-to-1 maps give disjoint grids.
- So in the non-amenable-product setting, G1 splits cleanly into existence (M2) and one
  minimality question.
- That minimality question is the same joint-diversification problem as on `Z^2`, now for
  the phases of per-grid hierarchies.
- A minimal, relationally coupled field of hierarchy phases over a group containing the
  input is the common core of both G1 routes. Functional couplings are excluded by
  `simple-subgroups-act-trivially-on-equicontinuous-factors`.
