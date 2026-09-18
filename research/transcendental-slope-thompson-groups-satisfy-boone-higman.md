---
rg: 2
id: transcendental-slope-thompson-groups-satisfy-boone-higman
kind: claim
title: For computable transcendental λ in (0,1), the derived irrational-slope Thompson group D(V_λ), a 2-generated simple group with solvable word problem that is not finitely presented, embeds in a finitely presented simple group
distinct_from:
  stein-derived-groups-need-computable-modules: that shows D(V_λ) embeds in no finitely presented simple group when λ is noncomputable; this is the complementary open case, where the word problem is solvable.
  norm-minus-one-sturmian-jm-groups-satisfy-boone-higman: that treats algebraic slopes of degree 2, where the derived group is itself finitely presented; for transcendental slopes it is not, so a genuinely new host is needed.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**OPEN.** A Boone--Higman test case.

`V_λ = V(Z[λ,λ^{-1}], ⟨λ⟩, 1)` with `λ ∈ (0,1)` computable and transcendental, for example `λ = 1/e` or
`λ = π − 3`.

## What is known about D(V_λ)

- **2-generated and simple.** Tanner, arXiv:2312.07375: `Z[λ^{±1}] ⋊ ⟨λ⟩ ≅ Z ≀ Z` is finitely generated.
- **Solvable word problem** (lane argument).
  - Since `λ` is transcendental, `Z[λ^{±1}] ≅ Z[t^{±1}]` as rings.
  - A word in the generators evaluates to a piecewise-linear map whose breakpoints and intercepts are Laurent
    polynomials evaluated at `λ`, and whose slopes are powers of `λ`.
  - Composing needs only order comparisons `p(λ) < q(λ)`. These are decidable: `p(λ) − q(λ) ≠ 0` unless
    `p = q`, so computing `λ` to increasing precision settles the sign.
  - A map is the identity iff every piece has slope 1 and intercept 0.
- **Not finitely presented**, conditional on Tanner's computation `H_2(D(V_λ);Q) ≅ ⊕_{i≥1} Q`.
- **Contains** the Juschenko--Monod group `IE(Z+Zα)'` for every irrational `α ∈ Z[λ^{±1}]`: the Sturmian
  derived full group of angle `α`.

So Boone--Higman predicts an embedding into a finitely presented simple group, and none is known. A positive
answer would also give Boone--Higman for the Sturmian Juschenko--Monod groups with angles in `Z[λ^{±1}]`.
Transcendental angles are not covered by `norm-minus-one-sturmian-jm-groups-satisfy-boone-higman`.

## Why the obvious hosts fail

- **`D(V_λ)` itself** is not finitely presented (Tanner's homology).
- **Algebraic Stein groups** cannot contain `IE(Z+Zλ)` through the natural interval-exchange embedding, since
  that needs `λ` in the breakpoint module. Abstract embeddings are not excluded.

A host must therefore break the piecewise-linear structure, for example with germs or near actions at the
transcendental breakpoints, while keeping the order on `Z[t^{±1}]` computable.

## Why the Pisot RSG route does not reach this case (09-18)

`pisot-stein-groups-are-contracting-rsgs` codes `[0,1)` by the β-shift. It gets a finite nucleus from Pisot
lattice finiteness:
- the offsets of local actions lie in `Z[β]`;
- all their conjugates are bounded;
- such a set is finite.

For transcendental `λ` there are no conjugates, and no β-shift coding makes the translations by `Z[λ^{±1}]`
act with finitely many local actions. For any coding by a fixed SFT with finitely many states, the offsets
`d ∈ Z[λ^{±1}] ∩ [0,1)` arising at deep cones would have to form a finite set closed under the renormalization
`d ↦ λ^{-1}d − (digit)`. That forces `λ` to be algebraic. So a host for this case must be something other than
a contracting RSG over such a coding. This is a heuristic remark, not a proof.
