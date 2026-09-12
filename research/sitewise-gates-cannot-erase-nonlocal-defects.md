---
rg: 2
id: sitewise-gates-cannot-erase-nonlocal-defects
kind: claim
title: A sitewise gate that reads a functional copy with a nonlocal remainder and must return a local value cannot read the copy
distinct_from:
  formalizable-left-inverse-iff-clean-shear-dilation: that locates the Bennett remainder in the erasure step; this proves that no sitewise gate, on any enlarged alphabet, removes a nonlocal remainder from a clean track.
  structurally-reversible-automata-are-formalizable: that shows words in gates are formal involutions; this shows that in the erasure step, sitewise gates cannot use a functional copy whose remainder is nonlocal.
artifacts:
  - research/artifacts/stable-formalization-erasure-audit-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `k` be a field and `S` a finite set of variables. Let `c ∈ k[S]`, and let `d` be a polynomial
involving some variable outside `S`. If `F ∈ k[S][w]` satisfies `F(c + d) ∈ k[S]`, then `F` does not
depend on `w`.

**Application: erasure in the Bennett dilation.**
- **The copy.** The formal copy of the data at cell `g` is `w_g = X_g − d_g`, with remainder
  `d = X − σ~(τ~(X))`.
- **Local variables.** Take `S` to be the variables at cell `g` still held by untouched tracks: the
  data variable, and identity-track variables.
- **Nonlocal remainder.** Suppose `d_g` involves a variable outside cell `g`.
- **Conclusion.** Any sitewise gate component that reads `w_g` and must return a local value (`0` on
  a clean track, or `X_g`, or `Y_g`) does not read `w_g` at all.
- **So:** no sitewise step clears a nonlocal remainder onto a clean track, whatever the enlarged
  alphabet and whichever tame realization of a symbol permutation is used.
- **What remains.** Erasure must read the window of `d`, or send the remainder into identity-track
  outputs. There `invertible-ancilla-outputs-collapse-stable-formalization` applies.

**Scope.** The algebraic statement holds verbatim over every group. "Sitewise" is relative to the
chosen sites.
- **Which gates.** The conclusion covers gate components that read only `S` and the copy `w_g`.
  A gate that also reads other modified tracks at cell `g`, for instance the output track `U_g`, is
  not covered. The remainder may be algebraically dependent on those values over `k(S)`, and then the
  transcendence argument does not apply.
- **After regrouping.** If `G` has a proper finite-index subgroup `H`, the automaton can be regrouped
  along `H`. A site is then a block of cells, `S` is the variables of a block, and only remainders
  involving variables outside the block are nonlocal. Regrouping can therefore escape this obstruction,
  as `marker-involution-is-formalizable-after-regrouping` does over `4Z`.
- **Without regrouping.** On hosts with no proper finite-index subgroup, such as finitely generated
  simple hosts, sites are single cells and the claim applies as stated.

Proof: Section 3 of the artifact (`d` is transcendental over `k(S)`).
