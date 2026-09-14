---
rg: 2
id: transported-gap-masa-kills-leavitt-hs-models
kind: claim
title: Scalar-gap Kazhdan blocks transported by one compressor force every HS model of the Leavitt group to be trivial
distinct_from:
  relative-wall-commutant-growth: that is the exact equivalence between a relative wall and growth of the relative commutant under a compressor, in any target; this proves that a maximal abelian subalgebra of the Kazhdan relative commutant cannot be carried back into that commutant while a commuting nonabelian subgroup survives, and turns the Leavitt block clauses into triviality of every model.
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: that exhibits a Kazhdan pair whose exact representation admits no compressor-monomial block decomposition; this shows that for the Leavitt triple such a decomposition, whenever it exists along an almost-representation sequence, already kills the sequence.
  hs-expander-block-decomposition: that is the open nested decomposition claim; this proves that its fine clauses plus the clause for the single compressor u already select the stable branch, with no coarse blocks, median, or second compressor.
  commutant-no-growth: that is dimension counting for genuine finite-dimensional representations; this is a masa argument valid in every finite von Neumann algebra, with no size and no counting.
artifacts:
  - c1168433:official/counterexample.tex
---

**ESTABLISHED.**

## (A) The hotel masa lemma, in any target

Let `Gamma <= G`, `t in G` with `t Gamma t^(-1) <= Gamma`, and let `J <= G`
satisfy `[Gamma,J]=1` and `t J t^(-1) <= Gamma`.  Let `(M,tau)` be a finite
von Neumann algebra, `sigma : G -> U(M)` a homomorphism, and
`A_0 = sigma(Gamma)' cap M`.

> If some maximal abelian subalgebra `B` of `A_0` satisfies
> `sigma(t) B sigma(t)^* <= A_0`, then `sigma([J,J]) = 1`.

So in a model where the commutator subgroup of `J` survives, every masa of
the Kazhdan relative commutant is pushed out of that commutant by the
compressor.  No size, trace or approximation enters.

## (B) The Leavitt application

Take the nine-leaf configuration of `openai-nine-leaf-leavitt-configuration`:
`R = L_(F_2)(1,2)`, `Gamma = EL_alpha(R) <= G = EL_D(R)`, the compressor `u`,
and `J = V_(1000) ~= V`.  Let `phi_n : G -> U(d_n)` have multiplicative
defects tending to zero pointwise in normalized Hilbert--Schmidt norm, and
suppose that for each `n` there are pairwise orthogonal projections
`p_(n,j)` with sum `p_n`, `tau(1 - p_n) -> 0`, and a constant `kappa' > 0`
such that:

```text
(F1) sum_j ||[phi_n(s), p_(n,j)]||_2^2 -> 0            for s in S_Gamma;
(F2) sum_(s in S_Gamma) sum_j ||[p_(n,j) phi_n(s) p_(n,j), x_j]||_2^2
       >= kappa'^2 sum_j ||x_j - tau_j(x_j) p_(n,j)||_2^2 - o(1)
       for all self-adjoint x = sum_j x_j, x_j in p_(n,j) M p_(n,j),
       ||x||_op <= 1   (tau_j the normalized corner trace);
(MW) sum_j ||phi_n(u) p_(n,j) phi_n(u)^* - p_(n,sigma_n(j))||_2^2 -> 0
       for some maps sigma_n.
```

Then `||phi_n(g) - 1||_2 -> 0` for every `g in G`.

`(F2)` is implied by the per-block scalar adjoint gap of
`hs-expander-block-decomposition`.  Only operator-bounded observables are
used, so no anti-spike control is needed.

## (C) Consequence

The fine clauses and the `u`-transport clause of the corrected
`hs-expander-block-decomposition` already give `leavitt-steinberg-hs-stable`.
A hyperlinear approximation of `G` would satisfy them and yet stay separated,
which is impossible, so `G` is nonhyperlinear.  `G ~= EL_4(R)`
(`leavitt-gl-equals-el-and-perfect-unit-group`), so `Q = EL_4(R)` is
nonhyperlinear, which is the stable branch by
`steinberg-hs-stability-equals-nonhyperlinearity`.  None of the coarse
ambient blocks, the median concentration
(`tracial-median-concentration`), the majority matching, or the second
compressor `v` is used.

## The differential this isolates

The permutation proof works with Kun's expander components.  Their atom
algebra `l^infinity(components)` commutes with the model of `Gamma` but is far
from maximal abelian in the relative commutant: on `l^2(C)` the action of
`Gamma` has a large commutant, because expansion is a *vector-level* gap
around the constant vector.  `J` may act inside a component, and exactness
comes from the finite automorphism group of an expander.

Normalized Hilbert--Schmidt norm cannot see single vectors: a rank-one vector
sector is `O(d^(-1/2))` in `||.||_2`, the phenomenon recorded as `(HS2)` in
`hs-analogue-of-normal-kazhdan-criterion-is-false`.  The only tracially
visible gap is the adjoint gap `(F2)`, and its atom algebra is a masa of the
relative commutant (step 2 of the derivation).  So the normalized-HS
transcription does not replace "`u` permutes expander components" by an
analogue; it replaces it by "`u` transports a masa of `A_0`", which `(A)`
forbids outright in any faithful model.  The two halves of that transcription
are:

* no intermediate endgame: with non-scalar block commutants, `J` lands in the
  unitary groups of those commutants, which carry no exactness and no
  contradiction for `V` unless `V` itself is nonhyperlinear; and
* with scalar blocks, the clause is already of the strength of the branch.

The operator-norm mechanism fails at a different step: the transport of the
Kazhdan projection, recorded in
`hs-analogue-of-normal-kazhdan-criterion-is-false`.

## What a nontrivial model must carry

Conversely, let `sigma` be any model with `sigma(J) != 1`.  Put
`Gamma_k = u^k Gamma u^(-k)`, `A_k = sigma(Gamma_k)' cap M` and
`V_k = u^k J u^(-k)`.  Then:

* `A_0 < A_1 < A_2 < ...` strictly, with `A_(k+1) = sigma(u) A_k sigma(u)^*`;
* `R_k = A_k cap A_(k-1)'` contains `sigma(V_k)`;
* the `R_k` pairwise commute; and
* `sigma(u) R_k sigma(u)^* = R_(k+1)`.

That is a one-sided shift of commuting subalgebras, each holding a Thompson
copy, inside the relative-commutant tower.  By `(A)`, none of the masas of
`A_k` lies in `A_(k-1)`.  This is the tracial Hilbert hotel an unstable-branch
construction has to realize.

Derivation: `transported-gap-masa-kills-leavitt-hs-models-proof`.
