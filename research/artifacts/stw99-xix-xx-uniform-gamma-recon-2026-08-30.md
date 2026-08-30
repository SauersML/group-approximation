---
title: STW Problems XIX and XX --- uniform property Gamma recon on diagonal AH models (2026-08-30)
---

Problem XIX (CETW Question C): does every unital simple separable nuclear
non-elementary stably finite C\*-algebra have uniform property Γ?
Problem XX: the Villadsen-V1 test case.  Elliott--Niu (arXiv 2024) rule
out Γ-witnesses inside the canonical Cartan.  This recon fixes what any
resolution must do, on the diagonal AH model
`A = lim (C(X_n) ⊗ M_{k_n}, φ_n)`, `φ_n(f) = diag(f∘λ_1, …, f∘λ_N)` with
`λ_i` either coordinate projections (`X_{n+1} = X_n^{c_n} × …`) or point
evaluations, identity weight `w_n = c_n k_n / k_{n+1}`, `Π w_n → w > 0`
in the Villadsen regime.

## 1. Central sequences away from coincidence are block selectors

At a point `y` of a deep stage where the values `a(λ_i(y))` of the test
elements are pairwise distinct for enough `a`, the relative commutant of
the image fibre `{diag(a(λ_1 y), …, a(λ_N y))}` is the block scalars, and
`ε`-commutation in the fibre trace norm forces a projection to be
trace-close to a union of blocks.  So a central-sequence projection is,
generically, a block subset `S` at its stage.

## 2. Block subsets fail uniform halving by `~ w/4`

The limit traces restricted to a stage include atomic diagonal states: a
point of a deeper stage all of whose identity coordinates equal a single
`x` induces on the earlier stage `w·(evaluation at the diagonal point) +
(1−w)·(evaluation-branch average)`.  Fix a block subset `S` containing
half of the identity blocks.  Choose `h = tr̄ a(·)` with `h = 1` on the
part of the diagonal hit by `S`'s coordinates and `h = 0` elsewhere:
against the atomic diagonal trace at that configuration,
`τ(χ_S φ(a)) − τ(φ(a))/2` has magnitude on the order of `w/4` times the
identity mass.  Uniform Γ demands halving against *all* limit traces, so
constant block selectors never witness it.  (With all connecting
multiplicities even and paired equal maps the obstruction vanishes — but
Villadsen towers use multiplicity-one distinct coordinates.)

## 3. The obstruction and the witness meet on the coincidence locus

The adversarial traces of §2 concentrate on diagonal configurations where
all identity coordinates agree.  There the image fibre has repeated
blocks, its commutant contains `M_{N_id}` mixing the equal blocks, and
rank-half projections in that commutant halve the atomic trace exactly.
So §1's forcing fails precisely where §2's adversary lives: the two cheap
arguments annihilate.  Uniform Γ for these models is equivalent to the
existence of projection-valued selections of half rank that are
(i) 2-norm approximately central, hence block-selecting away from
coincidence loci and mixing along them, and (ii) uniformly trace-halving;
i.e. a selection problem over the stratification of `X_M` by coincidence
patterns of the identity coordinates.  A negative resolution should turn
the Villadsen Euler-class obstruction (which already forbids norm-central
*trivialised* halvings via the Cartan, per Elliott--Niu) into an
obstruction for arbitrary measurable-uniform selections; a positive one
should glue the within-stratum rotations — a CPoU-type task with the same
signature as the rank ≥ 2 case of the trace problem
(`stw99-problem-xxii-tracial-completion-traces-continuous`).

## 4. Unique-trace nuclear algebras always have uniform Γ

Sato's surjection `(A^ω ∩ A')/(J_τ ∩ ·) → R^ω ∩ R'` for nuclear `A` with
faithful trace `τ`, together with the Kirchberg--Rørdam σ-ideal
projection lifting, hands the halving projections of the McDuff `R` to
`A^ω ∩ A'`.  So a counterexample to XIX must have a nontrivial trace
simplex, and the Villadsen algebras relevant to XX are the multi-trace
ones.

Sources: Castillejos--Evington--Tikuisis--White, IMRN (Question C);
Castillejos--Evington--Tikuisis--White--Winter, Invent. Math. 224 (2021)
(uniform Γ, CPoU); Elliott--Niu arXiv 2024; Kirchberg--Rørdam
arXiv:1209.5311 (σ-ideals, Sato's theorem); Villadsen JFA 154 (1998).
