---
rg: 2
id: quotientless-kazhdan-relation-hosts-collapse-to-subgroups
kind: claim
title: Relation-host certificates of the SQK gate collapse - quotientless Kazhdan groups act trivially through hyperfinite and Haagerup full groups, and a torsion-free Kazhdan Bernoulli relation inside a free orbit relation forces a subgroup embedding
distinct_from:
  simple-kazhdan-bernoulli-relation-hosts-contain-the-group: that proves the containment-forces-embedding statement for infinite simple Kazhdan groups, using simplicity for injectivity; this replaces simplicity by torsion-freeness (kernel ergodicity plus no finite normal subgroup), which is the hypothesis the SQK gate actually supplies, and adds the full-group clauses for arbitrary actions
  haagerup-hosts-blind-full-group-kazhdan-certificate: that proves finite orbits for every Kazhdan group acting through a Haagerup full group; this uses it, adds that finite orbits of a quotientless group are fixed points, and aims the result at the soficity gate instead of the Kun--Thom certificate
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that treats bounded piecewise translations of free amenable actions; this treats the whole measurable full group of an arbitrary hyperfinite relation
  torsion-free-sofic-quotientless-kazhdan-group-exists: that is the open gate (SQK); this kills the relation-host reframing of it, except for an explicit survivor class
  exact-kazhdan-radical-kernel-cannot-be-lef: that records the false (EKL2) and the summit-hard torsion-free repair; this is about host relations, not local models
---

**ESTABLISHED.** Call a group *quotientless* if it has no nontrivial finite quotient. Let `Γ` be a
nontrivial, torsion-free, quotientless group with property (T). So `Γ` is exactly a candidate witness of
`torsion-free-sofic-quotientless-kazhdan-group-exists` (SQK) with soficity not yet known.

**Why this matters (the reframing being killed).** By Elek (*Full groups and soficity*, arXiv:1211.0621,
Thm 1) every countable subgroup of the measurable full group `[R]` of a sofic p.m.p. relation `R` is
sofic, and by Elek--Lippner `Γ` is sofic iff its Bernoulli relation is. So (SQK) is equivalent to

```text
(RH)  some sofic p.m.p. relation R admits an injective homomorphism rho : Γ -> [R],
      for some Γ as above,
```

(Injectivity is needed for the reverse direction: a noninjective `ρ ≠ 1` only makes the quotient `ρ(Γ)`
sofic, and that quotient may have torsion. Clauses 3 and 4 below kill every `ρ ≠ 1`, injective or not.)

and the natural way to certify it is to take `R` from a known sofic source. For example, `R` could be
hyperfinite, the orbit relation of a free action of a residually finite, linear or Haagerup group, or a
relation into which the Bernoulli relation of `Γ` is placed. This node proves that each of these
sources fails at a named step.

## Statement

Let `R` be a p.m.p. countable Borel equivalence relation on a standard probability space `(X, μ)` and
`ρ : Γ → [R]` a homomorphism.

1. **Finite orbits are fixed.** After discarding a `ρ(Γ)`-invariant null set, every point with a finite
   `ρ(Γ)`-orbit is fixed by all of `ρ(Γ)`. So on `Supp ρ = X ∖ Fix ρ(Γ)` every orbit is infinite.
2. **Every ergodic action is weakly mixing.** Every ergodic p.m.p. action of `Γ` is weakly mixing, and
   by (T) strongly ergodic. In particular `Γ` has no nontrivial ergodic action with discrete spectrum:
   no nontrivial compact, profinite or odometer action.
3. **Hyperfinite hosts are blind.** If `R` is hyperfinite, then `ρ(Γ) = 1` in `[R]`.
4. **Haagerup hosts are blind.** If `R ⊆ R_G` (mod null) for an essentially free p.m.p. action of a
   countable group `G` with the Haagerup property, then `ρ(Γ) = 1` in `[R]`. This covers amenable,
   free, surface, `F_2 × F_2`, `SO(n,1)`- and `SU(n,1)`-lattice and CAT(0)-cubical hosts.
5. **Bernoulli containment is a subgroup certificate.** Let `β : Γ ↷ (Y,ν) = ([0,1]^Γ, Leb^(⊗Γ))`.
   Let `H ↷ (X,μ)` be an essentially free p.m.p. action of a countable group, `A ⊆ X` with
   `μ(A) > 0`, and `θ : (Y,ν) → (A, μ_A)` a measure-space isomorphism with `θ(γy) ∈ H·θ(y)` for all
   `γ` and a.e. `y`. Then there is an **injective** homomorphism `δ : Γ → H`, together with a
   measurable `ψ : Y → X` such that `ψ(γy) = δ(γ)ψ(y)`. Clause 5 uses only that `Γ` is infinite,
   torsion-free and Kazhdan.
6. **Consequence for residually finite hosts.** In clause 5, `H` cannot be residually finite, and in
   particular cannot be linear. Otherwise `δ(Γ) ≅ Γ` would be a nontrivial residually finite group with
   no finite quotient. Likewise `H` cannot be amenable or Haagerup, since an infinite Kazhdan subgroup
   is impossible there.

Proof: `quotientless-kazhdan-relation-hosts-collapse-proof`.

## Class killed, and where each member dies

A relation-host certificate of (SQK) produces `(R, ρ)` as in (RH) from a sofic source. Each member dies
at a named step:

- **Hyperfinite or amenable relations**, including every orbit relation of an amenable group, die at
  clause 3.
- **Full groups over free actions of Haagerup groups** die at clause 4. The step is that the
  Haagerup finite-orbit theorem feeds clause 1.
- **Bernoulli-relation embeddings** (the Elek--Lippner route) die at clause 5. Placing the
  diffuse-base Bernoulli relation of `Γ`, even on a positive-measure piece, inside a free orbit
  relation of a sofic group `H` returns `Γ ≤ H`. So the relation certificate is literally the
  subgroup certificate "`Γ` is a subgroup of a sofic group", and it adds nothing. For every residually
  finite, linear, amenable or Haagerup `H`, it is impossible (clause 6).
- **Compact, profinite and exactly periodic models of the `Γ`-action itself** die at clause 2.

**Survivors.** A relation-host proof of (SQK) must use an action `ρ` of `Γ` with all of these
properties:

- the action is weakly mixing and strongly ergodic on each component of `Supp ρ` (clause 2);
- it is not an s-malleable (Bernoulli-type) action placed in a free orbit relation of a group not
  already containing `Γ` (clause 5);
- it lies in a relation that is non-hyperfinite, and on `Supp ρ` is contained in no free orbit
  relation of a Haagerup group (clauses 3 and 4).

Concretely, the host must be something like the orbit relation of `SL_3(Z) ↷ T^3`, or of a free
action of a non-Haagerup residually finite group, or a relation not generated by any free action. And
the `Γ`-action must be a non-malleable action of the kind produced by piecewise constructions. No
such `ρ` with `Γ` torsion-free is known.

**Calibration.**
- Clause 5 with torsion is false as stated. With torsion, `δ` has finite kernel, and injectivity
  needs torsion-freeness or simplicity; compare
  `simple-kazhdan-bernoulli-relation-hosts-contain-the-group`.
- Clause 1 is false without quotientlessness: `SL_3(Z)` acts through `[R]` with finite orbits
  via its congruence quotients.
- Extending clauses 3–4 to arbitrary sofic `R` would refute (SQK), since for sofic `Γ` its own
  Bernoulli relation is a sofic host carrying the injective Bernoulli `ρ`. So no such extension
  is available without deciding the gate.

**Credit.** Clauses 1, 2 and 6 are elementary. Clause 3 is folklore in the form "Kazhdan groups act
through hyperfinite full groups with finite orbits". Clause 5 is the standard Popa untwisting behind
OE superrigidity; no novelty is claimed for it beyond replacing simplicity by torsion-freeness. The
new content is the assembly into a kill of the relation-host reframing of the SQK gate, with the
survivor class stated.
