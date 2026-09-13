---
rg: 2
id: irs-rigid-simple-dense-subgroups-act-properly-outer
kind: claim
title: A simple IRS-rigid dense subgroup with an escaping element acts properly outerly in every ergodic tracial action of a simple Howe-Moore group
distinct_from:
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that applies IRS rigidity to finite permutation almost actions; this applies it to trace-preserving actions of an ambient Howe--Moore group on finite von Neumann algebras.
  creutz-peterson-factor-representation-rigidity-steps: that imports the Creutz--Peterson steps that consume proper outerness; this supplies proper outerness without a square-integrable lattice.
---

**ESTABLISHED (unreviewed).** Let `G` be a second countable locally compact group that is
topologically simple and has the Howe--Moore property. Let `Λ < G` be a countable dense
subgroup such that

```text
(PO1) Λ is simple;
(PO2) every invariant random subgroup of Λ is t δ_e + (1-t) δ_Λ for some t in [0,1];
(PO3) some γ_0 in Λ satisfies γ_0^n -> infinity in G (it leaves every compact set).
```

Let `α : G -> Aut(M_0, τ)` be a continuous, ergodic, trace-preserving action on a finite von
Neumann algebra `M_0 ≠ C` with separable predual and faithful normal tracial state `τ`.
Continuity means continuity of `g -> α_g(x)` in `||·||_2` for every `x`. Then the restriction
of `α` to `Λ` is properly outer. That is, for `λ in Λ \ {e}` there is no nonzero `v in M_0`
with `α_λ(x) v = v x` for all `x in M_0`.

**What this replaces.** Creutz--Peterson's Proposition 4.1(ii) (arXiv:1311.4513v3) reaches
the same conclusion when `G` is simple and `Λ` contains and commensurates a square-integrable
lattice with a non-torsion element. In their proof that hypothesis is spent twice:
- in the non-factor case, to obtain finite stabilizers from [CrePet, Theorem 7.9];
- in the factor case, to supply a non-torsion element of a discrete lattice, which escapes
  to infinity.

Here IRS rigidity (PO2) replaces the first use, (PO3) replaces the second, and simplicity of
`Λ` (PO1) puts the escaping element among the inner automorphisms. Which hypotheses of
[CrePet, Theorem 7.9] actually need square-integrability was not audited here.

**Consequence.** Every step of Creutz--Peterson that uses Proposition 4.1 only through its
conclusion applies to such `Λ` (see `creutz-peterson-factor-representation-rigidity-steps`).
The instance is `S_q` inside each completion `L_±`
(`km-246-lattice-is-character-rigid`).

**Model test.**
- (PO2) holds for `S_q` (`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`). It fails
  for the derived topological full group of a minimal Cantor system, whose stabilizer IRS is
  nontrivial (`fp-infinite-simple-group-with-nontrivial-irs`). That is exactly the input the
  non-factor step uses.
- (PO3) is used only in the factor case. A dense subgroup all of whose elements lie in
  compact subgroups gives no mixing contradiction, and the proof does not treat it.

No novelty is claimed beyond the substitution.

Proof: `irs-rigid-dense-subgroup-proper-outerness-proof`.
