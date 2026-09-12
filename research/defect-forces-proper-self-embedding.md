---
rg: 2
id: defect-forces-proper-self-embedding
kind: claim
title: A nontrivial compression defect forces the stable letter to compress the core properly
distinct_from:
  concrete-compression-source: that claim builds a concrete source with nontrivial defect; this one is the structural converse constraint — WHICH core groups can ever carry one.
artifacts:
  - GroupApproximation/Sofic/ConcreteCompressionSource.lean
---

In any compression core (`ι : Γ → E`, stable letter `t` with
`t ι(γ) t⁻¹ = ι(α γ)`, mark `c` with `[c, ι(γ)] = 1` for all `γ`,
defect `N = ⟨⟨[tct⁻¹, ι(Γ)]⟩⟩`): if the induced `α : Γ → Γ` is
surjective, the defect is trivial.  Consequently a nontrivial defect
forces `α(Γ) ⊊ Γ` — a proper self-embedding of the core.

Two design corollaries for the torsion-free program.

1. **Co-Hopfian cores are useless.**  Higher-rank lattices (any
   congruence subgroup of `SL₃(ℤ)`, in particular) are co-Hopfian, so a
   torsion-free Kazhdan arithmetic core can never carry a nontrivial
   defect.  Worse, a faithful irreducible linear core of small degree
   admits no external element commuting with the compressed copy but
   not the whole copy (the centralizer of a congruence elementary
   subgroup in the matrix algebra is scalars), so the FF-style
   "commuting partner" pattern is also unavailable linearly.
2. **CORRECTED 2026-08-21 (the first version of this corollary was
   wrong and survived only hours):** the core's (T) field is NOT
   vestigial.  The W0 consumer trace, verified at source, shows the
   root-capture step
   (`MarkedCompressionRootCapture.transportedRoot_displacement_hsDistSq_vanishing`,
   line 243) opens by extracting a symmetric generating pair with a
   spectral gap from `C.kazhdan` — property (T) of the BASE.  A core
   over an amenable base proves nothing (an ascending HNN over `ℤ` is
   Baumslag–Solitar, amenable, hence MF — recorded as a theorem in
   `Sofic/BareDefectSource.lean`).  What the W0 slimming genuinely
   deletes is the simple-factor demand only.  Combined with this
   claim's forcing theorem, the surviving demand on the source is
   sharp: **a property-(T) group with a proper self-embedding, with a
   centralizing root and nontrivial marked commutator, realized inside
   a torsion-free finitely presented ambient**.  Since torsion-free
   hyperbolic (T) groups are co-Hopfian (Sela: co-Hopfian once freely
   indecomposable, and (T) forbids free splittings) and higher-rank
   lattices are co-Hopfian by rigidity, no off-the-shelf classical
   group qualifies; this is exactly the demand Fournier-Facio's
   universal-group construction was built to meet, and the base
   workstream must either formalize that route (Chiodo absorber —
   countable form already proved in-repo — plus the
   torsion-order-preserving Higman embedding and the Osin envelope,
   where the in-repo Novikov–Boone/S-machine corpus may pay the Higman
   bill) or find a certified alternative (e.g. a congruence subgroup of
   `EL₃(ℤ[x])` is (T)+torsion-free+non-co-Hopfian via the `x ↦ x²`
   substitution, but it is not finitely presented and realizing a
   homomorphic copy inside a f.p. ambient is again Higman-shaped).

## Addendum 2026-08-23: an off-the-shelf group does qualify

Corollary 2 above concludes that "no off-the-shelf classical group qualifies"
for the sharp source demand, on the grounds that torsion-free hyperbolic (T)
groups and higher-rank lattices are all co-Hopfian.  That reasoning is correct
about *lattices*, and the conclusion drawn from it is too strong.  The affine
congruence group `P = Gamma(3) ltimes Z^3` is not a lattice in a semisimple
group: the dilation `(g,v) |-> (g, m v)` is a proper injective endomorphism
that moves only the translation factor and leaves the arithmetic linear part —
the part rigidity makes co-Hopfian — untouched.  `P` is finitely presented,
torsion-free and Kazhdan, and carries the centralizing root and the
Britton-nontrivial marked commutator inside a torsion-free finitely presented
ambient.  So it meets the demand this claim isolates, in full, and the whole
package is kernel-checked.

That is recorded as [[affine-congruence-source-is-kazhdan]], which supplies the
property-(T) certificate that [[concrete-compression-source]] deliberately
leaves out, and it is what makes the Fournier--Facio universal-group machinery
optional on the source side.  Nothing else in this claim changes: the forcing
theorem, corollary 1's linear-centralizer observation, and the correction that
the core's (T) field is not vestigial all stand, and the last of those is
exactly why the added certificate is load-bearing.
