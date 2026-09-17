---
rg: 2
id: burton-kechris-cost-usc-and-maximum-action
kind: claim
title: For a finitely generated group, cost is upper semicontinuous on free actions and on free weak-equivalence classes, and a maximum action with dense conjugacy class exists
distinct_from:
  cost-is-constant-on-weak-equivalence-classes: that imports only the monotonicity corollary; this imports the semicontinuity theorem it is derived from, the maximum action, the conjugacy-closure form of weak containment, and the upper semicontinuity on the compact space of weak-equivalence classes.
---

**ESTABLISHED (import).** Let Γ be a countable group and (X,μ) standard non-atomic.

1. (Kechris Prop 10.1) For a,b in A(Γ,X,μ), a ≼ b iff a lies in the weak-topology
   closure of the conjugacy class of b.
2. (Glasner–Thouvenot–Weiss, Hjorth; Kechris Thm 10.7) There is a maximum a_∞,Γ for ≼,
   characterised by having a dense conjugacy class in A(Γ,X,μ).
3. (Glasner–King) FR(Γ,X,μ) is a dense G_δ in A(Γ,X,μ), and it is upward closed under ≼.
4. (Kechris Thm 10.13) If Γ is finitely generated, a ∈ FR ↦ C_μ(a) is upper semicontinuous
   for the weak topology.
5. (Burton–Kechris Thm 10.13) If Γ is finitely generated, ã ∈ F̃R ↦ C_μ(a) is upper
   semicontinuous on the compact metrizable space F̃R(Γ,X,μ) of free weak-equivalence classes.

It is **open** (Burton–Kechris Problem 10.14) whether the map in item 5 is continuous.

**Source.** P. Burton, A. S. Kechris, *Weak containment of measure preserving group actions*,
arXiv:1611.07921 (version of April 17, 2019), read 2026-09-17 from the arXiv PDF.
- Theorem 2.3: "([K, Proposition 10.1]). Let a ∈ A(Γ, X, µ), b ∈ A(Γ, Y, ν) with (X, µ),
  (Y, ν) non-atomic. Then a ≼ b ⇐⇒ a ∈ {c ∈ A(Γ, X, µ) : c ≅ b}‾, where ≅ denotes isomorphism
  (conjugacy) between actions."
- Theorem 3.1: "(Glasner-Thouvenot-Weiss [GTW], Hjorth; see [K, Theorem 10.7]). There is a
  maximum element in the pre-order ≼ of A(Γ, X, µ), denoted by a∞,Γ. Of course a∞,Γ is unique up
  to weak equivalence and is characterized by the property that its conjugacy class is dense in
  A(Γ, X, µ)."
- §3.2: "The set FR(Γ, X, µ) of free actions is a dense Gδ subset of A(Γ, X, µ) (Glasner-King
  [GK]; see also [K, Theorem 10.8])." Theorem 3.4: "The set FR(Γ, X, µ) of free actions is
  upwards closed in ≼".
- §7.1: "It has been shown in [K, Theorem 10.13] that when the group Γ is finitely generated,
  the function a ∈ FR(Γ, X, µ) ↦ Cµ(a) ∈ R is upper semicontinuous". Theorem 7.1 then gives
  "Cµ(sΓ) ≥ Cµ(a) ≥ Cµ(a∞,Γ) = C(Γ), for finitely generated Γ and any a ∈ FR(Γ, X, µ)."
- Theorem 10.13: "Let Γ be finitely generated. Then the map ã ∈ F̃R(Γ, X, µ) ↦ Cµ(a) is upper
  semicontinuous." Problem 10.14: "Let Γ be finitely generated. Is the map ã ∈ F̃R(Γ, X, µ) ↦
  Cµ(a) continuous?"

The PDF text was machine-extracted, so tildes and closure bars are restored by hand above.
[K] is Kechris, *Global aspects of ergodic group actions*; it was not read here, so its item
numbers are as Burton–Kechris print them.
