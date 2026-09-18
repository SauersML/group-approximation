---
rg: 2
id: fpbs-bernoulli-weak-class-cheap-approximability
kind: claim
title: The Bernoulli weak-equivalence class is a limit of free weak-equivalence classes of cost arbitrarily close to the group cost
distinct_from:
  fpbs-bernoulli-weak-class-cost-lsc: that forbids cost dropping in the limit at s̃; this asks for cheap classes accumulating at s̃, and together the two are equivalent to the Bernoulli lower bound.
  fpbs-weak-topology-cost-lsc-envelope-is-group-cost: in the weak topology on actions cheap actions are dense everywhere, which is item 1 there; this is the corresponding statement in the space of classes, where it is not automatic because the class map is not continuous.
---

**OPEN.** Let Γ be an infinite finitely generated group and s a nontrivial Bernoulli shift.
For every ε > 0, s̃ lies in the closure, in F̃R(Γ,X,μ), of {ã : a free, C(a) < C(Γ) + ε}.

Each set {ã : C(a) < r} is open in F̃R (`burton-kechris-cost-usc-and-maximum-action`, item 5),
and contains ã_∞,Γ for r > C(Γ). The claim asks whether these open sets all reach the minimum
class s̃. It is necessary for fixed price, since then s̃ itself has cost C(Γ).

A failure is a *cost-isolated Bernoulli class*. Some F̃R-neighbourhood of s̃ would carry
C ≥ C(Γ) + ε. That is a lower bound on cost which depends only on how close the statistics of
a are to those of s, in finitely many windows.

This is not excluded by `fpbs-weak-topology-cost-lsc-envelope-is-group-cost`. An
F̃R-neighbourhood of s̃ constrains all partitions of a (a Hausdorff condition on the whole
statistics set). Take Γ non-amenable, so that ã_∞,Γ ≠ s̃: a_∞,Γ weakly contains i_Γ × s, and
that is not weakly contained in the strongly ergodic s. Then a small enough F̃R-neighbourhood of
s̃ excludes ã_∞,Γ. Its preimage in FR contains no conjugate of a_∞,Γ, so by density of that
conjugacy class it has empty weak interior. The class map a ↦ ã is not continuous
(Burton–Kechris Theorem 10.4), and the envelope argument does not reach this set.

## Attempts

Approximants weakly contained in s. If a is free and a ≼ s, then s ≼ a by Abért–Weiss, so
ã = s̃ and C(a) = C(s). No gain: every approximant must fail to be weakly contained in s.

Convex mixing of a cheap action. t·a_∞ + (1−t)·s → s̃ as t → 0, by continuity of the convex
combination (Burton Prop 4.1, quoted in Burton–Kechris §10.7). But cost is additive over the
two invariant pieces: C = t·C(Γ) + (1−t)·C(s) → C(s). It dies at additivity. Any approximant
whose cheap part has mass tending to 0 gives nothing, so the cheap structure must occupy most
of the space.

Products with finite transitive actions s × (Γ ↷ Γ/N), N of finite index. The orbit relation
restricted to X × {N} is the orbit relation of s restricted to N. Gaboriau's induction formula
for restrictions to finite-index subgroups gives C(s|N) − 1 = [Γ:N](C(s) − 1), and restriction
to a set of measure 1/[Γ:N] rescales cost − 1 by the same factor. So C(s × Γ/N) = C(s). It dies
at the index formula: profinite-type long-range structure is invisible to cost. The approximants
need cheapness that is not a finite-index or stable rescaling of s.

Shape of what is left. By the first two attempts, approximants have to be ergodic-dominated and
not weakly contained in s. They also need cheap generating graphings, so they are closer to
a_∞,Γ in cost while being closer to s in statistics. No candidate family is known outside
groups with fixed price, where the claim is trivial.

2026-09-17 (swarm-0917 wave 5, inverter). Dilution by co-induction from finite-index subgroups.
For a cheap free a and H ≤ Γ of finite index, D_H(a) = CIND_H^Γ(a|H) on X^{Γ/H} and
E_H(a) = D_H(a) × Γ/H are free with C(E_H(a)) ≤ C(a). This is the natural way to keep a fixed
cheap structure on most of the space while spreading it over independent coordinates. It dies at
the Koopman representation: the normalized coset sum |Γ/H|^{−1/2} Σ_c ξ(y_c) reproduces every
coefficient ⟨κ^a(γ)ξ,ξ⟩ and is bounded in L⁴ uniformly in H, so the coefficient survives into
every ultraproduct. A limit s̃ forces κ^a_0 ≼ κ^s_0 ≅ ∞·λ_Γ, i.e. a tempered, for every sequence
of finite-index subgroups. For non-amenable Γ every free a ≽ i_Γ × s, including a_∞,Γ, is not
tempered. If the finite-index case of Burton–Kechris Problem 3.24 (a ≼ CIND_H^Γ(a|H)) holds, the
only reachable a have ã = s̃. The surviving shape by dilution is (T) inf cost over free tempered
actions = C(Γ), plus (K) E_{H_n}(a)~ → s̃ for such cheap tempered a, which contradicts
Problem 3.24 at finite index whenever ã ≠ s̃. See `fpbs-coinduced-dilution-needs-tempered`.
