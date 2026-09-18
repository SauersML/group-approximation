---
rg: 2
id: definable-parameter-hosts-cap-simple-subgroups-at-pspace
kind: claim
title: A finitely presented group acting faithfully by bijections uniformly definable, from arbitrary parameters, in the real field or in an ω-automatic structure on Cantor space specializes to tame parameters on every finite set, so its finitely generated simple subgroups have word problem in PSPACE
distinct_from:
  fp-piecewise-projective-groups-specialize-to-algebraic-data: that is the one-dimensional piecewise-projective case, with a polynomial-time bound over number fields, proved by density of algebraic points and openness of nontriviality; this is the same collapse for every semialgebraic action in any dimension and for ω-automatic actions on Cantor space with arbitrary addresses, proved by definable choice alone (Tarski transfer and Büchi's lasso theorem), with the uniform bound PSPACE.
  automaton-tail-full-groups-have-conp-relative-word-problem: that bounds parameter-free prefix-and-automaton groups themselves; this allows arbitrary real or symbolic parameters and bounds the finitely generated simple subgroups of the finitely presented members.
  complexity-bounded-host-classes-are-not-universal: that shows a host class with one recursive bound is not universal; this puts every definable-parameter host family into one such class, PSPACE.
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

**ESTABLISHED** through `definable-parameter-hosts-specialization-proof` (lane proof, elementary
given Tarski transfer, Büchi's theorem and Canny's PSPACE bound; not independently reviewed). No
priority is claimed. Specialization of finitely presented groups is classical (Malcev), and the
method is folklore in spirit. Here it is packaged as a host obstruction for Boone--Higman.

## Setting

A *definable action* of a finitely generated group `G = ⟨g_1..g_m⟩` is a faithful action by
bijections of a set `X`, of one of the following two types.

- **(R) Semialgebraic.** `X ⊆ R^n` and the graphs `Γ(g_i) ⊆ R^{2n}` are semialgebraic, with
  arbitrary real constants. Collecting the constants into `θ_0 ∈ R^k`, there are formulas
  `χ(θ,x)`, `γ_i(θ,x,y)` with rational coefficients that define `X` and `Γ(g_i)` at `θ = θ_0`.
- **(A) Automatic.** `X = Σ^N` for a finite alphabet `Σ`. The graphs are the `ξ_0`-sections of
  synchronous ω-regular relations `γ_i ⊆ (Γ × Σ × Σ)^N`, with an arbitrary parameter
  `ξ_0 ∈ Γ^N`.

A *tame member* of the family is the same formulas at a tame parameter. For (R) that is
`θ ∈ R_alg^k`. For (A) it is an ultimately periodic `ξ`.

Examples of (R):
- PL and piecewise projective groups with arbitrary real data, including discontinuous `V`-type
  maps and any dimension: `F, T, V`, Stein, Bieri--Strebel, irrational- and transcendental-slope
  groups, and finitely generated subgroups of Lodha--Moore and Monod groups.
- Interval exchange and polygon-exchange groups, PL homeomorphism groups of polyhedra, and all
  groups of semialgebraic bijections of `R^n`.

Examples of (A):
- `V`, `nV`, and Röver--Nekrashevych groups of automaton groups (prefix replacement has bounded
  shift, so its graph is synchronous ω-regular).
- Any extension of these by generators that act along an arbitrary address `ξ_0` in an automatic
  way, such as ray translations, or germs at singular points of arbitrary complexity.

## Statement

Let `G` be finitely presented with a definable action of type (R) or (A).

1. **Tame specialization.** For every finite `F ⊆ G ∖ {1}` there is a tame parameter at which the
   same formulas define an action of `G` in which no element of `F` acts trivially.
2. **Simple subgroups are tame.** Every finitely generated simple subgroup `S ≤ G` embeds in a tame
   member of the family, and `WP(S) ∈ PSPACE`.
3. **Word problem.** `G` has solvable word problem.
4. **Host consequence.** Let `Q` be a finitely generated group that embeds in a finitely presented
   simple group with a definable action, or in a finitely generated simple subgroup of a finitely
   presented group with a definable action. Then `WP(Q) ∈ PSPACE`. So no definable host family, of
   either type and with any parameters, embeds an input whose word problem lies outside PSPACE.
   For `fp-simple-groups-with-arbitrarily-complex-word-problem`, all such hosts share the single
   bound PSPACE.

## Lesson for general BH

A Boone--Higman host cannot store the input's algorithm in constants: not in real parameters, not
in a singular address, and not in any tame description of its generators. Finite presentation
consults the parameters only through a first-order condition, and first-order conditions over these
structures always have tame solutions. So the host for an input of complexity `C` needs generators
whose graphs are not definable in any structure with tame definable choice whose existential theory
is below `C`. In other words, the input's algorithm must be written into the combinatorial rule
itself, as in Higman's embedding, for instance through infinite-state self-similarity or germs that
are not automatic. This single statement classifies the geometric host families (PL, projective,
semialgebraic in any dimension, `V`/`nV`/Röver--Nekrashevych with any addresses) as capped for the
Birget root.

**Where the live routes escape.** The routes that are still open on the root lie exactly outside
this class:
- twisted Brin--Thompson hosts `SV_Γ` (Attempt 1), which permute infinitely many Cantor coordinates
  and so are not synchronous-automatic;
- infinite-state self-similar hosts (Attempt 2), whose graphs are not ω-regular;
- finite-index HNN inputs (Attempt 5), which are not given by an action at all.

The routes that died (Attempts 3, 4 orbit-preserving, 6, 8) are all definable. So the theorem is a
test to run on any proposed host: *is its generating rule tamely definable?* If it is, the host is
capped at PSPACE.

## Not claimed

- Sharpness. Automaton groups with PSPACE-complete word problem exist (D'Angeli--Rodaro--Wächter,
  not read here), but no finitely presented simple definable host is known to reach PSPACE. The
  known tame hosts reach coNP (Birget, Zaremsky) and `coNP^⊕P` (Attempt 7 of the root; linear, not
  of type (A)).
- Other structures, such as `R_exp` or the Presburger structure on `Z`. For `R_exp` the argument
  needs its decidability, which is known only conditionally on Schanuel's conjecture.
