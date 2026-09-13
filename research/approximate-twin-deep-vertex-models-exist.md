---
rg: 2
id: approximate-twin-deep-vertex-models-exist
kind: claim
title: Approximate twin deep models of the two modular vertex groups exist at every depth and every tolerance
distinct_from:
  twin-deep-vertex-models-give-homogeneous-microstates: that proves what such models would give and that exact ones do not exist; this is the existence statement for the approximate models themselves.
  dyadic-homogeneous-quotient-admits-topological-microstates: that is the microstate statement for compact quotients of PSL2(Q2); this is a purely modular finite construction with no lattice, marks or separation, which implies it.
  dyadic-amplified-edge-random-lifts-exist: that asks for exact vertex actions glued over the whole Iwahori group with tree-like incidence; this glues only approximately over the deep subgroup Delta_R and asks for 2-adically deep stabilizers.
---

**OPEN.** Notation of `twin-deep-vertex-models-give-homogeneous-microstates`: `C_0 = PSL_2(Z)`,
`C_1 = gC_0g^(-1)` with `g = diag(1,2)`, `N_0 = Γ(2^R)`, `N_1 = gN_0g^(-1)`,
`Δ_R = Γ(2^(R-1)) ∩ Γ_1(2^(R-1))`.

For every `R >= 2` and `ε > 0` there is a finite set `W` with exact actions `ρ_0` of `C_0` and
`ρ_1` of `C_1` such that all but `ε|W|` points have `ρ_0`-stabilizer inside `N_0` and
`ρ_1`-stabilizer inside `N_1`, and `ρ_0(s)`, `ρ_1(s)` differ on at most `ε|W|` points for every
`s` in a fixed finite generating set of `Δ_R`. This is `(TD_(R,ε))`.

**Stakes.** Route `dyadic-microstates-from-approximate-twin-deep-models` gives
`dyadic-homogeneous-quotient-admits-topological-microstates` for every torsion-free cocompact
`Λ`, hence the sofic dyadic vertex action and a sofic `G_2`. By
`dyadic-vertex-soficity-equals-frame-dynamics-soficity` the vertex question does not get easier
than this.

**Format any successful family must have** (from established nodes):
* never exact (`twin-deep-vertex-models-give-homogeneous-microstates`, part (b));
* asymptotically free on `Δ_R` as `ε → 0` with `R` fixed: the stabilizer laws are invariant under
  conjugation by `C_0`, respectively `C_1`, and any weak limit lives on the trivial normal core
  (same node);
* not congruence on both sides (`expanding-matchings-need-a-shared-stabilizer`).

## Attempts

- **Exact models.** Dead, by part (b) of `twin-deep-vertex-models-give-homogeneous-microstates`.
- **Congruence frames on both sides.** Dead: every bijection between principal-congruence vertex
  models has edge defect at least `h_S` (`expanding-matchings-need-a-shared-stabilizer`).
- **Induced covers through a fixed proper quotient of `N_0`.** Put `W = Ind_(N_0)^(C_0) Y` where
  the `N_0`-set `Y` factors through `N_0/M` for a fixed nontrivial `M ◁ N_0` of infinite index
  (cyclic or abelian covers with fixed voltages, nilpotent covers of bounded class, solvable
  covers of bounded derived length). Every point stabilizer contains a conjugate of `M` under
  `C_0`, so the stabilizer law never converges to the trivial subgroup. Dead by asymptotic
  freeness.
- **Expander ansätze (any coincidence pattern).** Dead: `twin-models-have-macroscopic-noncoincident-stabilizers`.
  At least a `λ_A^2/4` fraction of points have different vertex stabilizers. By Lemma G, a family
  whose diagonal `Δ_R`-orbits have uniform Cheeger constant `h` needs `ε >= λ_A^2 h/(4(2h + |S_Δ|))`.
- **Independent uniform induced models.** Take `Y_0`, `Y_1` independent uniform `N_0`-, `N_1`-sets
  with fibre size `y`, and induce. A union bound over bijections of `W` does NOT kill this ansatz.
  `N_0` is free of rank `1 + [C_0:N_0]/6`, so one side carries entropy about
  `(1/6)|W| log y`, below `log |W|! ≈ |W| log y`. It stays undecided; counting has to respect
  the fibration.
- **Amenable Borel chunks (in progress, this lane).** `P = A ∩ (upper triangular)` is amenable and
  acts transitively on type-0 vertices with stabilizer `P ∩ C_0 ≅ Z`, so the vertex action
  restricted to `P` is hyperfinite. The question is whether Følner chunks of `P` can be closed up
  to exact deep `C_0`- and `C_1`-actions while keeping the `Δ_R`-gluing defect small.
