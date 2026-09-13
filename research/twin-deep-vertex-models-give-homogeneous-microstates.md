---
rg: 2
id: twin-deep-vertex-models-give-homogeneous-microstates
kind: claim
title: Twin 2-adically deep models of the two modular vertex groups, glued only over a deep edge subgroup, give microstates for every compact dyadic quotient
distinct_from:
  dyadic-amplified-edge-random-lifts-exist: that asks for exact vertex actions glued over the whole index-three Iwahori group with tree-like orbit incidence; this glues only over the deep subgroup Delta_R, needs no incidence or separation condition, and asks instead for 2-adically deep stabilizers.
  dyadic-homogeneous-quotient-admits-topological-microstates: that is the microstate statement for one compact quotient; this is a sufficient criterion that mentions no lattice and no marks, so it serves every lattice at once.
  expanding-matchings-need-a-shared-stabilizer: that shows congruence twin models fail with a Selberg gap; this shows what any successful non-congruence twin model yields.
---

**ESTABLISHED (unreviewed).** Notation as in `expanding-matchings-need-a-shared-stabilizer`:
`C_0 = PSL_2(Z)`, `C_1 = gC_0g^(-1)` with `g = diag(1,2)`, `B = C_0 ∩ C_1 = PΓ_0(2)`, principal
congruence subgroups `Γ(L) ◁ C_0` and `Γ_1(L) = gΓ(L)g^(-1) ◁ C_1`. For `R >= 2` put

```text
N_0 = Γ(2^R),   N_1 = Γ_1(2^R),   Δ_R = Γ(2^(R-1)) ∩ Γ_1(2^(R-1)),
N_0, N_1 ⊆ Δ_R ◁ B,   [Δ_R : N_0] = [Δ_R : N_1].                                  (TD0)
```

A **twin deep model** `(TD_(R,ε))` is a finite set `W` with *exact* actions `ρ_0` of `C_0` and `ρ_1`
of `C_1` such that:

1. (*deep*) every `ρ_0`-stabilizer lies in `N_0` and every `ρ_1`-stabilizer lies in `N_1`, except
   on at most `ε|W|` points;
2. (*deep gluing*) `ρ_0(s)` and `ρ_1(s)` differ on at most `ε|W|` points, for `s` in a fixed finite
   generating set of `Δ_R`.

**Theorem.**
* **(a) Sufficiency.** If `(TD_(R,ε))` exists for every `R >= 2` and `ε > 0`, then for every
  torsion-free cocompact lattice `Λ <= PSL_2(Q_2)` the action of `PSL_2(Z[1/2])` on
  `PSL_2(Q_2)/Λ` admits topological microstates. By
  `homogeneous-quotient-soficity-gives-vertex-soficity`, the dyadic vertex action is then sofic.
* **(b) No exact models.** `(TD_(R,0))` never exists. For a uniform random `w ∈ W`, the stabilizer
  `S = Stab_(ρ_0)(w) = Stab_(ρ_1)(w) ⊆ N_0 ∩ N_1` has a law invariant under conjugation by
  `C_0` and by `C_1`, hence by `PSL_2(Z[1/2])`. So `S` lies in the normal core of `N_0 ∩ N_1`,
  which is trivial by the normal subgroup theorem. But `S` has finite index in `C_0`.

**How (a) works (tensor absorption).** Tensor `W` with the depth-`R` frame spaces of the two vertex
types. Over a level-`(R−1)` common cell, both sides are induced from `Δ_R`, with fibres
`(Δ_R/N_0) × W` and `(Δ_R/N_1) × W`. Deep stabilizers make each fibre a multiple
`[Δ_R : N_i]·W`: the frame coordinate is **absorbed**. So the two sides differ only by the gluing
defect of `W` over `Δ_R`. The Iwahori mismatch between the two frame systems, which costs `h_S` by
Lemma G, is therefore paid by `W` alone, on a subgroup where both vertex groups already act.

**What this says about the problem.** Soficity of the dyadic vertex action follows from a *purely
modular* finite construction. It needs no lattice, no marks and no separation. Take the modular
group and its `2`-conjugate, act on one finite set with `2`-adically deep stabilizers, and make the
two actions of the deep common subgroup `Δ_R` nearly agree. By (b) the agreement cannot be exact.
By Lemma G it cannot come from congruence actions. By the stabilizer-law argument of (b), in any
sequence with `ε → 0` the stabilizer laws of `Δ_R` converge weakly to the trivial subgroup, so the
models are asymptotically free. The live constructive question is whether two asymptotically free,
non-congruence deep extensions can be Hamming-correlated over `Δ_R`.

Proof in `twin-deep-vertex-models-give-homogeneous-microstates-proof`.
