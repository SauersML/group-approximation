---
rg: 2
id: turing-machine-groups-contain-distortion-elements-citation
kind: route
title: "Import Theorem D, the moving-tape definition, its isomorphism lemma and Lemma TMin2V of Callard--Salo"
target: turing-machine-groups-contain-distortion-elements
requires: []
---

Citation import. No proof is re-derived here.

**Source.** A. Callard and V. Salo, *Distortion element in the automorphism group of a full shift*,
arXiv:2208.00685v3; Ergodic Theory Dynam. Systems 44 (2024) 1757–1817. Lane
swarm-0917-w17-w17-nv-follow read the v3 e-print on 2026-09-19 (tex file `distortion-0-main.tex`,
subsections "Distortion in the group of Turing machines" and "Distortion in the Brin-Thompson group
mV"). The quotations below are from that file, with TeX macros expanded
(`\RTM` → RTM, `\llbracket k \rrbracket` → [[k]]).

- **Definition (RTM).** "We recall the definition of the group of Turing machines from [BaKaSa16].
  Let n ≥ 2 and k ≥ 1. Let Y_n be the full shift on n letters, and
  X_k = {x ∈ {0,1,...,k}^Z | 0 ∉ {x_i, x_j} ⟹ i = j}. Then
  RTM(n, k) = {f ∈ Aut(Y_n × X_k) | f|_{Y_n × {0^Z}} = ID|_{Y_n × {0^Z}}}."
- **Theorem D (restated there as `\TuringMachines`).** "Let n ≥ 2, k ≥ 1. Then the group of Turing
  machines RTM(n, k) contains a distortion element; indeed there is a finitely-generated subgroup
  G = ⟨F⟩ and an element f such that |f^n|_F = O(log^4 n)."
- **Definition (moving tape).** "Write RTM_fix(n, k) for the family of homeomorphisms
  f : [[k]] × [[n]]^Z → [[k]] × [[n]]^Z such that for some radius r ≥ 1 and local rule
  f_loc : {0,1}^r × {0,1}^r × [[k]] → {0,1}^* × {0,1}^* × [[k]] we have
  f(xu.vy, a) = (xu'.v'y, b) whenever f_loc(u, v, a) = (u', v', b) and for all u, v,
  f_loc(u, v) = (u', v', n) satisfies |u'| + |v'| = 2r."
- **Lemma (isomorphism).** "A proof of the following easy fact was outlined in [BaKaSa16]; one
  simply translates tape shifts into head movement into the opposite direction. The family of
  homeomorphisms RTM_fix(n, k) forms a group under composition, and there is a canonical group
  isomorphism RTM_fix(n, k) ≅ RTM(n, k)."
- **Lemma TMin2V.** "The group RTM(n, k) embeds in the Brin-Thompson group mV for all m ≥ 2,
  n ≥ 2, k ≥ 1." From its proof: "pick a complete suffix code C ⊂ {0,1}^* of cardinality n, and
  a complete prefix code D ∈ {0,1}^* of cardinality n. One can uniquely parse any x.y ∈ {0,1}^Z as
  ⋯ u_{−2} u_{−1}. v_0 v_1 v_2 ⋯ with u_{−i} ∈ C, v_i ∈ D ... For g ∈ RTM(n, 1), the map g^φ is
  easily seen to be in 2V". After the proof: "Dynamically, the proof gives a topological conjugacy
  between the natural action of RTM(n, 1) and the natural action of the subgroup of 2V that
  respects the encoding."
- On p. 2 the paper defines a distortion element as one of infinite order whose word norm grows
  sublinearly (as recorded in `brin-thompson-mv-contains-a-distortion-element-citation`).

**Cross-check with the original source of the moving-tape model.** S. Barbieri, J. Kari and V. Salo,
*The group of reversible Turing machines*, arXiv:1603.08715v1 (tex file `RTMautomatafinalv2.tex`,
read 2026-09-19):
- Lemma `lem:MovingTapeDynamicalDef`: "Let T : Σ^{Z^d} × Q → Σ^{Z^d} × Q be a function. Then T is
  a moving tape Turing machine if and only if it is continuous, and for a continuous function
  s : Σ^{Z^d} × Q → Z^d and a ∈ N we have T(x, q)_1 ∼_a σ_{s(x, q)}(x) for all
  (x, q) ∈ Σ^{Z^d} × Q", where "x ∼_m y if x_v = y_v for all |v| ≥ m".
- Lemma `group_isomorphism_lemma`: "If n ≥ 2 then: TM_fix(Z^d,n,k) ≅ TM(Z^d,n,k),
  RTM_fix(Z^d,n,k) ≅ RTM(Z^d,n,k)."
- Theorem `theorem_injective_surjective_reversible`: for T ∈ TM_fix(Z^d,n,k), T ∈ RTM_fix(Z^d,n,k)
  is equivalent to "T preserves the uniform measure (μ(T^{-1}(A)) = μ(A) for all Borel sets A)",
  μ being the uniform Bernoulli measure times the uniform measure on states.

The target's item 1 is the case `n = 2` of the moving-tape definition and the isomorphism lemma
(for `n = 2` the alphabet `{0,1}` of the local rule is literal; the phrase "f_loc(u, v) = (u', v', n)"
in the source is a typographical variant of `(u', v', b)`). Item 2 is Theorem D. Item 3 is
Lemma TMin2V.
