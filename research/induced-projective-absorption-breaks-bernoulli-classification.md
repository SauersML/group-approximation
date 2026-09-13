---
rg: 2
id: induced-projective-absorption-breaks-bernoulli-classification
kind: claim
title: If a free F_p[G]-module absorbs a nonzero module induced from finite subgroups, base entropy fails to classify Bernoulli shifts over G
distinct_from:
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that gives, from any one-sided inverse, a Bernoulli shift absorbing a nontrivial algebraic factor, with Bernoullicity of that factor left open; this handles every absorbed summand induced from finite subgroups and outputs an actual isomorphism of Bernoulli shifts of different base entropy.
  bernoulli-entropy-counterexample-constraints: that proves necessary conditions on a counterexample group; this is a sufficient algebraic condition for one.
  leavitt-unit-group-algebra-not-directly-finite: that is Kaplansky direct finiteness failure for the Leavitt units in any shape; this requires the defect module to be induced from finite subgroups, and then refutes the Bernoulli classification as well.
artifacts:
  - research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md
---

**ESTABLISHED (unreviewed)** by [[induced-projective-absorption-breaks-classification-proof]].

**Theorem E.** Let `G` be a countable group, `p` a prime, `n >= 1`, `F_1, ..., F_r <= G` finite subgroups,
and `Q_i` finite-dimensional `F_p[F_i]`-modules, not all zero, with

    F_p[G]^n ≅ F_p[G]^n ⊕ ⊕_i F_p[G] ⊗_(F_p[F_i]) Q_i       (left modules).

Put `rho = sum_i dim(Q_i)/|F_i|`. Then the Bernoulli shifts over `G` with base entropies `n log p` and
`n log p + rho log p` are isomorphic. So `rho log p` is a nonzero element of the collapse subgroup of
`bernoulli-isomorphism-collapse-set-is-a-subgroup`, and the same holds over every group containing `G`.

**Necessary conditions** on the hypothesis (Section 3 of the artifact):
- it is a failure of stable finiteness, so `G` is nonsofic, not surjunctive, and has `h^Rok_sup(G) <= n log p`;
- no `Q_i` has a trivial quotient, so permutation modules `F_p[G/F]` never occur. More generally, for every
  homomorphism to a sofic group the coinvariants of `ker ∩ F_i` on `Q_i` vanish;
- if `p` divides no `|F_i|`, then `rho ≡ 0 mod p` through the Hattori–Stallings trace. The real entropy gain
  is exactly what the mod-`p` Kaplansky trace cannot see.

**Reading.** The negative direction of `bernoulli-shift-entropy-classifies-for-every-group` reduces to a
purely algebraic identity in a modular group algebra. That identity is a Kaplansky counterexample of a
special shape. Over the binary Leavitt unit group the smallest candidate is
`leavitt-unit-algebra-absorbs-an-induced-projective`: `F_2[U]^n ≅ F_2[U]^n ⊕ F_2[U](c + c²)` for a unit `c`
of order 3. It holds in the Leavitt quotient, and it would give `X_(n log 2) ≅ X_(n log 2 + (2/3) log 2)`.
