---
rg: 2
id: radu-bmw-lattice-group-algebra-not-stably-finite
kind: claim
title: Some matrix algebra over a modular group algebra of Radu's BMW lattice is not directly finite
distinct_from:
  radu-bmw-lattice-nonsurjunctive: that is failure of surjunctivity over any alphabet by any automaton; this is the linear case over F_p^n alphabets, which implies it.
  leavitt-group-algebra-not-stably-finite: that is the linear target on the Kazhdan Leavitt unit group; this is the linear target on a lattice in a product of trees, which has the Haagerup property and no rigid compression defect.
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
---

**OPEN.** Let `Gamma_R` be Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`). For
some prime `p` and some `n >= 1`, exhibit `A, B in M_n(F_p[Gamma_R])` with

```text
B A = I_n,        A B != I_n.
```

By `stable-finiteness-failure-refutes-surjunctivity` this gives an injective non-surjective linear
automaton on `(F_p^n)^(Gamma_R)`, that is `radu-bmw-lattice-nonsurjunctive`
(`radu-bmw-stable-finiteness-failure-gives-nonsurjunctivity`).

## Attempts

* **Support filter (w3-lattice, 2026-09-12).** Suppose every entry of `A` and `B` is supported in a
  subgroup `S`. If `S` is sofic, it is surjunctive (`sofic-groups-are-surjunctive`), so
  `M_n(F_p[S])` is directly finite by the contrapositive of
  `stable-finiteness-failure-refutes-surjunctivity`, and `B A = I_n` forces `A B = I_n`. So the
  supports must generate a nonsofic subgroup. That subgroup lies in no conjugate of `A = <a,b,c>`,
  `V = <x,y,z>`, `<a,b,c,y>`, `<a,b,c,x,z>` or a dihedral `<h, v>`
  (`radu-bmw-coordinate-subgroups-are-sofic`, artifact Section 4).
* **Odd `p`: corner idempotents are dead.** Every involution `t` of `Gamma_R` maps to a nonzero vector of
  `Gamma_R^ab = (Z/2)^3`. So some character `chi` has `chi(t) = -1`, and it kills the averaging
  idempotent `(1+t)/2` at every matrix size. The swap and Klein corner witnesses used on the Leavitt
  hosts have no analogue here. More generally, invariant-output automata are excluded
  (`radu-bmw-lattice-has-no-invariant-output-injective-automata`).
* **`p = 2`: torsion is available.** For each involution `t`, `(1+t)^2 = 0`. So the two-by-two
  cancellation `(s+s')(m_1+m_2) = 0` with `m_2 m_1^(-1)` of order two, which torsion-free lattices forbid
  (Lemma D of `research/artifacts/vh-lattice-table-hosts-2026-09-12.md`), exists on `Gamma_R`, for example
  `(1+a)(1+a) = 0`. Characters into `F_2^x` are trivial, so no character obstruction applies.
* **Where it stops.** No candidate pair is known. Any witness needs entries whose supports mix `y`
  with `x` or `z` in their vertical normal-form parts, and generate a nonsofic subgroup.
