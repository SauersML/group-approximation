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
* **Splittings, edge-group filter and finite-subgroup defects (w4-radu-f2, 2026-09-12).**
  Artifact: `research/artifacts/radu-lattice-binary-algebra-splittings-2026-09-12.md`.
  - **Splittings.** `Gamma_R = P_y *_(A_ev) E_x = V *_(V_a) E_a`
    (`radu-bmw-lattice-splits-as-amalgams-of-virtually-free-groups`). So `F_p[Gamma_R]` is an
    amalgamated coproduct of group algebras of virtually free groups over a virtually free base. In
    characteristic two the base `F_2[A_ev]` contains `F_2[t]/(t^2)` and is not semisimple.
  - **Support filter.** The support group of a witness splits over a nonamenable edge group on both
    trees, and it meets a conjugate of `A` and a conjugate of `V` in nonabelian free groups
    (`nonsofic-subgroups-of-radu-lattice-have-nonamenable-edge-groups`). This contains the
    letter-subgroup filter above as the case where the support group meets `V` amenably.
  - **No finite-subgroup starting data.** For every `p`, an idempotent matrix over the algebra of a
    finite subgroup that is full at its own size is the identity. The defect `I - AB` is never
    conjugate into such an algebra (`radu-lattice-defect-idempotents-avoid-finite-subgroups`). Finite
    subgroups have order at most four and inject into `(Z/2)^3`. So at `p = 2` the torsion supplies
    square-zero elements `1 + t` but no idempotents, and the two-piece corner telescoping of the Leavitt
    hosts has nothing to start from.
  - **Where it stops.**
    - *Witness.* A witness is a nonzero projective `P` with `P ⊕ F_2[Gamma_R]^n ≅ F_2[Gamma_R]^n`. Its
      idempotent has infinite support that is not a basis change of a finite-subgroup idempotent, over
      supports that split nonamenably in both directions. No candidate is known.
    - *Positive direction.* This needs a Sylvester rank function on `F_2[Gamma_R]`. Its restrictions to
      `F_2[P_y]` and `F_2[E_x]` must agree on `F_2[A_ev]`, and rank functions on algebras of nonamenable
      virtually free groups over `F_2` are not unique. Matching them over the base is exactly where the
      two embeddings of `A_ev` disagree. No construction is known, and neither is a gluing theorem over
      a nonamenable base.
