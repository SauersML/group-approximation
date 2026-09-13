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
  - research/artifacts/radu-lattice-anchored-linear-gadgets-2026-09-12.md
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
* **Unit ball, letter sets and the finite residual (w7-vh-anchored, 2026-09-12).**
  Artifact: `research/artifacts/radu-lattice-anchored-linear-gadgets-2026-09-12.md`.
  - **Small gadgets.** A factor `I_n + nilpotent`, including every gadget built from `1 + t`, is a
    unit. A pair with `iota(A) = A` and `iota(B) = B`, for `iota(g) = g^(-1)` composed with transpose,
    is never strict. At size one this covers every element supported in the unit ball. Over `F_2`
    the solutions of `beta alpha = 1` there are `alpha = beta` in `{1, h, v, 1 + h + v}`, with
    `hv = vh` in the last case.
  - **Letter sets.** A set of letters generates `Gamma_R` iff it contains `{a,y,z}`, `{b,x,y}`,
    `{b,y,z}`, `{c,x,y}` or `{c,y,z}`. Otherwise it generates a sofic subgroup.
  - **Finite residual.** Modulo `Gamma_0` a pair becomes two-sided, so the defect support has two
    points in one coset of `Gamma_0`. With Remark 3.6 (`delta^(+-4)` shortest in `Gamma_0`), supports
    in `B_r` and `B_s` need `r + s >= 4`. The screen is blind at `r + s = 4`, through
    `((zx)^2)^(-1) (xz)^2 = delta^4`.
  - **Where it stops.** Transposed hinges kill letter identifications only; hinges among longer
    products survive. A witness must put two defect points in one coset of `Gamma_0`, at distance at
    least eight. For strict automata the same invariant, through quotient folding
    (`strict-pairs-transfer-to-table-realizations`), makes every Garden of Eden window distinguish two
    cells that differ by an element of `Gamma_0`, so its diameter is at least eight. No candidate is
    known.
* **Radius four and five, idempotent screen (w7-radu-r4-linear, 2026-09-12).**
  Artifact: `research/artifacts/radu-lattice-radius-four-linear-pairs-2026-09-12.md`.
  - **Source check.** Remark 3.6 of Titz Mite--Witzel states what the finite-residual screen uses:
    `Gamma_0 ∩ B_8 ⊆ {1, delta^(+-4)}`, through the residually finite image of `Phi`. No correction.
  - **Radius four excluded** (`radu-lattice-one-sided-pairs-need-radius-five`). The only residual
    coincidence in `B_4` is `{delta^2, delta^(-2)}`, so `D = I_n - A B = E (delta^2 - delta^(-2))` with
    `E` scalar, and `D = D^2 = E^2 (delta^4 - 2 + delta^(-4))` forces `E = 0`. So `(B_2,B_2)` and
    `(B_1,B_3)` carry no pair over any field, and no pair of any size is built on the `delta^4`
    coincidence there.
  - **Criterion.** If the coincidence points of `B_k` form a product-free set, radius `k` is excluded.
    Under H10 (`Gamma_0 ∩ S_10 ⊆ {y delta^(+-4) y}`) this holds at `k = 5`.
  - **Failed finer invariants.** Finite quotients, linear representations, letter identifications, the
    horizontal-tree image and Jennings filtrations do not separate `delta^2` from `delta^(-2)`.
    `[Gamma_0, Gamma_0]` gives a valid sofic screen, but it helps only if
    `delta^4 ∉ [Gamma_0, Gamma_0]`. The `J`-adic filtration needs `H_1(Gamma_0; K) != 0`. Both are
    unknown.
  - **Where it stops.** H10 is a finite check, the Remark 3.6 computation run to length ten, and it was
    not run under the compute rules. At radius six the coincidence set contains `delta` and
    `delta^2 = delta delta`. So supports give nothing there, and the coefficient equations of `D = D^2`
    are needed.
