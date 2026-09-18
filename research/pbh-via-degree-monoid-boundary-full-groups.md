---
rg: 2
id: pbh-via-degree-monoid-boundary-full-groups
kind: claim
title: Finiteness transfer - for a countable cancellative monoid with a unique-factorization degree map to N^k, lcms, finite residues and an F_infinity unit group, whose boundary groupoid is Hausdorff and effective, the full group of that groupoid times the Cuntz groupoid is F_infinity, simple and highly transitive, so every group acting by its boundary germs satisfies the permutational Boone-Higman conjecture
requires:
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - rcwa-groups-over-pids-satisfy-boone-higman
distinct_from:
  rcwa-groups-over-pids-satisfy-boone-higman: that proves the host properties for the ax+b monoids of specific rings; this isolates the five monoid axioms those proofs used, as a general host theorem with the unit group as the only group-theoretic input.
  permutational-boone-higman-via-v-times-aperiodic-sft-full-groups: that builds hosts from full groups of SFTs over V; this builds them from boundary groupoids of monoids with nontrivial F_infinity unit groups, where the unit group supplies the infinite local symmetry.
  fp-self-similar-subgroups-satisfy-permutational-boone-higman: that uses rank-one Röver-Nekrashevych envelopes of finitely presented self-similar groups; this is a higher-rank monoid form, where the units need not act self-similarly on a tree.
---

**ESTABLISHED** (lane proof, not reviewed). The proof is the argument of
`rcwa-over-pids-bh-via-ax-plus-b-monoid-hosts-proof`, Steps 2–5, together with Lemma 2 of
`rcwa-groups-satisfy-permutational-boone-higman`. Only the monoid axioms below are used.
The inputs are:
- Li arXiv:2110.04505v2, Theorem `thm:deg` and the lemma after it;
- Li arXiv:2209.08087, Corollary `introcor:Vanish`;
- Matui's Künneth theorem, as quoted in FKPS arXiv:1808.07807;
- Matui arXiv:1210.5800v3, Theorem `simple2`;
- BFFHZ Theorem C.

No priority is claimed for the general statement. It is a packaging of these theorems.

## Statement

Let `C` be a countable monoid that is a submonoid of a group. Suppose:

- **(M1) Degree map with unique factorization.** There is a degree map `d : C → N^k` with
  `d^{-1}(0) = C^*`, satisfying Li's (UFP*).
- **(M2) lcms.** `aC ∩ bC` is empty or equal to `cC` for some `c`.
- **(M3) Finite residues.** Each degree has finitely many elements up to right units, and
  each basis degree `e_j` has at least two.
- **(M4) Units.** `C^*` is of type `F_∞`.
- **(M5) The groupoid.** Li's boundary groupoid `G_C = I_l(C) ⋉ ∂Ω` is Hausdorff and
  effective.

Let `H_C = F(G_C × G_{O_2})` be the topological full group on `∂Ω × {0,1}^N`. Then:
1. `H_C` is of type `F_∞`, simple, and highly transitive on every orbit.
2. Every subgroup of `H_C` lies in `B_A`, so it satisfies the permutational Boone–Higman
   conjecture.
   - This covers every group acting faithfully on `∂Ω` by homeomorphisms that are
     piecewise, on finitely many cylinders, restrictions of the partial maps
     `λ_a λ_b^{-1}` (`a, b ∈ C`). Such a group embeds in `H_C` by `g ↦ g × id`.

## Proof

- **`F_∞`.** `C × F_2^+` satisfies (M1)–(M4) with degree monoid `N^{k+1}`, and it is right
  cancellative, which gives Li's (F). Li's Theorem `thm:deg` then gives `F_∞`, with (t < d)
  from Li's lemma after it (Step 2 of the ax+b route).
- **The product.** Li's product identification gives `G_C × G_{O_2}`.
- **The unit space.** `∂Ω` is compact, metrizable and totally disconnected.
  - It has no isolated points: each cylinder `∂Ω(a)` is the disjoint union of the at least
    two cylinders `∂Ω(ab)`, `d(b) = e_j`, by (M1)–(M3).
  - So the unit space of the product is a Cantor set.
- **Minimal.** There is one object, so `λ_b λ_a^{-1}` maps `∂Ω(a)` onto `∂Ω(b)`. Hence every
  orbit meets every cylinder, and cylinders form a basis by (M2)–(M3).
- **Essentially principal.** The product of effective Hausdorff ample groupoids is effective
  and Hausdorff, so it is essentially principal (Baire).
- **Purely infinite, comparison, high transitivity.** Binary splitting in the `O_2` factor
  gives pure infiniteness and comparison, as in Step 4 of the ax+b route. It also gives the
  equivalence of any two nonempty clopen sets (Lemma 1 of the PBH node), hence high
  transitivity on each orbit (Lemma 2 there).
- **Simple.** `H_*(G_{O_2}) = 0` (FKPS), so `H_*(G_C × G_{O_2}) = 0` by Künneth. Li's
  `introcor:Vanish` then makes `H_C` perfect, and Matui's `simple2` makes it simple.
- **`B_A`.** BFFHZ Theorem C (iii) ⟹ (i) puts every subgroup of `H_C` in `B_A`. ∎

## Instances on main

| Monoid `C` | Unit group `C^*` | Groups hosted |
|---|---|---|
| `R ⋊ S_P`, `R` a number ring of class number one | `R ⋊ R^*` (polycyclic-by-finite) | `RCWA_P(R)` |
| digit submonoid of `F_q[t] ⋊ S_P` | `F_q^*` | `RCWA_P(F_q[t])` |
| `Z[1/N] ⋊ S_π` | `Z[1/N] ⋊ ⟨−1, q \| N⟩` (ascending HNN) | f.g. `RCWA(Z_(π))` |
| `Λ_P ⋈ Z` (odometer) | `Z` | `RCWA_P(Z)` via sign doubling |
| `Λ_P` (class-transposition k-graph) | trivial | `CT_P(Z)` |
| the one-vertex `k`-graph `(F_2^+)^k` | trivial | Brin's `kV` |

## Lesson for general BH

A finitely presented simple host costs exactly one `F_∞` group, the unit group, plus
combinatorics.
- **What the unit group does.** Li's theorem transfers finiteness from `C^*` to the whole
  full group.
- **What the rest supplies.**
  - The Cuntz factor supplies perfectness, simplicity and high transitivity for free.
  - The monoid axioms (M1)–(M3) only ask that "residue classes" behave like boxes:
    unique factorization of degrees, closure under intersection, and finitely many
    classes per degree.
- **The reduction.** BH or PBH for a group `G` therefore reduces to a representation
  problem: find a monoid satisfying (M1)–(M5) whose boundary germs contain `G`.
  - This is sharper than asking for a finitely presented simple overgroup, because the
    group-theoretic finiteness is concentrated in `C^*`.
  - Ax+b monoids of PIDs solve the representation problem for every RCWA group at once.
- **Where it stops: matrix monoids.**
  - For `n ≥ 2`, the monoid `C_n = Z^n ⋊ M_n^{(p)}(Z)` of affine maps `x ↦ Ax + b`, with `A`
    integral of `p`-power determinant, admits **no** degree map to any `N^k` satisfying
    (UFP*).
    - The units `C_n^* = Z^n ⋊ GL_n(Z)` act transitively on the index-`p` lattices by
      `A ↦ uAv`. So every degree map gives all index-`p` elements the same degree `e`.
    - `pI = A_1 B_1 = A_2 B_2` with `A_1 Z^n ≠ A_2 Z^n` of index `p`, since `pZ^n` lies in
      `(p^n − 1)/(p − 1) ≥ 3` such lattices.
    - (UFP*) would force `A_2 = A_1 u` with `u` a unit, hence `A_2 Z^n = A_1 Z^n`, a
      contradiction.
  - This Hecke branching is the precise obstruction to lattice-coset hosts. That matters
    for Kohl's `RCWA(Z^n)`, and for `GL_n(Q)`-type piecewise actions on `Ẑ^n`.
  - The central Garside element `pI` suggests replacing (M1) by Li's general Garside
    criterion (Li, Theorem `intro:Fn`), whose extra conditions (St), (LCM) and (t < d) are
    not checked here.

## Limits of the route (proved)

- **L1. The units act through a residually finite quotient.**
  - `C^*` acts on the finite set `Res_e = {aC : d(a) = e}` (M3) by `u·aC = uaC`. This preserves
    degree, so it gives a homomorphism `C^* → Sym(Res_e)`.
  - A unit in every kernel fixes every cylinder `∂Ω(a)` setwise. For each `e` the degree-`e`
    cylinders partition `∂Ω`, and cylinders form a basis, so such a unit fixes every point.
  - `G_C` is effective, so `H_C` acts faithfully. Hence that unit is trivial in `H_C`.
  - So the image of `C^*` in `H_C` embeds in `∏_e Sym(Res_e)`: it is residually finite. Its
    `F_∞` property is used, but its non-residually-finite part is invisible.
  - Non-residually-finite subgroups of `H_C`, such as `BS(1,2)` in `2V_τ` through the baker
    map, must come from the combinatorics of the boundary, not from the units.
- **L2. Hosts are `F_∞`.** Every group the route reaches embeds in an `F_∞` group. A proof of
  BH through this route therefore also proves, for the groups it reaches, a positive answer
  to BBMZ survey Question 5.6 ("Does every finitely presented group embed as a subgroup of a
  type F∞ group?").

## Question

Does every finitely generated group with solvable word problem act faithfully by the
boundary germs of some monoid satisfying (M1)–(M5)? A positive answer implies the
permutational Boone–Higman conjecture, and hence BH. It is not known whether BFFHZ's
finitely presented twisted Brin–Thompson groups themselves arise this way. They are full
groups over infinitely many colours twisted by an oligomorphic group, not over `N^k`.
