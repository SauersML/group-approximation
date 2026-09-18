---
rg: 2
id: lagrangian-brin-thompson-group-is-finitely-presented
kind: claim
title: For some n >= 2 the commutator subgroup of the Lagrangian Brin-Thompson group [[(Sp_2n(Z) on the unimodular Maslov Cantorization) x Cuntz]] is finitely presented; at n = 1 it is 2V
distinct_from:
  lagrangian-thompson-group-is-finitely-presented: that asks finite presentation, simplicity and containment for the odometer host V_Λ^τ on the full rational Cantorization at odd n; here simplicity, finite generation and containment are established (deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group) for every n >= 2, and only finite presentation is asked, for the Cuntz-factor host on the unimodular Cantorization.
  deligne-class-dies-on-some-rational-projective-host: that is the finiteness-plus-class premise of the rational projective route; this is a finiteness question for a different host, on which the class is already dead.
  deligne-lattice-satisfies-boone-higman: that is the embedding question for Deligne's lattice; this is one sufficient host, through deligne-lattice-bh-via-lagrangian-brin-thompson-group.
---

**OPEN.** Let `2V_Λ(n) = [[𝒢_n × G_2]]` be the group of
`deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group`. It is built from
`Sp_{2n}(Z)` acting on `Y_u × F_n`, where `Y_u` is the unimodular Maslov Cantorization
of `unimodular-maslov-cantorization-is-minimal-expansive`, and the Cuntz groupoid `G_2`.

**Claim.** For some `n ≥ 2`, the commutator subgroup `D(2V_Λ(n))` is finitely presented.
The value `n = 2` gives the literal `Sp_4` statement of
`deligne-lattice-satisfies-boone-higman`.

**Consequence.** Deligne's lattice `Γ̃_n` embeds in the finitely presented simple group
`D(2V_Λ(n))`. This is the route `deligne-lattice-bh-via-lagrangian-brin-thompson-group`.

## Known about the group

- **Established** (`deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group`).
  `D(2V_Λ(n))` is simple, finitely generated and has solvable word problem. It contains
  `Γ̃_n`, `Sp_{2n}(Z)` and `V`.
- **Calibration, n = 1.** `2V_Λ(1) ≅ 2V`, which is finitely presented (Brin;
  Hennig–Matucci; textbook, not read at source). The same construction puts `B_3` inside
  it.
- **Possibly simple itself.** `H_*(𝒢_n × G_2) = 0`, by the Künneth formula and
  `H_*(G_2) = 0` (`matui-groupoid-homology-kunneth-and-full-shift-vanishing`).
  - So Matui's AH conjecture for this groupoid would give `[[𝒢]]^{ab} = 0`. Then
    `2V_Λ(n)` is simple and equal to its commutator subgroup.
  - The conjecture is proved in wide generality by X. Li. Its hypotheses are not checked
    here.

## Attempts

1. **Engines that cannot apply (established on main).**
   - Belk–Hyde–Matucci over `V` is ruled out, because the actions are not almost-V
     (`deligne-lift-actions-are-not-almost-v`).
   - Local similarity groups are ruled out, because they are Haagerup (lane remark in
     that node).
   - Matui's shift-of-finite-type results are ruled out for `𝒢_n` alone: those full groups
     are Haagerup (`matui-sft-full-group-haagerup-citation`), while `[[𝒢_n]]` contains
     `Sp_{2n}(Z)`.
   - This last point does not separate `2V_Λ(n)` from `2V`, which is not a-T-menable
     either (`brin-thompson-2v-is-not-a-t-menable`).
2. **Brin–Thompson shape (lane remark).** At `n = 1`, finite presentation comes from
   brick decompositions of the product `(Farey) × (dyadic)`, where each factor subdivides
   canonically.
   - The Cuntz factor keeps its canonical subdivision for every `n`. What is missing for
     `n ≥ 2` is a subdivision rule on the `Y_u` side.
   - The naive Farey rule fails, as recorded in item 2 of
     `lagrangian-thompson-group-is-finitely-presented`. Cells are not rigid: the Levi
     `GL_n(Z)` stabilizes each cell of a frame.
3. **A concrete first test: dissection (open, lane remark).** Is every element of `𝔅_u` a
   finite disjoint union of single cells, modulo `Λ^0`? This is true for `n = 1` (Farey
   arcs). The first case for `n = 2` is the unimodular triangle.
   - **The triangle.** Take the frames `(e,f)`, `(e+f, f)` and `(e, e+f)`.
     - In the `(e,f)` chart their cell indices are `c`, `a + c` and `b + c`.
     - Here `a`, `b` and `c` count the eigenvalues of `S` in `(0,1)`, in `(1,∞)`, and
       below `0`.
     - (Check: `(e, e+f)` has coordinate `(I − S)^{-1} S`, with eigenvalues
       `λ/(1−λ)`.)
     - So the atoms of the triangle are the six types `(a,b,c)` with `a + b + c = 2`.
   - **The pure types** `(2,0,0)`, `(0,2,0)` and `(0,0,2)` are single cells:
     `{0 < S < I}`, `{S > I}` and `{S < 0}`.
   - **The mixed types**, for example `(1,1,0) = {S > 0, S − I indefinite}`, are the test.
     - We expect the stabilizer of such an atom to be finite. The reason is that it
       should permute the three walls, and a unimodular transverse triple has finite
       stabilizer (Levi `A` with `A A^T = I`).
     - Whether the mixed atom is a finite union of cells is not known.
   - **What a yes would give.** A positive answer makes elements of `[[𝒢_n]]` into
     "cell diagrams", like tree-pair diagrams, with arithmetic cell stabilizers. That is
     the input a Stein–Farley complex with vertex stabilizers commensurable to products of
     `GL_n(Z)`-type groups would need.
   - **What a no would give.** A negative answer would mean `𝔅_u` is not "Thompson-like",
     and a proof would have to use the dyadic factor to absorb the non-rigid Maslov
     pieces.
