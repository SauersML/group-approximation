---
rg: 2
id: stabilizer-engines-are-fp-only-over-isolated-groups
kind: claim
title: If the stabilizer engine F_B of an infinite finitely generated group B (or its derived group) is finitely presented, then B is an isolated point of the space of marked groups; so Reid's group is not finitely presented, and no non-finitely-presented simple input has a finitely presented engine
requires:
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
  - fp-stabilizer-engines-need-decidable-vertex-groups
invalidates:
  - simple-inputs-have-finitely-presented-stabilizer-engines
distinct_from:
  fp-stabilizer-engines-need-decidable-vertex-groups: that shows an fp engine forces a decidable vertex group; this forces the much stronger condition that the vertex group is isolated (finitely presented and finitely discriminable).
  hard-cusps-are-canonical-and-flux-free: that describes the local model at the emitter; this shows the emitter model can only give finite presentation for isolated vertex groups.
  stabilizer-engines-embed-in-every-branch-compactification: that builds the blow-up family F_S^K and shows the emitter K = S⁺ is never of finite type; this shows the emitter engine itself is infinitely presented unless S is isolated. It does not apply to finite-type blow-ups.
---
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-18; elementary; **not reviewed**; referee
requested). The characterization of isolated groups is Cornulier–Guyot–Pitsch (J. Algebra
2007; not re-read at source): a finitely generated group is isolated iff it is finitely
presented and finitely discriminable. No priority is claimed.

**Notation.** `B` is an infinite group with a finite generating set `Σ_B`, `k ≥ 2`, and
`D = Z/k * B`. `T` is its Bass–Serre tree, `X_B` is `T`'s ends together with its `B`-vertices,
and `F_B = [[D ⋉ X_B]]` is the stabilizer engine. For a finite group `B'` of order `≥ 3`,
`X_{B'}` is the end space of the tree of `Z/k * B'` (a Cantor space), and `F_{B'}` is defined
the same way.

## Theorem
1. **Approximation.** Let `(B_n, Σ_n)` be marked groups converging to `(B, Σ_B)` in the space of
   marked groups. Then `F_B` is a limit of marked subgroups `Q_n ≤ F_{B_n}`. Under the limit,
   each `s ∈ Σ_B` goes to the action of the corresponding generator of `B_n`.
2. **Isolation.** If `F_B` is finitely presented, then `(B, Σ_B)` is isolated. The same holds
   if `D(F_B)` is finitely presented, since then `F_B` is (by
   `fp-stabilizer-engines-need-decidable-vertex-groups`). So `B` is finitely presented and
   finitely discriminable.
3. **Corollaries.**
   - (a) **Reid's group is not finitely presented** (`k = 2`, `B = Z`, MO 339541). Neither is
     its simple derived group. Also, `F_B` is infinitely presented for every infinite finitely
     generated residually finite `B`.
   - (b) **Simple inputs.** If `S` is an infinite finitely generated simple group that is not
     finitely presented, then `D(F_S)` is not finitely presented. Such `S` with solvable word
     problem exist: the derived full group of a minimal subshift with decidable language (for
     example Sturmian) is finitely generated, simple and infinitely presented (Matui).
     So `simple-inputs-have-finitely-presented-stabilizer-engines` is false.
   - (c) **Track C (`boone-higman-via-stabilizer-engines`) is circular.** A simple isolated
     group is a finitely presented simple group, and for an input already inside one, the
     engine adds nothing.
   - (d) **The flux-free test is not decided.** Thompson's `F` is isolated: it is finitely
     presented, and every nontrivial normal subgroup contains `F'`. Thompson's `V` is isolated
     (finitely presented and simple). So the theorem is silent for `B = F` and `B = V`.
     *Superseded (bh-invent-18, 58db3f3f9):* `stabilizer-engines-need-torsion-vertex-groups`
     collapses a deep subgroup into the base edge stabilizer and shows `F_B` is infinitely
     presented whenever `B` has an element of infinite order, so `B = F, T, V` are decided
     negatively.

## Proof of 1
**Tables.** An element `f ∈ F_B` is given by a table:
- a finite partition of `X_B` into clopen sets, each a Boolean combination of shadows
  `Sh(e)` of directed edges;
- a label `d ∈ D` on each piece;
- the translated pieces again form a partition.

Every clopen set of `X_B` is such a Boolean combination. This is because the complement of a
basic neighbourhood of a vertex point `y` is a finite union of shadows of edges at `y`.
Nonempty clopen sets contain shadows, and `D` acts locally uniquely: an element fixing a
shadow pointwise fixes an edge, and edge stabilizers are trivial.
- So `f = 1` iff every label is `1`.
- Also, the table of a product is computed from the tables of the factors by finitely many
  refinements and label multiplications.

**The finite configuration of a word.** Fix a word `w` in a finite generating set `Σ` of `F_B`.
Its evaluation uses:
- finitely many directed edges, namely elements of `D` given by words of bounded length;
- finitely many Boolean combinations of their shadows;
- finitely many label products.

All of this is determined by finitely many facts:
- which of these bounded words are equal in `D`;
- how the edges sit in `T` (equality, adjacency, which side of which), which is read off the
  free-product normal form of `d^{-1}d'`;
- which Boolean combinations are empty.

Emptiness is combinatorial. At an `A`-vertex it depends on the `k` children. At a `B`-vertex,
`Sh(e) \ (Sh(e_1) ∪ … ∪ Sh(e_m))` is never empty, because there are infinitely many children
and the vertex point.

**Transfer.** Marked convergence `B_n → B` gives convergence `Z/k * B_n → D`: free reduction
uses only bounded relations of `B`. It also gives `|B_n| → ∞`. So for `n ≥ n(w)`:
- every fact above holds verbatim in the tree of `Z/k * B_n`;
- at `B_n`-vertices there are spare children, so no used atom becomes empty.

**Images of generators.** For `f ∈ Σ`, its table with labels reduced to `Z/k * B_n` is a
partition-to-partition table for `n` large. It defines `f_n ∈ F_{B_n}`. Let `Q_n = ⟨Σ_n⟩`.

**Convergence.** The table computation of `w(Σ_n)` is the transported computation of `w(Σ)`.
- If `w = 1`, every final label is trivial, so `w(Σ_n) = 1`.
- If `w ≠ 1`, some label `u ≠ 1` in `D` has bounded length, so `u_n ≠ 1` for `n` large. That
  piece is nonempty, and local uniqueness holds in `X_{B_n}` as well, so `w(Σ_n) ≠ 1`.

Thus `(Q_n, Σ_n) → (F_B, Σ)`. Choose `Σ ⊇ Σ_B` from the start; finite presentability does not depend on the finite generating set. For `s ∈ Σ_B` the table is `(X, s)`, so `s_n`
is the action of `s ∈ B_n`.

## Proof of 2
- **Setup.** Suppose `F_B = ⟨Σ | R⟩` with `R` finite, and `(B_n, Σ_n) → (B, Σ_B)` with
  `(B_n, Σ_n) ≇ (B, Σ_B)` for all `n`.
- **An epimorphism.** By part 1, for `n ≥ max_{r∈R} n(r)` every relator holds in `Q_n`.
  So there is an epimorphism `φ_n : F_B → Q_n` with `φ_n(f) = f_n`.
- **Its kernel.** Let `N = ker φ_n`. `D(F_B)` is simple
  (`free-product-boundary-groupoids-carry-the-vertex-group-homology`), so
  `N ∩ D(F_B)` is `1` or `D(F_B)`.
  - *Case `D(F_B) ⊆ N`.* Then `Q_n` is abelian. But take any `g, h ∈ F_B` with
    `[g,h] ≠ 1`. By part 1, `[g,h]_n ≠ 1` for large `n`. Contradiction.
  - *Case `N ∩ D(F_B) = 1`.* Then `N` centralizes `D(F_B)`. The centralizer of `D(F_B)` in
    `Homeo(X_B)` is trivial:
    - every nonempty clopen `U` contains three sibling shadows at a `B`-vertex, and they are
      `D`-translates of one another;
    - the commutator of the two swap involutions they define is a nontrivial element of
      `D(F_B)` supported in `U`;
    - if some `h ≠ 1` commuted with `D(F_B)`, take `U` with `hU ∩ U = ∅`. Then `h` conjugates
      an element supported in `U` to one supported in `hU`, which is a different element.

    So `N = 1`, and `φ_n` is injective. On `B = ⟨Σ_B⟩ ≤ F_B` it is the homomorphism
    `s ↦ s_n` into `B_n`, which acts faithfully on `X_{B_n}`. Its image is `⟨Σ_n⟩ = B_n`.
    So `(B, Σ_B) ≅ (B_n, Σ_n)` as marked groups. Contradiction.
- **Conclusion.** So `(B, Σ_B)` has no such approximating sequence, that is, it is isolated.
  Cornulier–Guyot–Pitsch then give finite presentation and finite discriminability.

## Proof of 3
- **(a)** `Z/n → Z` as marked groups. More generally, for residually finite `B`, the quotients
  by finite-index normal subgroups missing larger and larger balls converge to `B`.
- **(b)** An isolated group is finitely presented. For the example, `S = D([[φ]])` with `φ`
  Sturmian is finitely generated and simple (Matui) and not finitely presented (Matui;
  Grigorchuk–Medynets). Its word problem is decidable, because the action of each generator
  on cylinders is computable from the rotation.
- **(c)** An isolated simple group is finitely presented.
- **(d)** Cannon–Floyd–Parry: every nontrivial normal subgroup of `F` contains `F'`.

## Relation to the other engine nodes
- **The cusp picture is the emitter.** The canonical cusp `(P × Cantor)^+` of
  `hard-cusps-are-canonical-and-flux-free` is the bottom member `K = S⁺` of the blow-up family
  of `stabilizer-engines-embed-in-every-branch-compactification`. It is not the SFT
  with an isolated dense orbit, (IE′) there and (★𝒞) in
  `decidable-groups-embed-in-rigid-sft-compactification-groups`.
- **Why the proof stops at blow-ups.** The emitter's combinatorics is decided by bounded
  relations of `B`, so it passes to approximating groups. That is the whole proof.
  A finite-type blow-up `K = \overline{Sx}` breaks that transfer. Emptiness of cylinders in an
  orbit closure is global, and an approximating group need not carry an isolated seed point
  at all.
- **The substitution.** So the rigidity of the vertex group (isolation among marked groups)
  must be replaced by rigidity of a configuration (an isolated seed point in an SFT). This
  explains why several lanes converged on that object. It is the only way left to make the
  engine's finiteness depend on something other than the vertex group being isolated.

## Lesson for general BH
- **The principle.** A full group built from a marked vertex group `B` by rules that read only
  bounded relations of `B` is a marked limit of the same construction over any groups
  approximating `B`. If it has simple derived group with trivial centralizer, it can be
  finitely presented only when `B` is isolated.
- **What it kills.** Infinite emitters therefore certify nothing beyond the vertex group. They
  are finitely presented only over isolated groups, so hard (infinitely presented) inputs
  never have finitely presented emitter engines. Reid's group is not finitely presented, and
  Track C is circular.
- **What survives.** The one route left in this family is the finite-type blow-up: a
  compactification whose local rules do not transfer to approximating groups, namely an SFT
  with an isolated dense orbit.
- **What to test next.** The next test is whether that isolated-seed rigidity can itself be
  approximated, that is, whether the transfer argument extends to finite-type blow-ups.
