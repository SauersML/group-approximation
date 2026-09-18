---
rg: 2
id: pbh-finitary-alternating-hosts-proof
kind: route
title: Backward by the finitary stabilizer lemma; forward by adjoining all finitary permutations of the clopen sets to the twisted Brin--Thompson group
target: permutational-boone-higman-iff-finitary-alternating-hosts
requires:
  - fp-finitary-alternating-overgroups-have-type-a-actions
  - finitary-symmetric-extensions-of-oligomorphic-actions-are-fp
  - twisted-btb-clopen-action-is-type-a
  - twisted-brin-thompson-finite-presentation-criterion
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target and in `twisted-btb-clopen-action-is-type-a`.

**(2 ⇒ 1).** `Γ` is finitely presented and `Alt_fin(X) ≤ Γ ≤ Sym(X)`. By
`fp-finitary-alternating-overgroups-have-type-a-actions`, item 3, the
action of `Γ` on `X` is of type (A). So `H ≤ Γ` witnesses 1.

**(1 ⇒ 2).** Let `H ≤ Γ_0`, where `Γ_0` acts on `S` with type (A).

*Step 1. Into `SV_{Γ_0}`.*
- `S` is countable: `Γ_0` is countable and has finitely many orbits on `S` (if `|S| ≥ 2`,
  finitely many orbits on 2-subsets give finitely many point orbits; `|S| = 1` is
  trivial).
- `SV_{Γ_0}` is finitely presented (Zaremsky Theorem A, in
  `twisted-brin-thompson-finite-presentation-criterion`).
- `g ↦ τ_g` is a homomorphism `Γ_0 → SV_{Γ_0}`: each `τ_g` is one branch with empty
  prefixes. It is injective because the action on `S` is faithful. So
  `H ≤ Γ_0 ≤ SV := SV_{Γ_0}`.

*Step 2. Condition 1 for `SV ↷ Ω`.* By item 3 of `twisted-btb-clopen-action-is-type-a`,
`SV` has finitely many orbits on `k`-tuples of `Ω` for every `k`, in particular on
injective 4-tuples.

*Step 3. Condition 2 for `SV ↷ Ω`.* Let `U ≠ W` in `Ω`.
- Let `A_1, ..., A_r` be the nonempty atoms among `U∩W, U∩W^c, U^c∩W, U^c∩W^c`. They
  partition `C^S` with `r ≥ 2`, since `U` is proper, so each `A_j` is proper, i.e. in `Ω`.
- *Claim:* `Stab(U) ∩ Stab(W) = D(A_1) × ... × D(A_r)`.
  - `⊇`: disjointly supported elements commute, and each `D(A_j)` fixes every atom.
  - `⊆`: let `f` fix `U` and `W`. By item 4 for `U`, `f = f_U f_{U^c}` with
    `f_U ∈ D(U)` equal to `f` on `U`. Now `f_U` preserves `W∩U` (it agrees with `f`
    there) and `W∩U^c` (it is the identity there), so `f_U ∈ Stab(W)`.
  - By item 4 for `W`, `f_U = a b` with `a ∈ D(W)`, where `a` equals `f` on `U∩W` and the
    identity elsewhere. So `a ∈ D(U∩W)`. The other three atoms are treated the same way.
    Their four pieces multiply to `f`, and the pieces for empty atoms are trivial.
- Each `D(A_j)` is isomorphic to `SV`: `SV` is transitive on `Ω` (item 3, one orbit on
  1-tuples), and `D(gA) = g D(A) g^{-1}`. With item 4, each `D(A_j)` is finitely
  presented, so `Stab(U) ∩ Stab(W)` is finitely generated.
- The setwise stabilizer of `{U, W}` contains it with index at most 2, so it is finitely
  generated.

*Step 4. Finite presentation.* By Steps 1–3 and
`finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`,
`P := FSym(Ω) ⋊ SV` is finitely presented.

*Step 5. Faithfulness and the finitary subgroup.*
- Let `1 ≠ f ∈ SV`. Pick `κ` with `fκ ≠ κ`, and a clopen `U ∋ κ` with `fU ∩ U = ∅`
  (continuity and a clopen base). Then `fU' ≠ U'` for each of the infinitely many
  nonempty clopen `U' ⊆ U`. So no nontrivial element of `SV` acts on `Ω` as a finitary
  permutation.
- By the faithfulness remark in `finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`,
  `P` acts faithfully on `Ω`.
- `Alt_fin(Ω) ≤ FSym(Ω) ≤ P`, and `Ω` is infinite.
- `H ≤ SV ≤ P`, so `P` witnesses 2.

**The PBH form.** Apply the per-input equivalence to each finitely generated `H` with
solvable word problem.
