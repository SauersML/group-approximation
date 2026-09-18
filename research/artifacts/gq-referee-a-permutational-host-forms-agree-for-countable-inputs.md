# Referee report (gq-referee-a, proof-gap lens): permutational host forms for countable inputs

**Reviewed:** `permutational-host-forms-agree-for-countable-inputs` and its route `-proof` (7ee358237),
read on origin/main.

**Verdict: PASS (proof-gap lens).** No step uses generators of `H`, or any hypothesis on `H`. Each
implication is a statement about the host, followed by passing to a subgroup.

## 1. The equivalences

- **(2 ⇒ 1).** `fp-finitary-alternating-overgroups-have-type-a-actions`, item 3, is about `Γ` alone.
  Its stabilizer proof `finitary-alternating-overgroup-type-a-proof` was read: Schreier transversal
  data, finite `D_0`, gluing of `Alt(D)` by Jordan's theorem. It uses only finite generation of `Γ`.
  Then `H ≤ Γ`.
- **(1 ⇒ 2).** `H ≤ Γ_0 ≤ SV_{Γ_0} ≤ FSym(Ω) ⋊ SV_{Γ_0}`.
  - The finite presentation of the last group needs two inputs. The first is the oligomorphic
    condition on injective 4-tuples of clopens, from `twisted-btb-clopen-action-is-type-a` item 3.
  - The second is that stabilizers of two-element sets are finitely generated. Item 4 of the same node
    gives point stabilizers `D(U) × D(U^c) ≅ SV × SV`. For a two-element set `{U, U'}` the setwise
    stabilizer contains the pointwise stabilizer with index at most 2. The pointwise stabilizer is the
    stabilizer of the Boolean atoms, a finite product of copies of `D(atom) ≅ SV`, so it is finitely
    generated. This step is implicit in the cited node and not re-proved there. I checked it for
    finite Boolean patterns.
- **(1 ⇒ 3) and (3 ⇒ 1).** Immediate from the same nodes.
- **Kernel removal.** `K ≤ Stab_G(s)`, so `Stab_{G/K}(s) = Stab_G(s)/K` is finitely generated. Pair
  orbits are unchanged, and `H ∩ K = 1` makes `H → G/K` injective. Correct.

## 2. Not in my lens

- **Membership of countable abelian groups, including `Q` and `Q^x`, in `B_A`.** This rests on the
  hosts listed in BFFHZ Remark 3.5 as recorded in `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`:
  "all finitely presented simple groups of homeomorphisms of the Cantor space containing the
  commutator subgroup of some Higman–Thompson group", applied to `VA ⊇ V`.
  - That is a citation. `gq-referee-b` should check the exact statement of BFFHZ Remark 3.5, and that
    it gives embedding in a finitely presented simple highly transitive group, before this is used as
    a stepping stone.
- **The "no local-to-global step" remark.** It is correctly stated.
