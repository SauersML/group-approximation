# bh-free-49 (free lane; seed: a host for Higman's group H4)

**Direction (updated 11:05).** Graph-of-groups inputs in the permutational class: prove
that faithfulness is free and isolate the local configuration H4 and BG need. Not
Cantor-brick constructions (bh-testcases).

**Landed**
- a7af2a20a: homogeneous invariants vanish on BS bases (no proper cocompact CAT(0) host
  for H4 or BG); a retract inherits proper-power conjugacy (the common-retract,
  graph-product and relative-holomorph closures do not apply to H4's splittings).
- df5f12934 and 837c3d51e: Attempts entries on the H4 and BG nodes.
- 10249e417: three claims.
  1. `pbh-amalgams-over-centralizer-separated-edges`: amalgams and HNN extensions are in
     B_A given a B_A group containing the vertex groups and a centralizer-realized
     separator. One-sided retract version. Configurations are elliptic, so closure never
     creates them.
  2. `bs12-base-generator-is-a-centralizer-in-b-a`: ⟨b⟩ ≤ BS(1,2) is realized. So
     Λ wr_(BS(1,2)/⟨b⟩) BS(1,2) and ⟨a,b,t | b^a=b^2, [b,t]=1⟩ are in B_A; they are not
     quasi-linear.
  3. `higman-chain-group-pbh-iff-chain-configuration`: G_1 ∈ B_A iff some fp twisted BT
     group has a chain configuration (b^a = b^2, c^b = c^2, c of infinite order).
     Necessary for H4 and BG.

**Open leads for anyone**
- Put the twisted coset lamplighter M_1 = (⊕_(BS(1,2)/⟨b⟩) Z[1/2]) ⋊ BS(1,2) in B_A. That
  gives G_1. It is f.g. solvable of derived length 3 and not quasi-linear, a sibling of the
  q-difference lamplighter.
- A twisted coset-wreath closure, with the stabilizer acting on the lamp, would do it.
  Is Ind_C^G(K) ⋊ G ∈ B_A when K ⋊ C ∈ B_A and C is realized?
- Find a chain configuration in an SV_Γ: b of infinite entropy (coordinate-shift type)
  conjugate to b^2, dilating an infinite-order c.
