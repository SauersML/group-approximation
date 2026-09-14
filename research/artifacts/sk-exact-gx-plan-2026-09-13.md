# sk-exact-gx: plan (2026-09-13, wave 11)

Lane sk-exact-gx. This is a plan with no claims. Problem: is G_X = EL_3(LC(X,F_2) ⋊ Z) exact (property A, equivalently C*_r(G_X) exact) for an infinite minimal subshift X? Open node: `subshift-elementary-groups-are-exact`.

## What main already has (not redone)
- **Dead routes** recorded in the open node:
  - the p.m.p. algebraic action on F_2^{Z×3};
  - permutation (wobbling) models, impossible for infinite Kazhdan groups;
  - the coarse groupoid of Z (dies at germ isotropy);
  - the zero section of X × F_2^{Z×3};
  - **single-end** Tate lattices (stabilizer ⊇ SL_3(F_2[u]), non-amenable);
  - finite asymptotic dimension ([[T]]′ ≥ ⊕_N Z);
  - Alekseev–Finn-Sell sofic criteria.
- **Amenable subgroups available** (PASS, sk-verify-13 part5): the cut stabilizer S_y, the stabilizer of the splitting V^{<0} ⊕ V^{≥0} in the orbit module at y, is locally finite.
- **Constraints on any non-exact subgroup:** no distorted infinite-order elements (sk-sl3z-bandwidth PASS); banded finite representations (sk-lef-embedding-d).
- **Non-exact hosts exist in the lamplighter family** (E1, sk-free-1, unreviewed).

## Routes, in order

### P. Two-ended skew lattices (new; the single-end version is dead)
- **Setup.** Put B = LC(X,F_2) and α = T^*, so R = B[u^{±1};α] and R ⊂ R̂_+ = B((u)) and R ⊂ R̂_- = B((u^{-1})).
- **Action.** G_X acts by right multiplication on the countable sets 𝓛_± of left B[[u^{±1}]]-submodules of R̂_±^3 commensurable with the standard lattice.
- **Stabilizers.** The stabilizer of the standard pair is GL_3(B[u;α]) ∩ GL_3(B[u^{-1};α]) ∩ G_X = GL_3(B) ∩ G_X, which is locally finite (B is a directed union of finite Boolean algebras).
- **P1.** Write out the stabilizers and the G_X-invariant distances on 𝓛_±.
- **P2.** The obstruction to the Guentner–Higson–Weinberger argument is the infinite residue ring B, so the lattice spaces are not locally finite. Test for "C(X)-families of Euclidean buildings" twisted by α: does boundary amenability survive? Test rank one first: G_X is perfect, so G_X ≤ EL_2(M_3(R)) through g ↦ diag(g,1) and the Whitehead identities, which are homomorphic on commutators.
- **P3.** If P2 works, conclude exactness through an amenable action on a compactification of 𝓛_+ × 𝓛_- with amenable stabilizers.

### Q. The cut space
- G_X acts on Y_y = G_X/S_y, the set of splittings of the orbit module reachable from V^{<0} ⊕ V^{≥0}, with locally finite stabilizers.
- **Reduction (direction ⇐, standard):** an amenable action on βY_y gives exactness. Exactness from amenable actions on compact spaces needs no stabilizer condition; the stabilizers matter only for the converse.
- **Q1.** Find almost equivariant η_n: Y_y → Prob(G_X) built from window positions (the window lemma: V^{≥W} ⊆ π(g)V^{≥0} ⊆ V^{≥−W}), or show the natural candidates fail.
- **Q2.** Relate Y_y to 𝓛_+ × 𝓛_-.

### N. Non-exactness tests
- **N1. Weakly embedded expanders.** The tower copies H_V ≅ GL_{3h}(F_2) have Kazhdan generating sets. Is their G_X-length bounded? Propagation plus cylinder complexity suggests length ≳ h, which would kill homomorphic copies. Look instead for uniformly Lipschitz maps from expanders with small fibres.
- **N2. Banded block constructions.** Growing blocks are not locally constant along a minimal orbit. Record why.
- **N3. Osajda-type groups.** Test whether a graphical small cancellation RF group can have banded representations with no distortion.

### L. Literature (bounded)
- Guentner–Higson–Weinberger (exactness of linear groups): its proof structure through valuations, and why R is not PI.
- Exactness for groups acting on non-locally-finite trees (vertex stabilizers exact) and on products of trees.
- Boundary amenability for SL_n(F_q[t]).
- Any result on exactness of unit groups of Steinberg algebras or algebraic crossed products.

## Deliverables
- Established claims only with complete routes, queued in `sk/queue/sk-verify-13.txt`.
- Attempts merged into the open node for every dead route.
- Final report to main.
