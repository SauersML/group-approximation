# sk-exact-gx: exactness of G_X, part 1 (2026-09-13)

Lane sk-exact-gx, wave 11. Plan: `research/artifacts/sk-exact-gx-plan-2026-09-13.md` (4730b5efe7). Question: is G_X = EL_3(LC(X,F_2) ⋊ Z) exact, for X an infinite minimal subshift? It stays OPEN. This part lands two established results (unreviewed) that change the route map, and records where each route dies.

## 1. Results (proofs in the route nodes)
**Theorem 1** (`bounded-width-subgroups-of-subshift-gl-are-locally-finite`). Let Γ ≤ GL_m(LC(X,F_q) ⋊ Z). If the u-width of its elements (largest |k| with a nonzero u^k-coefficient in g or g^{-1}) is uniformly bounded, then Γ is locally finite.
- **Proof idea.** The span U_t of the Γ-orbit of a basis vector at site t sits in a window of dimension ≤ m(2p+1) and is Γ-invariant. Γ embeds in ∏_t GL(U_t), and a finitely generated subgroup has only finitely many distinct kernels there, since normal subgroups of F_k of index ≤ c are finite in number.

**Theorem 2** (`subshift-el3-two-ended-lattice-stabilizers-locally-finite`). Put B = LC(X,F_2), R = B[u^{±1};α], R̂_+ = B((u)), R̂_- = B((u^{-1})).
- G_X acts by right multiplication on the countable sets 𝓛_± of finitely generated B[[u^{±1}]]-lattices in R̂_±^3.
- The stabilizer of the standard lattice at one end is GL_3(B[u;α]) ⊇ SL_3(F_2[u]), which is non-amenable.
- The stabilizer of ANY pair (L_+, L_-) is locally finite: fixing both ends bounds the width by 2n, and Theorem 1 applies. For the standard pair it is G_X ∩ GL_3(B).

**What changes on the route map.**
- The open node's "Tate-space lattices, dies" used one end. With both ends, all point stabilizers are amenable, exactly as for SL_3(F_2[u^{±1}]) on the product of the Bruhat–Tits buildings at 0 and ∞.
- The remaining difference is the residue ring. For F_2[u^{±1}] it is F_2, so the buildings are locally finite. For G_X it is B, which is infinite, and B is twisted by α across positions.

## 2. What exactness needs from here, and why off-the-shelf theorems do not apply
**Sources checked:**
- Guentner–Tessera–Yu, *Discrete groups with finite decomposition complexity*, Groups Geom. Dyn. 7 (2013) 377–402, doi 10.4171/GGD/186, p. 378. Verbatim:
  - "The collection of countable groups having finite decomposition complexity is closed under the formation of subgroups, extensions, free amalgamated products, HNN extensions and direct unions."
  - "The collection of countable groups having finite decomposition complexity contains all countable subgroups of GL(n,R), where R is any commutative ring, all countable subgroups of an almost connected Lie group, all hyperbolic groups and all elementary amenable groups."
  - "Countable FDC groups have Property A."
- Why none of these closure properties reaches G_X:
  - G_X is finitely generated, so direct unions do not help.
  - It is simple, so there are no extensions.
  - It has (T), so it is no nontrivial amalgam or HNN extension (FA).
  - R is not PI: it contains M_n(F_2) for every n, through tower algebras. So G_X lies in no GL_n over a commutative ring.

**Route P (fibering over two-ended lattices), the open step.** The orbit map g ↦ (O_+^3g, O_-^3g) is uniformly expansive for the natural distances d_±(L,L′) = min{m : u^mL ⊆ L′ and u^mL′ ⊆ L}. Its fibres over bounded sets are cosets of the bounded-width sets Q_r = {g : w(g) ≤ r}. Two missing ingredients:
- **(P-a)** FDC, or boundary amenability, of 𝓛_+ × 𝓛_-. These spaces are C(X,·)-families of lattices twisted by α, not finite-dimensional buildings. Scaling lattices L_a = {Σf_ju^j : f_j(x)=0 for j<a(x)} exist for every locally constant a with a(Tx) ≤ a(x)+1, and bumps on disjoint towers give many independent directions. So no finite asymptotic dimension, and no off-the-shelf property A.
- **(P-b)** Uniform FDC of the fibres h·Q_r in the word metric of G_X. Q_r is a set, not a group. Its elements of bounded word length generate coefficient complexity along the orbit, so the r-components of Q_r are infinite.

**Route Q (cut space) is only a reformulation.**
- G_X/S_y, with S_y the locally finite cut stabilizer (PASS, sk-verify-13 part5), carries all the geometry of G_X.
- An amenable action on β(G_X/S_y) implies exactness, as does any amenable action on a compact space.
- Constructing one is as hard as the problem itself. For F_2[u^{±1}] the cut space is the group modulo a finite subgroup.

**Linear wobbling reformulation.**
- Through the faithful orbit representation, G_X ≤ GL^{band}(Z×3;F_2), the unit group of the algebraic uniform Roe algebra of Z over F_2: banded invertible matrices with banded inverses.
- So a positive answer to "are finitely generated subgroups of GL^{band}(Z×k;F_q) exact?" would settle G_X.
- Strang, *Banded matrices with banded inverses and A = LPU* (MIT preprint, abstract, verbatim): "If A is a banded matrix with a banded inverse, then A = BC = F_1 … F_N is a product of block-diagonal matrices. We review this factorization, in which the F_i are tridiagonal and N is independent of the matrix size. For a permutation with bandwidth w, each F_i exchanges disjoint pairs of neighbors and N < 2w. This paper begins the extension to infinite matrices. For doubly infinite permutations, the factors F now include the left and right shift."
- So at each width, GL^{band} is generated in boundedly many steps by the two locally finite groups of 2-site block-diagonal matrices, plus shifts. The permutation version W(Z) has the same structure, which is why this structure alone decides nothing.
- **Contrast.** Kazhdan subgroups of W(Z) are finite: the open node proves this (Schreier graphs of infinite orbits have linear growth). GL^{band}(Z×3;F_2) contains the infinite simple Kazhdan group G_X. So permutation arguments do not transfer to the linear setting.

## 3. Non-exactness tests (dead, with reasons)
- **N1, weakly embedded expanders through tower copies.** The tower copies H_V ≅ GL_{3h}(F_2) over Kakutani–Rokhlin towers of height h are expanders for suitable generators. For a uniformly Lipschitz inclusion, their generators need bounded G_X-length.
  - A word of length r has coefficients depending only on coordinates in [−r,r].
  - The matrix units of H_V involve level indicators e_{T^aV} with V ∩ T^jV = ∅ for 0 < |j| < h.
  - For Sturmian X, cylinders of length L have measure ≥ 1/(L+1), and a clopen set with return time ≥ h has measure ≤ 1/h. So V depends on ≳ h/2 coordinates and the non-constant generators have length ≳ h/2.
  - Only SL_3(F_2) ⊗ I is cheap, so homomorphic tower copies are not weakly embedded.
  - Not ruled out: non-homomorphic Lipschitz maps with small fibres.
- **N2, sup-metric copies through full-group cocycles.** Products g_1^{n_1}⋯g_k^{n_k} of commuting first-return maps on disjoint clopen sets realize arbitrary masks S ⊆ {1..k}. Every ball of radius r in G_X has ≤ e^{Cr} elements, so some masks cost ≳ k/C. The induced metric is not uniformly comparable to ℓ^∞ on Z^k, and no expanders arise this way.
- **N3, Osajda-type subgroups.** Any non-exact subgroup of G_X must have no distorted elements (sk-sl3z-bandwidth, PASS), and by Theorem 1 every subgroup of bounded width is locally finite. Whether Osajda's graphical small cancellation RF groups admit faithful banded representations over F_2 on Z×k is untested.

## 4. Sharpest next steps
- **(P-a) on the simplest model.** The Z-scaling part of 𝓛_+: locally constant a with a(Tx) ≤ a(x)+1, under the action of [[T]]-cocycles. Does it admit a G_X-equivariant decomposition compatible with Kakutani–Rokhlin partitions, as a "direct union over clopen partitions" that GTY's permanence could use?
- **The linear wobbling question** for k = 1, q = 2: are the finitely generated subgroups of GL^{band}(Z;F_2) exact? Test first on groups of linear cellular automata with position-dependent rules coming from minimal subshifts.
