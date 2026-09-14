# sk-exact-banded: plan (2026-09-14, wave 12)

Lane sk-exact-banded. Question: is G_X = EL_3(LC(X,F_2) ⋊ Z) exact (property A, equivalently C*_r(G_X) exact), for an infinite minimal subshift X? The open node is `subshift-elementary-groups-are-exact`. Main at planning time: a40b790b0e.

## What is on main (read, not re-derived)
- **sk-exact-gx** (sk-verify-16 PASS):
  - subgroups of GL_m(LC(X,F_q)⋊Z) of bounded u-width are locally finite;
  - stabilizers of two-ended lattice pairs are locally finite;
  - G_X ≤ GL^{band}(Z×3;F_2), the unit group of banded matrices with banded inverses.
- Dead routes recorded on the open node:
  - the essentially free p.m.p. algebraic action;
  - Tate lattices at one end (non-amenable stabilizer);
  - finite asymptotic dimension ([[T]]′ ⊇ ⊕Z);
  - wobbling / coarse groupoid (isotropy);
  - the cut space (reformulation only);
  - weakly embedded tower expanders;
  - sup-metric masks.
- Open steps from sk-exact-gx: (P-a) FDC or boundary amenability of the two-ended lattice space, and (P-b) uniform FDC of the bounded-width fibres Q_r.

## Literature bound (this lane, 2026-09-14)
- Two web searches ("wobbling group … exact property A finitely generated subgroups"; "exactness topological full group … amenable germs") and one fetch (Corson arXiv:2504.21496, abstract).
- Found: Juschenko–de la Salle, *Invariant means for the wobbling group* (Bull. Belg. Math. Soc. 22 (2015)), which is about amenable actions and invariant means; Corson 2504.21496, whose abstract concerns dyadic rationals in bounded-displacement groups; the Juschenko–Monod and Matui papers on topological full groups; and the statement that wobbling groups of subexponential-growth spaces have no infinite Kazhdan subgroups.
- Not found: any theorem on exactness or property A of finitely generated subgroups of W(Z), or of unit groups of algebraic uniform Roe algebras over finite fields. The question looks open, within this bound.

## Plan
**Part 1: rigorous reformulations (this lane proves them).**
- **L-A (linear wobbling = subshift crossed products).** GL^{band}(Z×m;F_q) ≅ GL_m(ℓ^∞(Z,F_q) ⋊ Z) = GL_m(LC(βZ,F_q)⋊Z). Every finitely generated subgroup comes, through the orbit representation at a transitive point, from GL_m(LC(Y,F_q)⋊Z) for a transitive subshift Y, and that representation is faithful. So "every finitely generated subgroup of the linear wobbling group is exact" is a statement about subshift crossed-product groups.
- **L-B (tower and corner transfers).**
  - Tower identity: for the height-k tower system X′ over X, G_{X′} ≅ EL_{3k}(R_X). It uses EL_3(M_k(S)) = EL_{3k}(S) and R_{X′} ≅ M_k(R_X).
  - Corner transfer: for nonempty clopen V, EL_n(R_{X_V}) ≤ EL_n(R_X) ≤ EL_{nk}(R_{X_V}) for some k.
  - Consequences: the sets of exact EL_n(R_X) are initial segments of n ≥ 3, and "EL_n(R_X) exact for all n" is invariant under Kakutani equivalence of minimal Cantor systems. "G_X exact for every infinite minimal subshift X" is equivalent to "EL_n(R_X) exact for all n and all X".

**Part 2: toward (P-b) and (P-a).**
- **(P-b).** Test whether the bounded-width fibres Q_r have property A in the induced word metric. Tool: tower factorization into two block-diagonal locally finite pieces (Strang; sk-free-6 Theorem D's compression), plus the coarse radius function ρ (the coefficient dependency radius, 1-Lipschitz up to r).
- **(P-a).** The scaling lattices a(x) with a(Tx) ≤ a(x)+1 as a direct union over Kakutani–Rokhlin partitions. Check the fibering permanence theorem for property A at source (Guentner's survey; Dadarlat–Guentner) before building on it.

**Part 3: non-exactness test N3.** Decide whether a residually finite non-exact group (Osajda, GAFA 28 (2018)) can admit a faithful banded representation over F_q on Z×m. Necessary conditions: no distorted elements (sk-sl3z-bandwidth), and linear Krylov growth dim span(B_r v) ≤ m(2wr+1) for finitely supported v.

**Landing.** Artifacts `research/artifacts/sk-exact-banded-2026-09-14[-partK].md`; claim and route nodes for L-A and L-B; Attempts merged onto the open node. Review requests go to sk2/queue/verify.txt.
