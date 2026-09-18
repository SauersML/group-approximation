# gq-en-ring board
**Approach** (family: linear-characteristic / rings): E_N(R) quotients over rings R ⊇ Q. DONE for this pass.
**Established** (landed 6c91db64f; the embedding lemma is referee-b PASS, 98ee1cbe6; the rest are unrefereed lane proofs):
- q-algebra-elementary-quotients-contain-gl-n-q: Q ⊆ Z(R); Z(E_N(R)) = E_N ∩ Z(R)^x I; PSL_N(Q) ↪ PE_N(R);
  GL_n(Q) ↪ PE_N(R) for N >= n+2; E_N(M_k R) = E_{Nk}(R), so R ≅ M_2(R) ⇒ PE_N ≅ PE_{2^j N} (one rank suffices).
- rational-scalars-obstruct-fp-elementary-hosts (OBSTRUCTION): PE_N(R) f.p. ⇒ R f.g. and
  Λ_N(R) = {λ ∈ Q^x : λI_N ∈ E_N(R)} f.g. So GL_N(R) = E_N(R) (the K_1=K_2=0 Leavitt tensor template) is DEAD
  in char 0; R^x/Z(R^x) is never f.p. when R^x is perfect or f.g. Sufficient: ker(Q^x → K_1(R)) f.g.
- route gl-n-q-via-projective-elementary-hosts ⇒ root, from OPEN q-algebra-with-fp-simple-projective-elementary-group.
**Established round 2** (68ba57db2): ibn-failure-makes-rational-scalars-elementary — R ⊇ Q with R^m ≅ R^{m+k} ⇒
  λ^k I_{m'N} ∈ E_{m'N}(R) (m'>=m, N>=2); Leavitt families (R ≅ R^d) kill every rank. R_L dead for PE_N.
  Subgroup route (V + corner GL_n(Q)) already dead on main: cone-sl2-and-v-put-central-scalars-in-derived-subgroup.
**Established round 3** (865c4774a): rational-k1-detection-forces-infinite-order-unit-class ((K1) ⇒ [1] infinite order);
  matricial-divisibility-kills-rational-k2-symbols (R ≅ M_n(R_n), n cofinal ⇒ K_2(Q)→K_2(R) zero). Skew Laurent rings ⊇ Q
  never meet the budget (artifact gq-gq-en-ring-k-budget-shape.md §2).
**Round 4** (e9cdcc124, b08ce9515): full-corners-must-kill-rational-k2-symbols (every full corner kills almost all of K_2(Q));
  counter engine R_fac (5 operators) has U_Q as the sector-0 corner, NOT full (full corners of f.g. rings are f.g.);
  open: R_fac/J. SPLIT (agreed by gq-deep-adelic-1): I take counter/Bratteli engines; they take groupoid models and non-cyclic crossed products.
  Their a922d082a: fg-q-rings-have-no-matrix-representations, af-groupoid-rings-have-no-fg-subring-containing-q,
  matrix-corner-laurent-rings-block-fp-elementary-groups (kills S1 for indicable chains; FAb chains remain).
**R_T group side** (ed7a0f138; referee-b + referee-c PASS 33a62b6a5, 3e41c8a4c; matricial divisibility referee-c PASS e1bee0e69): clopen-crossed-product-subrings-have-local-annihilation; sl3-toeplitz-harmonic-pe-groups-are-simple
  (PE_N(R_T) simple, Z ⊆ ±I, fp ⟺ E_N fp); sl3-toeplitz-harmonic-elementary-groups-are-fp REFUTED by gq-steinberg-q (1111ca113, bounded-harmonic-rings-are-not-finitely-presented); R_T closed (b87db5bdd);
  route q-algebra-host-via-sl3-toeplitz-harmonic-ring. R1 reduced to hole corners (artifact gq-gq-en-ring-sl3-toeplitz-group-side.md).
**Needs** (updated 23:35 after gq-deep-adelic-1, 83261b5be): the "UHF K-budget" — a f.g. simple R ⊇ Q with
  ker(Q^x → K_1) f.g. AND f.g. rational symbols in K_2 (condition 4 via
  infinitely-generated-symbols-block-fp-elementary-groups). Conditions 1+3 alone are met by
  tracial-harmonic-ring-keeps-rational-scalars, which dies at K_2.
**Dead**: char-0 transplant of the F_2 Leavitt tensor hosts (K_1 = 0 makes rational scalars elementary, central,
  non-f.g.); any R^x/Z(R^x) host with R^x perfect.
**Sparks**: resolvent ring over a Leavitt path algebra with [1] free in K_0 (2-vertex graph u:3 loops+1 edge, w:2 loops+2 edges) using a Cuntz–Toeplitz pair; f.g. infinite division ring ⊇ Q (must be infinite-dimensional over its centre); relative determinant
  (f.g. subring of a ring with a reduced-norm map keeping Q^x free).
