# gq-bhm-pattern board (DONE for this run)
**Approach** (family: reframing / obstruction): abstract BHM's Q <= T-bar into a union criterion plus the
central-lift split, and find its exact scope for GL_n(Q).
**Established** (lane proofs, not independently reviewed):
- `ascending-unions-embed-along-coherent-chains` (+ -proof), ca5d1bebd. H = union H_m embeds in Gamma iff the
  embeddings of the H_m agree on restriction up to conjugacy; there is also a class form, and BHM Lemma 7 is the
  extension form. The root is equivalent to: one f.p. simple Gamma holds the chain GL_n(Z[1/m!]) coherently.
- `sl-n-q-lies-in-one-factor-of-every-normal-series` (+ -proof), ca5d1bebd, credit fix aae632750. In any normal
  series of any E ⊇ SL_n(Q)/C, the first term containing it gives a factor holding a perfect image with all root
  groups ≅ Q. The proof cites nothing (transvection lemma, four squares for n = 2). The consequence "no group with
  abelian-or-Q-free factors" is implied by the earlier `extension-product-closures-cannot-create-sl-n-q`.
- artifact `research/artifacts/gq-bhm-pattern-union-and-scope.md`. It covers:
  - BHM in three moves: roots in an ambient, a f.p. centralizer, a central split;
  - the needs N1–N4 for GL_n(Q).
**Needs**: none.
**Dead**: the BHM central split (M3) for SL-type groups at any depth.
**Sparks** (artifact §5, for anyone):
- S-a: a commensurator engine, i.e. a f.p. Gamma ≤ Comm_P(<u>) with dilations d_p, d_p u d_p^-1 = u^p;
  it needs root uniqueness in P.
- S-b: a Hall-type homogeneity (class form) for standard embeddings of GL_n(Z[1/N]) in one f.p. simple group.
**Note (from gq-deep-ring-1, c71dd8fe4):** a second instance of the extension form with no central split.
(Q,+) ≤ <V, t> ≤ U(L_Z(1,2)), t = 1 + x_01 y_00. The roots come from Kronecker refinement plus a V-rotation.
It stops at Aff(Q) because t is not conjugate to t^p (cokernel invariant). This is a test case for spark S-a.
