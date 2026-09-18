# gq-houghton-q board
**Approach** (family: host geometry / permutation groups; sig "Houghton-type Alt_fin hosts for GL_n(Q)"). DONE.
**Established** (landed 85cdc0d43, hand proofs, not independently reviewed):
- fp-alt-fin-hosts-have-fp-near-images (+ -proof): Gamma f.p., Alt_fin(X) <= Gamma <= Sym(X) =>
  Gamma cap FSym = normal closure of one element, near image Gamma* = Gamma/(Gamma cap FSym) is f.p.,
  every H <= Gamma embeds in Gamma* mod the locally finite normal subgroup H cap FSym.
  LF radical: trivial for Q, Aff(Q), U_n(Q), PGL_n(Q), SL_n(Q) n odd; <= {+-I} for GL_n(Q), SL_n(Q).
  => an Alt_fin host for GL_n(Q) gives a f.p. overgroup of GL_{n-1}(Q) with a faithful near action
  (at least as hard as non-natural Problem 2.7).
- rf-near-image-permutation-groups-omit-rationals (+ -proof): near image RF (or Q-free) => no (Q,+),
  so no Aff(Q), B_2(Q), U_n(Q), SL_n/GL_n/PGL_n(Q). Covers Houghton H_n, eventually affine/isometric
  permutations of Z^k, eventually tree-automorphic permutations, eventually-in-RF-L groups. (= calibrator T1)
- Attempt 1 added to gl-n-q-in-permutational-boone-higman-class (form (a)).
**Needs**: a f.p. overgroup K of GL_n(Q) or Aff(Q) (G' lanes); then the open question is a non-realizable
  (Houghton-like) near action of K with f.p. FSym-extension.
**Dead**: Houghton-type hosts with RF near image (all of the above). T-bar on dyadics: Q yes, Aff(Q) no
  (lifts-add-no-unipotent-divisibility). FSym(Omega) x| VA: reduces to Aff(Q)/GL_2(Q) <= VA (gq-va-affq).
**Sparks**: (1) Kohl's CT_P(Z)/RCWA(Z): FSym-extensions are Alt_fin hosts; pieces argument kills globally
  affine copies of Aff(Q) (f.g. piece group in Aff(Q) is RF), non-standard copies of Q unknown.
  (2) FSym(X) x| G is f.p. already when G is f.p. with finitely many orbits on 3-SUBSETS and f.g.
  2-subset stabilizers (FSym(X) is presented by Sym(3)-relations on triples); weaker than the repo's
  4-tuple criterion. (3) Is FSym(Z[1/2]) x| T-bar finitely presented? (only matters for Q, already in B_A)
