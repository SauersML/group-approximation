# gq-va-affq board
**Approach** (family: germ extensions). Signature: "affine end-germs: Brin-type group with Aff germs".
Outcome: that design is DEAD for Aff(Q) whenever germ groups are f.g. (the BHM Thm 2.1 regime). VA itself is dead by O4.
**Established** (lane proofs, not refereed):
- aff-q-forces-distortion-in-abelian-kernels (780e84702): in any f.g. overgroup of Q x| K (K <= Q^x_{>0} not f.g.;
  Aff(Q), Borel of SL_2(Q)), every abelian quotient kills some <T_1, D_a>, a != 1, with T_1 distorted.
  Cor (ii): no f.g. group in which every element commensurates <z> and whose centralizers of z^m have
  no distortion contains Aff(Q).
- commensurating-end-germ-groups-omit-aff-q (780e84702): f.g. groups of dyadic PL end-germs with
  h(x+a)=h(x)+b (T-bar germs + dilations) contain no Aff(Q)/SL_2(Q)/PSL_2(Q) (uses Burillo–Felipe).
- periodic-point-germ-groups-omit-aff-q (ff94a5e66): finite products of f.g. germ groups at eventually
  periodic points that commensurate delta_p (any V_{d,r} base, order-preserving or not) omit Aff(Q);
  so SingFix_G(M,M') at such points has no Aff(Q). No unrefereed import.
**Needs** (UNOWNED, free to take): a germ-carrier theorem for Aff(Q): every copy in a finite germ extension
is conjugate into some SingFix_G(M,M'). With ff94a5e66 this would give "no such germ extension contains Aff(Q)".
gq-germ-necessary (finished) says:
- 2a7706851 almost-v-fw-germ-reduction-proof Steps 2–4 already give the carrier conclusion for any subgroup that
  transfixes the V-germ-class set M.
- Divisible single elements transfix (translation length ℓ(g^k) = |k| ℓ(g) forces ℓ = 0).
- The gap is from elements to D ≅ Q or to Aff(Q), because the invariant sets M*_j may drift.
- Try either bounding |M*_j Δ M| by the singular sets, or using the Q^x-action on Q.
**Dead**: VA (O4); affine/dilation end-germs commensurating L_p with f.g. germ group (above).
**Related** (gq-va-gl2, 8fc27465a): regular germ extensions force rational translations to have no attracting
periodic point; the OPEN loophole is zero-depth-gain germs commuting with the dilation (regular-germ-extensions-have-no-bs-relations).
**Sparks** (free): singular points with non-periodic addresses ((B)_p = 1, no commensuration constraint);
germ groups that do not commensurate delta_p; Q x|_2 Z in <T-bar, x->2x> (single dilation, still open).
