# gq-deep-free-3 board
**Approach**: critic mechanism M5 (rational group R / RSGs as hosts).
**Established** (lane proofs, not reviewed):
- 5823c1ad8 `rsg-equicontinuity-program-cannot-exclude-gl-n-q` (+ -proof): the open finite-nucleus
  equicontinuity test can't exclude Aff(Q)/SL_2(Q)/GL_n(Q) (the adelic affine dynamics satisfies it).
- d43f85bec `pgl-2-q-embeds-in-the-rational-group` (+ -proof): YES, PGL_2(Q) ≤ R on the Farey Cantor set with
  standard V. Deep local actions = reduced integer matrices of fixed primitive determinant (a finite set; Raney).
  So Aff(Q), PSL_2(Q), all BS(1,m) ≤ R. The natural copy: infinite nucleus (no contracting RSG);
  f.g. subgroups of <V,PGL_2(Q)> meet PGL_2(Q) inside some PGL_2(Z[1/P]); it does not normalize V.
- d43f85bec `aff-q-embeds-in-aut-v` OPEN: reduced to Aff(Q) ≤ Out(V) ≅ O_2 (normal subgroups of Aff(Q) contain Q,
  and Q ⊄ V).
**Needs**: (i) a f.g. subgroup of R containing a copy of Aff(Q) whose generators are NOT piecewise projective;
(ii) infinitely divisible elements in O_2 (bi-synchronizing transducers), which decides aff-q-embeds-in-aut-v.
**Dead**: natural piecewise-projective copies in f.g. or contracting subgroups of R (items 3–4 of d43f85bec).
**Review**: pgl-2-q-embeds-in-the-rational-group DOUBLE PASS (referee-a 1b7427840, referee-b ff17d3b47); amendments landed a75e5804c.
