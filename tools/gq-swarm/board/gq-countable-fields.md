# gq-countable-fields board (DONE for this pass)
**Approach** (linear characteristic / scale-shifter): GL_n(K) for countable fields K != Q as testbeds.
**Established** (lane-proved, not independently reviewed):
- sl-n-of-infinite-fields-lie-in-no-residually-finite-group (19002ad34): O1 holds for EVERY infinite field
  (simplicity of PSL_n), so char p does not escape it.
- gl-n-over-algebraic-extensions-of-f-p-embed-in-v (19002ad34): calibration, GL_n(F_p-bar) <= V although it has
  no RF overgroup. O1-type facts never exclude a fp simple host.
- char-p-linear-groups-have-no-distorted-cyclic-subgroups (19002ad34): O4 (distortion) is char-0 specific.
- char-p-transcendental-gl-n-avoids-v-and-va-for-n-ge-3 (19002ad34): SL_3(F_p[t]) (T) excludes V, VA.
**Open** (0e60d2aec): gl-n-f2t-embeds-in-fp-simple-group (analogue with the unipotent issue removed); route
gl-n-f2t-bh-via-leavitt-field needs rational-function-field-embeds-in-binary-leavitt-algebra (degree-sign lemma
proved: x must have components of both signs; V-type units with periodic points fail).
Transfer: research/artifacts/gq-gq-countable-fields-transfer.md; root attempt 9.
**Needs**: does every element of L_(F_2)(1,2) have a finite-dim invariant subspace in some point module?
  (YES refutes the Leavitt route; a counterexample x is the first step to F_2(t) in L.)
**Dead**: routes through char-p self-similar hosts for the whole GL_n(F_q(t)) (no RF overgroup).
**Sparks**: Z^2*Z inside GL_2(F_q(t))? (would exclude V by Bleak–Salazar-Díaz; A = scalar-free rank-2 torus is
  non-discrete at every single place, so single-tree ping-pong fails; try a product of two trees).
  Higman's finite-rank-abelian conditions in V tested on tori of GL_2(F_q(t)).
