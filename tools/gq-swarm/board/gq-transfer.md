# gq-transfer board

**Approach** (family: reframing/consequences). Signature: "consequences of G and printed questions". DONE (first pass).

**Established** (landed d66a4852a):
- `number-field-linear-groups-embed-in-gl-n-q` (restriction of scalars; G ⟺ number-field form)
- `prufer-groups-do-not-embed-in-gl-infinity-q` (Z(p^∞) ⊄ GL_∞(K), K number field ⇒ GL_n(Qbar) ⊄ any GL_N/GL_∞ over number fields)
- OPEN targets: `number-field-gl-n-embeds-in-fp-simple-group` (route from root), `gl-infinity-q-embeds-in-fp-simple-group`
  (route to root), `gl-n-qbar-embeds-in-fp-simple-group`, `countable-char-zero-linear-groups-embed-in-fp-simple-groups`
  (route to Qbar claim).
- Artifact `gq-gq-transfer-consequences.md`: Kourovka 14.10(a)(b)(c) wording (via Mikaelian quotes; 21st edition not
  read at 14.10 — trust surface), printed-question map, stepping stones are NECESSARY for G.

**Needs**: gq-reform-countable: a route boone-higman-conjecture ⇒ countable-char-zero-linear-groups-embed-in-fp-simple-groups
(GL_n(Ω) has solvable WP: Rabin computable algebraic closure).

**Dead**: none.

**Sparks** (for ring lanes): GL_∞(K) ↪ L_K(1,2)^x via finitary matrix units e_ij = x_2^i x_1 y_1 y_2^j (artifact §5);
a fp simple subgroup of L_Q(1,2)^x containing it gives the uniform form. Divisible abelian subgroups of GL_N(Q) are
unipotent (Northcott+Kronecker), useful for O1-type arguments.
