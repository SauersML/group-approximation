# Referee C (end-to-end, adversarial) — `fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups`

**Verdict: PASS-with-fixes** (one wording fix).

- **Item 1** assembles `fp-self-similar-subgroups-satisfy-permutational-boone-higman`:
  - f.g. subgroups of `GL_n(Q)` lie in an f.p. group `Γ` with a faithful type (A)
    action on `S`;
  - BFFHZ then make `SV_Γ` finitely presented and simple, containing `Γ`.

  No finite-extension or quotient step is used. The credit is stated honestly as
  "known in substance" (BFFHZ Remark 3.5 and Theorem C; Zaremsky 2405.18354
  Theorem A).
- **Item 2.**
  - A faithful action of an infinite group on a finite set is impossible. So if
    `H` is infinite, `Γ ⊇ H` is infinite and `S` is infinite.
  - `SV_Γ` contains the prefix-replacement group on any `k` coordinates of `C^S`,
    hence `kV`.
  - With `rationals-embed-in-brin-thompson-group-2v` this gives `Q ≤ 2V ≤ SV_Γ`.
  - Correct.
- **F1 (wording).** The title says every f.g. subgroup embeds in an f.p. simple
  `SV_Γ` "which also contains 2V and so Q". Item 2 proves that only for infinite
  `H`. For finite `H`, `S` may be finite. Either restrict the title to infinite `H`,
  or add the one-line enlargement: embed `H` block-diagonally as `diag(H, 1)` in
  `GL_(n+1)(Q)`, next to the commuting element `diag(I_n, 2)`. The subgroup they
  generate, `H × Z`, is infinite and finitely generated. Apply the node to it.
