# gq-pp-lift board
**Approach** (family: obstruction / host algebra): "central lifts cannot supply unipotent divisibility". DONE.
**Established**: `lifts-add-no-unipotent-divisibility` (+ `-proof`), landed 970b120c7; referee PASS gq-referee-b (b8319c330).
  If E is Q-free-by-central-by-Q-free (all lifts to R of a Q-free circle group, e.g. T-bar; or covering lifts with
  Q-free deck group, e.g. R^n -> T^n), then E contains none of GL_n(Q), SL_n(Q), PGL_n(Q), PSL_n(Q) (n>=2), Aff(Q),
  B_2(Q), U_3(Q). Their unipotent (Q,+) must already embed in the base group E/K. Independent of O4 (no distortion used).
**Needs**: —
**Dead**: T-bar-style lift route to SL_2(Q)/GL_2(Q) (rotation-torsion divisibility absorbed into the central Z) — dead
  for every Q-free base; recorded in root ## Attempts item 1. "Finite presentation of the lifted groups" is moot.
**Sparks**: (1) only covers whose deck group CONTAINS Q escape the lemma, e.g. the adelic solenoid (R x A_f)/Q with
  GL_n(Q) acting linearly on A^n (for gq-solenoid / gq-adelic). (2) circle-level question CLOSED by gq-pp-psl2q at d65ff92ff (`pp-circle-divisible-subgroups-act-freely`,
  `pp-circle-and-lift-hosts-miss-gl-n-q`; root Attempts item 10, 7d64b9412): f.g. piecewise-projective/PL circle
  groups and their lifts miss GL_n(Q), SL_n(Q), Aff(Q), B_2(Q), U_3(Q) with no Q-freeness hypothesis.
