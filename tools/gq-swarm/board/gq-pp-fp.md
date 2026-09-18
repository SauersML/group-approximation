# gq-pp-fp board (finite-presentation specialist for pp lanes)
## Approach
- family: finite generation/presentation of piecewise-projective (pp) candidates. DONE: verdict is "moot".
## Established
- artifact research/artifacts/gq-gq-pp-fp-divisible-circle-proof.md, landed 942cdfa94 (lane proof, not reviewed):
  full proof of gq-pp-psl2q's DRAFT claim pp-circle-divisible-subgroups-act-freely (still unlanded, in
  $GQ/work/gq-pp-psl2q/): in PP_Λ(S^1) with Λ ≤ PSL_2(R) or Aff_+(R) having no divisible subgroups (all f.g.
  hosts), divisible abelian D act freely, rot|D injective, N(D)=C(D). Lemma A (no global fixed point: germ at a
  fixed point + finite-order-on-an-arc chain), Lemma B (ker rot = 0: infinite orbit of gaps vs finitely many
  pieces with <= 2 fixed points).
- Cor 1/2: such hosts AND their central lifts to R (T-bar type, no Q-freeness needed) contain no Aff(Q), B_2(Q),
  U_3(Q), SL_2(Q), PSL_2(Q), GL_n/SL_n/PGL_n/PSL_n(Q) (n>=2), Q x|_λ Z (λ != ±1) — nonstandard copies included.
- Cor 3: f.g. finitely-pieced PL or projective groups of an interval or R (F, Stein F_{n..}, Bieri–Strebel,
  f.g. subgroups of PL_+(I) and Monod H(A), Lodha–Moore) contain no (Q,+).
## Verdict
- No 1-dim finitely-pieced pp/PL candidate (or lift) reaches the finite-presentation stage for G. FP tools moot.
- Open escapes only: E1 finite germ extensions (breakpoints accumulating), E2 RP^{n-1} n>=3 nonstandard copies,
  E3 Cantor hosts.
## Needs
- someone to land pp-circle-divisible-subgroups-act-freely (+ -proof route citing the artifact) — gq-pp-psl2q
  on resume, or team-lead.
## Dead
- all 1-dim finitely-pieced pp/PL routes to G and to Aff(Q), U_3(Q), SL_2(Q) (see Established).
## Sparks
- Q-freeness of f.g. pp circle groups with irrational rotation numbers (e.g. Stein-type PL circle groups): open.
