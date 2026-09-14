# SK roster G: wave 9, after the restart (~20:20)

The user, after the 20:00 outage: "let's resume swarm. you got this!" / "also do swarm asap".
- All 27 stopped lanes have resumed by raw id.
- Main's note is rev2 (e80dcf20ad). Rev3 is being re-assembled in `sk/drafts/rev3.tex`.
- Decision log: `sk/drafts/rev2-decisions.md`.
- FALSE, never use: diag(a,a^{-1},1) as a homomorphism; the "double swap" γ ↦ (γ,γ^{-1}).
- Queue claims with `sk/queue/sk-verify-7.txt`.

## sk-cstar-simple
Is G_X C*-simple? The criterion is: no nontrivial amenable confined subgroups (Kennedy; Le Boudec–Matte Bon). Read the statements at source first.
- Test subgroups, in order: the locally finite union ⋃ EL_3(A_k); the root subgroups; [[T]]′.
- Background: sk-strong-2 (f0a7a27ee2), open claim `subshift-elementary-groups-are-cstar-simple`, and unique trace (routine, BKKO).
- Either answer is informative.

## sk-sl3z-bandwidth
Does SL_3(Z) lie in no G_X? sk-lef-embedding-d (df468eaeb0, 30de1069dc) proved that every finitely presented subgroup of GL_m(R_X) has banded finite representations, injective on balls, with bandwidth independent of the radius.
- A no for SL_3(Z) comes from dimension-expansion bounds for characteristic-2 modules of SL_3(Z/M).
- A yes suggests a banding construction.
- Open claim: `every-lef-group-embeds-in-a-z-subshift-elementary-group`.

## sk-el2-fq
Simplicity of EL_2(LC(X,F_q)⋊Z) modulo its centre for q > 2 (sk-el2, 3e5a0ff303). This needs the roots e_12(e_C u) and a non-scalar step in rank two. (T) already holds over every F_q.

## sk-cartan-counterexample
Two routes (sk-rigidity-cartan, 99d9f9d236):
- find a ring isomorphism R_X ≅ R_Y between subshifts that are strongly orbit equivalent, not flip conjugate, and of equal complexity growth;
- or prove that every effective groupoid model of R_X is a transformation groupoid, via a continuous Z-cocycle whose kernel is a principal AF subgroupoid.

## sk-labbe-2d
A genuinely two-dimensional obstruction to periodic quantum tilings on fat tori (both axis periods ≥ 4D+2) for Labbé's SFT, or a contextual base module. sk-labbe-matricial (9ba72a8361) settled thin cylinders. One idea: the holonomy of context frames around both cycles.

## sk-k2-recurrent
For an orbit closure X of a recurrent, non-uniformly-recurrent point, with Y a minimal subset: is K_2(3,R_X) → K_2(3,R_Y) onto? sk-k2-subsystems (84039d59fa) has the finite-limit-type case. A yes makes normal subgroups correspond exactly to subsystems there; a no gives a noncongruence normal subgroup.

## sk-measured-subshift
Does every non-amenable sofic group admit a free minimal subshift with an invariant measure and sofic-approximation labellings? sk-sofic-embedding-b (5deaad2389; conditional Theorem SR in its artifact §4) shows this is the missing ingredient for rank-metric envelopes of sofic groups. Read Elek–Lippner at source.

## sk-rev3-referee-a and sk-rev3-referee-b
Two independent referees of rev3 at the Inventiones standard.
- Wait for `sk/drafts/rev3.tex` newer than 20:05 (background loop, 60 s checks), then referee the WHOLE draft line by line:
  - §1 with the density patch and the e_ij(1) generator fix;
  - the operator-algebra paragraph placed after simplicity;
  - §2 LEF groups (lamplighter host, Ore overgroup, diag(u,1,1));
  - the universal host;
  - word problems, questions, credits.
- Label each finding ERROR / GAP / UNCLEAR / FREE STRENGTHENING, with verbatim fixes.
- Land `research/artifacts/sk-rev3-referee-<a|b>-2026-09-13.md`.
- SendMessage main at once on an ERROR. Main lands rev3 only after both referee reports.
- Referee (a) concentrates on correctness. Referee (b) on credit, exposition and whether every claim in the abstract and theorem is proved in the text.
