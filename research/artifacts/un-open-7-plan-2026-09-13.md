# un-open-7 plan: the coarse geometry of the UN ladder

Lane `un-open-7`, 2026-09-13. Open-ended lane, lens: geometry and rigidity. This plan is
the required first landing; the mathematics follows in later landings.

## Target

The UN ladder is currently a **ring-theoretic** dichotomy: paradox versus measure decides the
matricial approximation type of `EL_n(A_k(𝒢))`. I take the **coarse/geometric** face of the same
ladder, in three steps.

**(1) The RF/MF gap.** For every rung, `S = EL_n(A_k(𝒢))/Z` is infinite and simple
(`steinberg-elementary-groups-are-simple-mod-centre`, reviewed PASS). Simplicity alone already
kills every homomorphism to a residually finite group, on *both* sides, for free. What the
dynamics decides is only the weaker approximation notion: the measure side is LEF, hence MF;
the paradox side kills every homomorphism to an MF group. So the whole dichotomy lives exactly
in the gap between RF-rigidity (free, from simplicity) and MF-rigidity (paid for by paradox).
This is the conceptual point of the lane and it costs nothing to state correctly.

**(2) Coarse separation.** Finite presentability is a quasi-isometry invariant of finitely
generated groups. On the measure side `S` is LEF and infinite simple, so by Vershik–Gordon it is
**never finitely presented**. The paradox side does contain finitely presented examples (the
non-MF paper's finitely presented torsion-free Kazhdan group with no MF quotient; and the
Steinberg-cover machinery of `steinberg-finite-presentation-and-kazhdan-theorem`). Hence the two
ends of the ladder are separated by a **coarse** invariant, not merely by an operator-algebraic
one: no measure-side group is quasi-isometric to a finitely presented paradox-side group. That is
the geometric explanation the brief asks for.

**(3) A quantitative invariant: LEF growth.** For the measure side define
`F_S(r) = min{ |H| : H finite and the r-ball of S embeds ball-injectively into H }`,
an isomorphism invariant up to rescaling `r -> Cr`. The Pestov construction models the `r`-ball by
a Kakutani–Rokhlin tower of height `N(r)`, giving `F_S(r) <= |EL_{nN(r)}(F_q)|`, so the LEF growth
is controlled by the **return-time function of the subshift**. Upper bound: provable from the
existing tower construction. Lower bound: the crux, landed as an open claim with Attempts. A lower
bound would give a continuum of pairwise non-isomorphic infinite simple Kazhdan LEF groups indexed
by the dynamics, refining Pestov 9.1 from "one exists" to "the dynamics is visible in the group".

## Why this matters

- It turns the ladder from a statement about rings into a statement about the **coarse type** of
  the groups, which is what "geometric explanation" has to mean.
- (2) gives a separation that survives every abstract group isomorphism and every quasi-isometry.
- (3) proposes the first invariant that could distinguish measure-side groups **from each other**,
  which nothing in the program currently does.

## What this does not duplicate

- `un-simplicity` (done, reviewed): simplicity of the groups. I consume it, I do not reprove it.
- `un-paradox`, `un-middle`, `un-tarski`, `un-converse`: the ring-level paradox/measure dichotomy
  and its thresholds. I consume their statements; I add no ring-level arrow.
- `un-traces`: traces and corona traces. Disjoint; my invariants are coarse, not operator-algebraic.
- `un-k1-homology`: `K_1` and groupoid homology of the unit groups. Disjoint.
- `un-full-groups-bridge`: topological full groups versus elementary groups. Disjoint; I work only
  with `EL_n`.
- `un-stability-nonsofic`: permutation stability. Disjoint, though (1) is a useful adjacent fact
  for that lane, since stability arguments also run through residual finiteness.
- `un-low-rank-band`, `un-boundary-families`, `un-reduced-cstar`, `un-hyperlinear-paradox`,
  `un-sofic-not-lef`, `un-labbe-ring`, `un-rf-beyond-free`: all ring- or operator-side.
- Repo precedent to build on, not redo: `cohn-elementary-group-is-not-lef` already runs the
  finitely-presented-Steinberg-cover argument for the Cohn and Jacobson algebras. My (2) is the
  same mechanism read as a coarse invariant and applied across the ladder.

## Order of work

1. This plan.
2. The RF/MF gap node plus the uniform rigidity package (property FA, FH, no finite-dimensional
   linear representation over any field, no nontrivial homomorphism to an RF group).
3. The coarse separation theorem, with the Vershik–Gordon import quoted verbatim.
4. LEF growth: definition, the upper bound, and the open lower bound with Attempts.
