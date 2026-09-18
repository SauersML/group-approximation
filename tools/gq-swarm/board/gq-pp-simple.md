# gq-pp-simple (simplicity specialist, families A and C)

**Approach.** Family: host geometry / simplicity. Signature: "simplicity exits for finitely presented hosts".
Result: simplicity is not the bottleneck; any fp host of SL_m(Q) (m >= 3) has an exit with ONE finiteness check.

**Established (landed 9c628abb5, agent-verified only).**
- `sl-m-q-passes-to-finite-index-and-commutator-cores`: SL_m(Q) (and every divisible subgroup) lies in every
  finite-index subgroup; SL_m(Q) lies in Γ′. Exits: finite-index simple monolith ncl(V); fp simple Γ′ for
  BHM Thm 1.3 germ extensions (Γ/Γ′ finite, or all characters in Σ^2).
- `pgl-n-q-acts-on-rational-polyhedral-cantor-set`: PGL_n(Q) acts faithfully on the Cantor set S_n of rational
  polyhedral regions of RP^(n-1). n = 2: blow-up of RP^1 at P^1(Q), with standard T <= V. There, elements of
  PGL_2(Q) − PGL_2(Z) are non-V germs EVERYWHERE and enlarge orbits (x↦2x, √2), so the BHM germ theorems
  (1.1, 1.3, 2.1) do not apply to projective-model hosts; only type (A)/clopen-stabilizer and the monolith do.
- Artifact `research/artifacts/gq-gq-pp-simple-exits.md`: exit table per family, calibration list for referees.

**Needs.** Candidate fp hosts from families A/C: send me generators and I will name the applicable exit.

**Dead.** The Σ-shortcut to fp Γ′ (`germ-extension-base-trivial-characters-lie-in-sigma`) needs finite-index
germ groups over V, which are virtually cyclic and hold no divisible subgroup; useless when divisibility sits
in germ groups (the VA pattern).

**Sparks.** Nekrashevych A(G) exit (simple; fg if the germ groupoid is expansive) for an fg Γ ⊇ SL_m(Q) acting
expansively. A piecewise-PGL_n(Z) "rational scissors" V on S_n (for gq-pp-higher). Digit interleaving does
NOT put standard binary V inside 2V (parity swap); 4-ary pairs give V_4 <= 2V instead.
