---
rg: 2
id: lamp-commutator-coset-closure-subgroup-membership-proof
kind: route
title: Proof that the reversed commutator lamp enters the coset-parity closure exactly when two subgroup memberships hold
target: lamp-commutator-coset-closure-is-subgroup-membership
requires:
  - residually-permutational-lamp-extensions-are-surjunctive
artifacts:
  - research/artifacts/lamp-commutator-coset-closure-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Artifact `lamp-commutator-coset-closure-2026-09-12.md`, Sections 0--2. Corrected forward after
w3-vf-nonlinear Section 21: the first version wrongly said pairing (P_b) below forces
`pi_S(w) = 0`, and it omitted the second condition of pairing (P_a).

**Step 1 (the two closures sandwich).** Coset projections `pi_S` (`S >= Gamma`) are permutation
maps into `F_2[G/S]`, so the coset-parity closure `U^c` is an intersection over a sub-family of the
maps defining the permutation closure `U-bar`. Fewer maps give a larger common kernel:
`U <= U-bar <= U^c`. (Section 0; Lemma 0.1 derives `U = U^c => W/U` surjunctive from
`residually-permutational-lamp-extensions-are-surjunctive`.)

**Step 2 (the four-coset computation).** For `S >= Gamma`, `pi_S(U) = 0` iff `pi_S(v) = 0` by
`G`-equivariance and cyclicity of `U`. Here
`pi_S(v) = e_S + e_(aS) + e_(bS) + e_(abS)` and
`pi_S(w) = e_S + e_(bS) + e_(aS) + e_(baS)`.
`pi_S(v) = 0` iff the four cosets cancel in pairs, that is, iff one of three pairings holds:
- **(P_a)** `S = aS`, `bS = abS`: `a in S` and `b^-1 a b in S`. Then `aS = S` and `baS = bS`, so
  `pi_S(w) = 0`.
- **(P_b)** `S = bS`, `aS = abS`: `b in S`. Then `pi_S(w) = e_(aS) + e_(baS)`, which is zero iff
  `a^-1 b a in S`.
- **(P_ab)** `S = abS`, `aS = bS`: `ab in S` and `a^-1 b in S`. Then `pi_S(w) = e_S + e_(baS)`, and
  `ba = (ab) m` with `ab in S` gives `baS = S` iff `m in S`.
Coincidences of three or four cosets are sub-cases where several pairings hold. The formulas above
use only each pairing's own conditions, so they stay valid there.

**Step 3 (the iff).** `w in U^c` iff `pi_S(w) = 0` for every `S >= Gamma` satisfying some pairing.
(P_a) never obstructs. The subgroups satisfying (P_b) are exactly those containing `S_1 = <Gamma, b>`,
and every one of them contains `a^-1 b a` iff `S_1` does. The subgroups satisfying (P_ab) are
exactly those containing `S_0 = <Gamma, ab, a^-1 b>`, and every one contains `m` iff `S_0` does.
So `w in U^c <=> (m in S_0 and a^-1 b a in S_1)`. With Step 1, failure of either membership gives
`w notin U-bar`. The S_3 example (`a=(12)`, `b=(13)`, `S = <b>`) shows the second condition cannot
be dropped.

**Step 4 (free generators).** Stallings folding of `H = <ab, a^-1 b>` in `F(a,b)` yields two
vertices `*, u`, `a`-edges `* -> u`, `u -> *`, one `b`-edge `u -> *`. Reading
`m = b^-1 a^-1 b a` from `*` fails at the final `b` (no outgoing `b`-edge at `*`), so `m notin H`.
Also `a^-1 b a notin <b>` (reduced, not a power of `b`). Choosing `a, b in N = EL_r(R)` inside a free
subgroup with `<a,b> cap S_0 = <ab, a^-1 b>` gives `m notin S_0`, hence `w notin U-bar`.

No compute was run.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS on the corrected statement (297ace12af).**
- **First version wrong.** It claimed "`w in U^c` iff `m in S_0`", which is false: pairing (P_b) needs
  `a^-1 b a in S`, and `S_3` with `S = <(13)>` breaks it.
- **Corrected version checked.**
  - Three pairings.
  - Minimal subgroups `S_1` and `S_0`.
  - (P_a) never obstructs.
  - Stallings fold of `<ab, a^-1 b>`.
- **Hypothesis.** The free-subgroup intersection is correctly left as a hypothesis.
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 21.)
