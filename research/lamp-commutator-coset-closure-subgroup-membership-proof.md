---
rg: 2
id: lamp-commutator-coset-closure-subgroup-membership-proof
kind: route
title: Proof that the reversed commutator lamp enters the coset-parity closure exactly when the commutator lies in the generated subgroup
target: lamp-commutator-coset-closure-is-subgroup-membership
requires:
  - residually-permutational-lamp-extensions-are-surjunctive
artifacts:
  - research/artifacts/lamp-commutator-coset-closure-2026-09-12.md
---

Artifact `lamp-commutator-coset-closure-2026-09-12.md`, Sections 0--2.

**Step 1 (the two closures sandwich).** Coset projections `pi_S` (`S >= Gamma`) are permutation
maps into `F_2[G/S]`, so the coset-parity closure `U^c` is an intersection over a sub-family of the
maps defining the permutation closure `U-bar`. Fewer maps give a larger common kernel:
`U <= U-bar <= U^c`. (Section 0; Lemma 0.1 derives `U = U^c => W/U` surjunctive from
`residually-permutational-lamp-extensions-are-surjunctive`.)

**Step 2 (the four-coset computation).** For `S >= Gamma`, `pi_S(U) = 0` iff `pi_S(v) = 0` by
`G`-equivariance and cyclicity of `U`. With
`pi_S(v) = e_S + e_(aS) + e_(bS) + e_(abS)` and
`pi_S(w) = e_S + e_(aS) + e_(bS) + e_(baS)`, vanishing of `pi_S(v)` forces one of: (I) `ab in S` and
`a^-1 b in S`; (II) `a in S`; (III) `b in S`. Cases II, III give `pi_S(w) = 0` by the same
coincidences. Case I gives `pi_S(w) = e_S + e_(baS)`, and `ba = (ab) m` with `ab in S` makes
`baS = S` iff `m in S`.

**Step 3 (the iff).** If `m notin S_0 = <Gamma, ab, a^-1 b>`, then `S = S_0` is type I with
`pi_(S_0)(v) = 0` and `pi_(S_0)(w) != 0`, so `w notin U^c`. If `m in S_0`, every `S` with
`pi_S(v) = 0` is type I, II or III; type I forces `S >= S_0 ni m`, so `pi_S(w) = 0` in all cases and
`w in U^c`. Hence `w in U^c <=> m in S_0`. With Step 1, `m notin S_0 => w notin U-bar`.

**Step 4 (free generators).** Stallings folding of `H = <ab, a^-1 b>` in `F(a,b)` yields two
vertices `*, u`, `a`-edges `* -> u`, `u -> *`, one `b`-edge `u -> *`. Reading
`m = b^-1 a^-1 b a` from `*` fails at the final `b` (no outgoing `b`-edge at `*`), so `m notin H`.
Choosing `a, b in N = EL_r(R)` inside a free subgroup with `<a,b> cap S_0 = <ab, a^-1 b>` gives
`m notin S_0`, hence `w notin U-bar`.

No compute was run.
