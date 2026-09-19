---
rg: 2
id: linear-groups-embed-in-elementary-coordinate-groups
kind: claim
title: Every finitely generated linear group embeds in an elementary group over a polynomial coordinate ring, with no Suslin input
distinct_from:
  char-zero-linear-groups-embed-in-polynomial-s-integer-groups: that lands in GL_M of the coordinate ring, and reaching E_N from there needs SL_N = E_N over that ring (Suslin); this lands in E_N directly, using only Gaussian elimination over the field.
  char-p-linear-groups-embed-in-polynomial-f-p-groups: the same difference in characteristic p.
---

**ESTABLISHED (2026-09-19, lane proof, not reviewed)** through
`linear-groups-embed-in-elementary-coordinate-groups-proof`. The proof is in Lean, landed
e5e9cd450a in `GroupApproximation/BooneHigmanLinear/CharZero/` and not yet built.

**Statement.** Let `K` be a field and let `H <= GL_n(K)` be finitely generated.
1. There is a finite set `s ⊆ K` such that `H` embeds in `E_{2n+2}(B)` for every subring
   `B ⊇ s`.
2. If `char K = 0`, then for some `m >= 1` and `k >= 0`, and for every `N` from some bound on,
   `H` embeds in `E_N(Z[1/m][x_1..x_k])`.
3. If `char K = p > 0`, then for some `k >= 1` and every large `N`, `H` embeds in
   `E_N(F_p[x_1..x_k])`.

Lean: `NoSuslin.exists_finset_elementary_embedding` (part 1),
`NoSuslin.charZeroElementaryCoordinates` (part 2, with `N >= k + 5`) and
`NoSuslin.charPElementaryCoordinates` (part 3). The two coordinate theorems are closed
statements, with no hypotheses.

**Why it matters (lesson for general BH).** The linear-host route used to go as follows:
coordinates in `GL_M(R)`, then `diag(g, g^-T, 1)` into `SL_N(R)`, then `SL_N(R) = E_N(R)`. The
last step is Suslin's theorem over a polynomial ring. It is route A's owed input `S1` in the
Lean chain, and a cited theorem in `char-zero-linear-pbh-via-polynomial-self-similar-hosts`.
That step can be done over the field instead, before the coordinate ring is chosen. Then the
choice of the ring absorbs the factorizations. The general mechanism: a condition that holds
over the field, witnessed by finitely many elements, is inherited by every finitely generated
subring containing them. So the coordinate ring should be chosen **last**. With this, T1, T2 and
T3 of the Palomar BH megasubmission need only the K₂ inputs and the envelope
(`NoSuslin.finitelyGeneratedLinearStatement_noSuslin (hP1 hZ1 hH1)`).

No priority is claimed: the observation is elementary. It removes a literature input.
