---
rg: 2
id: finitely-generated-linear-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated linear group over any field embeds in a finitely presented simple group
distinct_from:
  char-zero-linear-groups-satisfy-boone-higman: that is characteristic zero only; this is the union over all characteristics, stated once.
  char-p-linear-groups-satisfy-permutational-boone-higman: that is positive characteristic only, in the stronger permutational form; this is the plain property in every characteristic.
  positive-char-linear-groups-satisfy-boone-higman: that is positive characteristic through Leavitt projective elementary hosts, which rest on an unrefereed preprint and on Farrell--Jones imports; this uses the self-similar route in positive characteristic instead.
  gl-n-q-embeds-in-fp-simple-group: that is GL_n(Q) itself, which is not finitely generated and is not covered here; it is BBMZ Problem 5.3(5) literally and stays OPEN.
---

**ESTABLISHED** by `finitely-generated-linear-groups-satisfy-boone-higman-proof`. It
only composes two claims already on main, both independently reviewed. No novelty is
claimed.

**Statement.** Let `K` be any field and let `H <= GL_n(K)` be finitely generated.
Then `H` embeds in a finitely presented simple group. So every finitely generated
linear group satisfies the Boone--Higman conjecture.

**The two halves.**
- **Characteristic zero:** `char-zero-linear-groups-satisfy-boone-higman`, reviewed by
  lane `bh-poly-linear-review` (2026-09-12).
- **Characteristic `p > 0`:** `char-p-linear-groups-satisfy-permutational-boone-higman`.
  It puts `H` in the finitely presented self-similar group `R^N x| E_N(R)` with
  `R = F_p[s_1..s_k]`. Its route and new nodes PASS in
  `research/artifacts/review-metabelian-bh-2026-09-13.md` (items 2–4). Zaremsky's
  Theorem 1.1 (`fp-self-similar-groups-embed-in-fp-simple-groups`) then gives the
  finitely presented simple envelope.

**Which named problem.** The Belk--Bleak--Matucci--Zaremsky survey
(arXiv:2306.16356v3, Problem 5.3) has no item for all finitely generated linear
groups. Its item (5) asks for `GL_n(Q)` itself, which this does not reach. The
nearest printed statement is Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, which
lists "Q-linear groups" as known (quoted in
`char-zero-linear-groups-satisfy-permutational-boone-higman`). The novelty searches
behind the two halves were bounded
(`research/artifacts/review-bh-polynomial-linear-2026-09-12.md`,
`research/artifacts/bh-quasi-linear-pbh-2026-09-13.md`). Nobody has done a
MathSciNet search.

**Trust surface.** Everything is either elementary or read at source, except the
following.
- **Zaremsky, arXiv:2405.09722, Theorems 1.1 and 1.2.** Read from the arXiv text.
- **Standard commutative algebra and K-theory.** Stacks tags; Quillen, Invent. Math.
  36 (1976), Theorem 4; Weibel, *K-book* III 1.2.5, 5.5.2, 6.1.1 and V 6.3. All were
  read at source by the lanes that cite them.
- **Rehmann--Soulé and Borel--Serre** in the characteristic-zero elementary-group
  step. These are recorded in `elementary-groups-over-polynomial-s-integers-are-fp-proof`.
- **Krstić--McCool is not needed.** Both elementary-group nodes import finite
  presentation of `St_n` from Krstić--McCool, whose primary text is unread. But both
  consuming routes use `n >= k+4 >= 5` with `k >= 1`, where the refereed
  `steinberg-groups-of-fp-rings-are-fp-in-rank-five` gives the same conclusion. The
  trust notes on the two elementary nodes record this. For `k = 0` the groups are
  covered by Zaremsky's rational theorem in characteristic zero, and by finite groups
  inside `GL_M(F_p[s_1])` in characteristic `p`.
- **Not used:** the Leavitt-tensor hosts of
  `positive-char-linear-groups-satisfy-boone-higman`, with their Khanh and
  Farrell--Jones imports.

**Stronger form, not claimed here.** In characteristic `p` the groups are in the
permutational class `B_A`, by the reviewed node above. In characteristic zero that
is `char-zero-linear-groups-satisfy-permutational-boone-higman`, whose last input is
marked not independently reviewed. So the uniform permutational statement waits on
that review.
