---
rg: 2
id: sl3-z-inverse-3-is-flexibly-p-stable
kind: claim
title: The S-arithmetic group SL3(Z[1/3]) is flexibly permutation stable
artifacts:
  - research/artifacts/wreath-permutation-collapse-2026-08-22.md
distinct_from:
  iwahori-local-global-defect-question: that is the Dogon-Vigdorovich flexible HILBERT-SCHMIDT stability question for SL_2(Z[1/2]); this is its PERMUTATION sibling at SL_3 - Hamming metric, symmetric groups - feeding the wreath nonsoficity collapse rather than the HNN non-hyperlinearity theorem.
  sl2-z-inverse-pq-is-hs-stable: that is an HS-stability hole for an SL_2 pair; this is permutation-category stability of the SL_3 S-arithmetic group, where the Becker-Lubotzky (tau)-obstruction kills the strict form and only the flexible form is at stake.
---

Claim (OPEN): `Gamma = SL_3(Z[1/3])` is flexibly P-stable: every
asymptotically-multiplicative (normalized Hamming) sequence
`sigma_n : Gamma -> Sym(V_n)` is asymptotically close to genuine
actions `tau_n` on sets `V_n' supseteq V_n` with
`|V_n' \ V_n| / |V_n| -> 0`.

Status and stakes.  STRICT P-stability is FALSE: Becker–Lubotzky
(arXiv:1809.00632) — an infinite residually finite group with property
(tau) is never P-stable — applies.  The flexible form is open and is
the permutation sibling of the Dogon–Vigdorovich HS-stability question
that runs the Iwahori lane.  If TRUE, then by
`wreath-nonsofic-from-flexible-p-stability` the summit wreath `W_3` is
NOT sofic, and (with `coset-wreath-is-hyperlinear`) the separation
root closes; Bowen–Burton (arXiv:1906.02172) already tie flexible
stability of higher-rank lattices to nonsoficity, so a proof would be
a landmark either way.  If FALSE, `Gamma` has essentially
non-correctable almost-actions — new exotic permutation models beyond
the congruence ones, the Hamming shadow of the outlier sector.

## Attempts

- **IRS heuristic (for).**  Becker–Lubotzky–Thom (arXiv:1801.08381)
  characterize P-stability for amenable groups via co-sofic invariant
  random subgroups, and with (T) the flexible form follows from
  co-sofic IRS rigidity in the cases where the criterion applies.
  Stuck–Zimmer gives total IRS rigidity for higher-rank lattices
  (every ergodic p.m.p. IRS is finite-index or central), and CSP makes
  finite-index IRSs congruence — the IRS side is as rigid as it could
  possibly be.  The gap: the BLT machinery converts IRS data to
  stability only through amenability or additional structure; for
  non-amenable (T) groups the conversion of an almost-action's local
  statistics into an invariant random subgroup loses the
  almost-multiplicativity control.  Making the Stuck–Zimmer rigidity
  bite on almost-actions rather than actions is exactly the open
  content.  Note the statistics side is COMPLETE: every
  Benjamini–Schramm limit of almost-actions of `Gamma` is an invariant
  random Schreier structure, classified (Nevo–Stuck–Zimmer type IRS
  rigidity for higher-rank S-arithmetic groups) as mixtures of
  congruence coset statistics and the free part — and both are
  realized by genuine deep-congruence actions (injectivity radius of
  congruence quotients tends to infinity, so deep levels realize the
  free statistics).  So the hole's entire content is the gap between
  matching STATISTICS and matching in HAMMING (pointwise correction),
  the same gap as everywhere in the program.
- **Two-sided warning.**  A flexible P-stability proof for `Gamma`
  would, via Bowen–Burton-type arguments and the wreath collapse,
  produce nonsofic groups; skepticism is warranted exactly to the
  degree one believes nonsofic groups should not come this cheaply.
  Conversely the known nonsofic groups (Kun–Thom) arrived without any
  stability input, so there is no meta-obstruction; the question is
  genuinely open, and the wreath collapse gives its resolution a
  second consumer.
