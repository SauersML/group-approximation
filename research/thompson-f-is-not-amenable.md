---
rg: 2
id: thompson-f-is-not-amenable
kind: claim
title: Thompson's group F is not amenable
root: true
distinct_from:
  thompson-f-is-amenable: that is the amenable answer to the same named problem; this is the non-amenable answer, which would make F a finitely presented non-amenable group without free subgroups.
---

**OPEN.** Richard Thompson's group `F` is not amenable.

*Marked `root` because it answers a named open problem.* A proof would give a
finitely presented, torsion-free, left-orderable non-amenable group with no free
subgroups (`thompson-f-has-no-free-subgroups`). Survey: V. Guba,
arXiv:2305.07113v4 (2023). The opposite root is `thompson-f-is-amenable`. Source
map: `research/artifacts/thompson-f-amenability-map-2026-09-12.md`.

## Attempts

- **Free subgroups.** Excluded by `thompson-f-has-no-free-subgroups`. A proof
  needs a mechanism other than a free subgroup: a paradoxical decomposition
  without free groups, a uniform isoperimetric inequality, or a non-Ore pair in
  `K[F]`. Dies: no such mechanism is known for `F`.
- **Spectral gaps from property (T).** Excluded: `F` lies in `V`, which has the
  Haagerup property (`thompson-v-has-haagerup-property`), so every Kazhdan
  subgroup of `F` is finite and no Kazhdan-type uniform gap is available. The
  Haagerup property does not obstruct non-amenability either, since free groups
  have it.
- **Numerical cogrowth.** Cogrowth sampling for the standard generators
  (Elder–Rechnitzer–Janse van Rensburg, *Random sampling of trivial words in
  finitely presented groups*, Exp. Math. 24 (2015), arXiv:1312.5722;
  Haagerup–Haagerup–Ramirez-Solano, Int. J. Algebra Comput. 25 (2015)) is
  reported to point toward non-amenability. Elder–Rogers, arXiv:1608.06703,
  "identify two potential sources of error" in that method (abstract). Dies:
  finite data cannot certify an asymptotic growth rate, and this graph has read
  none of the numerical values. That is now a theorem:
  `thompson-f-moment-data-cannot-certify-nonamenability` shows that finitely many
  exact closed-walk counts are always matched by a symmetric measure reaching
  `+-1`. So no finite cogrowth computation, however exact, proves `||P|| < 1`.
  Such data certify only lower bounds on `||P||`, via orthogonal-polynomial zeros
  (`experiments/thompson-f/cogrowth_exact.py`).
- **Non-Ore certificate.** By `thompson-f-amenable-iff-group-ring-is-ore`,
  non-amenability is equivalent to a pair `a, b` in `K[F]` with no nonzero common
  multiple. A finite search can propose candidate pairs, but ruling out every
  multiple needs a structural invariant. Dies: none is known. What is excluded:
  - `(1 - a, 1 - c)` for all `a, c ≠ 1` (`thompson-f-binomial-pairs-have-common-multiples`);
  - `(1 - x_0, b)` for every `b` (`thompson-f-one-minus-x0-is-ore-with-every-element`, Guba
    2022);
  - `(1 - h, b)` for every `b`, when `h` is conjugate to `x_0^{+-1}`, `x_1^{+-1}` or
    `(x_1 x_0^-1)^{+-1}`. That is Guba's Question 3.20, answered here
    (`thompson-f-one-minus-x1-is-ore-with-every-element`).
  - homogeneous degree-one pairs `P_(1,m)` for all `m`, and the degree-two case
    `P_(2,1)` (Guba's survey arXiv:2305.07113, Theorems 3.10, 3.11, 3.14);
  - three-equation systems `Q_3` in linear forms of `x_0, x_1, x_2` (survey Corollary
    3.13).

  Open candidates named in the survey: the degree-two case `P_(2,2)` and the
  four-equation system `Q_4`. A witness must also avoid `1 - h` for `h` in those
  conjugacy classes. Map: `research/artifacts/thompson-f-certificate-shapes-2026-09-12.md`.
- **Evacuation schemes and bounded flows.** Non-amenability is equivalent to a flow on
  the Cayley graph with bounded values and inflow at least `epsilon` everywhere, or an
  evacuation scheme in which each edge is used at most `C` times. This is survey
  Propositions 1.3 and 2.3, and by Proposition 2.4 (König) it can be checked on finite
  fragments. Dies for `C = 1`: the Cheeger constant of `F` is below 1 for
  `{x_0, x_1, x_1 x_0^-1}` and for `{x_0, x_1, x_2}` (survey Theorems 2.5, 2.6, 2.8). Open
  for `C >= 2`.
- **Unaccepted claims.** arXiv:1408.2188 claims non-amenability, and Shavgulidze's
  papers claim amenability (critiqued in arXiv:1102.0747). Neither is an accepted
  result. They are recorded so that no lane cites them as theorems.
