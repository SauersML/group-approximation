---
rg: 2
id: dkkms-grassmann-2to1-test-is-locally-99-percent-rigid
kind: claim
title: Every labelling of the DKKMS multi-edge 2-to-1 game of value close to 1 agrees on almost all constraint mass with the locally honest patchwork of some outer labelling of value 15/16 and dirt 1/64
distinct_from:
  high-advantage-selector-witnesses-decode-good-outer-labellings: that proves that near-honest selector witnesses decode; this is the rigidity statement that would make every near-1 selector witness near-honest, and it concerns the plain 2-to-1 game with no orientation.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies the list-decoding hypotheses (E) and (M=) for honest encodings of global assignments; this asks for a structure theorem about arbitrary labellings of value near 1.
  two-to-two-games-theorem: that is the 1 percent soundness statement of Khot--Minzer--Safra, which decodes labellings of value delta to a list; this is a 99 percent statement asking for agreement on all but zeta_1 of the mass with one patchwork, with explicit constant outer value 15/16.
  efficient-branch-selector-on-proved-2to1-instances: that asks for a polynomial-time orientation with YES lift value near 1; by Corollary B of the high-advantage node, this claim together with that one gives NP in RP.
---

**OPEN.**

*Setting.* The notation is that of
`high-advantage-selector-witnesses-decode-good-outer-labellings`. `G_multi` is
the unfolded DKKMS 2-to-1 game on a regular 3LIN input: one copy per member
`(U,L)` of each folding class `C` and each B-vertex `(V,L')` with `L' < L`.
`Phi_k` is its outer k-tuple game. `hon_kappa(lambda)` is the patchwork of an
outer labelling `lambda`, read at canonical members `kappa(C)`, and
`d_kappa(lambda)` is its dirt.

*Statement.* There are absolute constants `eta_1, zeta_1 <= 1/128` and `l_0`
such that the following holds for all `l >= l_0` and all `k` admissible for
Corollary A (`2^(l-1-2k) <= 1/16`, `eps_k <= p0^2/4`). On every 3LIN input,
every labelling `(A, sigma')` of `G_multi` with value `>= 1 - eta_1` agrees,
outside constraint mass `zeta_1`, with `hon_kappa(lambda)` for some outer
labelling `lambda` with

```text
val_(Phi_k)(lambda) >= 15/16      and      d_kappa(lambda) <= 1/64.
```

**Why this is a genuine prerequisite.**

* **Consequence.** By Corollary B of the high-advantage node, this claim and
  `efficient-branch-selector-on-proved-2to1-instances` together give `NP in RP`.
  So under `NP not in RP`, at least one of the two fails. If this claim holds,
  the selector route to UGC through the proved instances is closed.
* **Can fail on its own.** The claim uses no orientation and no complexity
  assumption, so it is a combinatorial statement about one test. It fails if
  some near-1 labelling is `zeta_1`-far from every patchwork of every good outer
  labelling. The selector hole says nothing about that.
* **Weaker than global rigidity, on purpose.** Agreement with `hon(a)` for one
  global assignment `a` is false at rate `Omega(beta)`, where `beta` is the
  fraction of k-tuples that can be relabelled consistently. Dictator patchworks,
  which use different satisfying assignments on different k-tuples, are
  heuristic evidence for this. They are locally honest, so they satisfy this
  claim by construction.

**Evidence for.**

* Each k-tuple `U` is tested only through moves `U -> V -> U'` and through
  `L' = L meet X_V`. So near-1 value forces per-`U` consistency on most of the
  Grassmannian of `U`. That is the regime of the known 99 percent agreement
  theorems for Grassmann tests.
* Folding makes the unfolded label `lambda_U` satisfy the equations of `U`
  automatically. So an outer labelling read off per `U` is honest for `Phi_k` on
  most tuples.

**Evidence against, or difficulty.**

* Folding classes span several `U`. A class label is read at one
  representative, so the patchwork can pay dirt wherever the members disagree.
  The claim needs this dirt to be `<= 1/64` for some choice of `kappa` and
  `lambda`.
* Zoom-in and zoom-out sets of the Grassmann test have measure about `2^(-l)`.
  Near-1 structure theorems that go through them may lose factors of `2^l` in
  `zeta_1`. The claim needs `zeta_1` to be absolute.
* Nothing recorded yet proves any 99 percent statement for the folded 2-to-1
  test at constant `eta_1` uniformly in `l`.

## Attempts

* **Global rigidity (2026-09-18).** The first formulation asked for agreement
  with `hon(a)` for one global assignment. Dictator patchworks suggest that it
  fails at rate `beta`. It was replaced by the local statement above, which
  Theorem 3 of the high-advantage node can use because it decodes any outer
  labelling of value `>= 15/16`, with no global gluing. Not a proof of either
  form.
