---
rg: 2
id: kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf
kind: claim
title: Kazhdan groups acting by bounded piecewise translations of an essentially free amenable measure-preserving action have almost all orbits finite
distinct_from:
  elek-monod-near-hit-has-torsion-no-kazhdan-subgroup: That excludes infinite Kazhdan subgroups of one Z^2 full group through Juschenko--de la Salle's wobbling theorem, which needs subexponential growth of the acting group; this holds for every amenable acting group, including exponential growth, and uses the invariant measure instead of growth.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: That treats Rover--Nekrashevych hosts through commensurated subsets and self-similarity; this treats measure-preserving amenable orbit full groups through almost invariant vectors.
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: That is the coset-space statement for a single subgroup; this is the orbit-relation statement for a whole measure-preserving action, where stabilizers vary from point to point.
---

**ESTABLISHED.**

**Setting** (as in `amenable-orbit-full-group-subgroups-are-sofic`).
- `Lambda` is a countable amenable group acting essentially freely by
  measure-preserving Borel automorphisms on a standard probability space
  `(X, mu)`.
- `W(Lambda ~ X)` is the group of Borel bijections `g` of `X` with
  `g(x) = c_g(x) x` for a Borel `c_g : X -> Lambda` of finite range.

**Theorem.** Let `Gamma` have property (T) and let `rho : Gamma -> W(Lambda ~ X)`
be a homomorphism. Then `mu`-almost every point has a finite `rho(Gamma)`-orbit.

**Consequences.**
1. If `mu(Fix rho(g)) < 1` for every `g != 1`, then `Gamma` is residually finite.
2. If `Gamma` is infinite and simple, `rho(Gamma)` acts trivially almost everywhere.
3. **Topological version.** If `X` is compact, the action is continuous, and
   `mu` has full support, then every Kazhdan subgroup of `[[Lambda ~ X]]` is
   residually finite, and no infinite simple Kazhdan group embeds in
   `[[Lambda ~ X]]`.

**What it says for the finitely presented simple question.** The soficity
certificate `amenable-orbit-full-group-subgroups-are-sofic` cannot reach any
infinite simple Kazhdan group. That removes, as candidates for
`fp-simple-group-in-amenable-orbit-full-group`, the Kazhdan Kac--Moody lattices
of `simple-kazhdan-kac-moody-lattices-exist` and the Titz Mite--Witzel kernels of
`titz-witzel-simple-kazhdan-cat0-lattices-exist`. It says nothing about their
soficity by other means.

**Necessity of (T).** `Lambda` itself embeds in `W(Lambda ~ X)` with `c_lambda`
constant, and its orbits are infinite. So the theorem fails for amenable
groups, as it must.

**Credit.** No novelty is claimed. The theorem is a corollary of two classical
facts: property (T) makes every ergodic measure-preserving action strongly
ergodic (Connes--Weiss 1980; K. Schmidt, Ergodic Theory Dynam. Systems 1, 1981),
while an ergodic diffuse hyperfinite relation is never strongly ergodic, and the
orbit relation here sits inside the hyperfinite relation of `Lambda`
(Ornstein--Weiss). Theorem numbers in those sources were not re-read. The route
gives a direct Hilbert-space proof that avoids ergodic decomposition and
hyperfiniteness; the credit was flagged by the ex-novelty lane in
`research/artifacts/ex-open-status-2026-09-12.md`.

Proof: `kazhdan-subgroups-amenable-orbit-full-groups-rf-proof`.
