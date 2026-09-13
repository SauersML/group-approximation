---
rg: 2
id: cayley-traffic-law-refutes-markov-reconstruction
kind: claim
title: The rooted Cayley law of a nonsofic group meets every Cayley-valid traffic constraint exactly and has no finite Markov model
invalidates:
  - hyperlinear-implies-sofic-via-traffic-lift
distinct_from:
  permutation-traffic-is-simultaneous-fixed-points: that computes the graph moments of a finite action and their forced limit values; this evaluates those canonical values on an infinite Cayley graph and shows that matching them exactly, together with positivity, forces no finite model.
  raw-unitary-traffic-gauge-instability: that kills the raw unitary graph polynomial as the extension formula on an exact finite regular table; this kills the downstream reconstruction and realization steps for every positivity notion that Cayley laws satisfy, whatever extension is used.
  markov-sofic-equals-sofic: that rounds finite Markov tables to permutations; this imports it once and is a statement about graph-indexed laws.
  branching-traffic-markov-reconstruction: that is the reconstruction principle; this is its refutation, recorded by refuted_by on that claim.
artifacts:
  - research/artifacts/q34-rounding-routes-2026-09-12.md
---

**Setting.**  Fix a group `G` and a finite window `F` of `G` containing `e`
and closed under inverses.  A test graph is a finite connected directed graph
`T` with edges labelled by `F`.  Its **rooted Cayley law** is

```text
lambda_G(T) = #{ phi : V(T) -> G  with  phi(v_0) = e  and
                 phi(w) = l(e) phi(v) on every edge e : v -> w }.   (CL)
```

The canonical permutation traffic value of `T` at the regular character is
`1` when every cycle word of `T` is trivial in `G` and `0` otherwise.  This is
the forced limit value of `permutation-traffic-is-simultaneous-fixed-points`.

**Theorem.**

1. `lambda_G(T)` does not depend on the root and equals the canonical value
   on every connected test graph.  On a directed cycle with word `w` it is the
   regular trace `1[w = e]`.
2. `lambda_G` satisfies:
   - (P1) values in `[0,1]`, value `1` on the one-vertex graph;
   - (P2) reflection invariance: reverse every edge and relabel `s -> s^{-1}`;
   - (P3) Gram positivity: `sum_{i,j} c_i conj(c_j) lambda_G(T_i o T_j) >= 0`
     for `k`-rooted connected test graphs glued along their roots;
   - (P4) nonnegative injective counts `tau^0`, related to `lambda_G` by
     Möbius inversion over vertex partitions.
3. Let `P` be any class of graph-indexed laws containing `lambda_H` for every
   group `H`, for instance all laws with (P1)–(P4).  Say **RP_G(P)** holds when
   the following is true for every window `F` of `G` and every `eps > 0`.
   There are finitely many test graphs and a `delta > 0` such that every law
   in `P` within `delta` of the canonical values on those graphs yields a
   finite set `X` and doubly stochastic `X x X` matrices `P_g` (`g in F`) with

   ```text
   ||P_g P_h - P_{gh}||_2 < eps   for g, h, gh in F,
   ||P_e - I||_2 < eps,
   |tau(P_g)| < eps               for g != e in F,
   ```

   with `||.||_2` the normalized Frobenius norm and `tau` the normalized trace.
   Then **RP_G(P) holds if and only if `G` is sofic.**
4. Say **RL_G(P)** holds when, for the same data, every law in `P` within
   `delta` of the canonical values is within `eps` of the law of some finite
   action.  The comparison is on the triangle graph of each relation
   `g h = gh` with `g, h, gh in F`, and on the one-loop graph of each
   `g != e` in `F`.  Then RL_G(P) holds if and only if `G` is sofic.

For `G` the group of `finitely-presented-nonsofic-group-exists`, both
principles are false for every such `P`.

## Scope

- Hyperlinearity is never used, and nothing here is conditional on Q3.4.
  The witness may or may not be hyperlinear.
- For sofic `G` both principles hold trivially, since a sofic approximation
  supplies the conclusion without reading the law.  As a reduction they carry
  no information beyond the soficity of the ambient group.  This scoping
  covers amenable, residually finite, linear and every other sofic class.
- The finite state space is essential.  If measure spaces are allowed, the
  Bernoulli shift of any group gives exact measure-preserving kernels with
  fixed-point measure `0`.
- **Finiteness-sensitive positivity.**  The closure `K` of finite-action laws
  is convex, because disjoint unions give rational mixtures.  So
  `lambda_{G_ns}` is separated from `K` by a finite linear inequality valid on
  `K`.
  - Requiring all such inequalities, i.e. "within `delta` of `K` on the tested
    graphs", makes reconstruction trivial.
  - Producing such a law from a microstate is then per-window soficity.  A law
    in `K` near the canonical values on those cycle graphs is a sofic model of
    the window, and conversely.

## Consequences in the graph

- `branching-traffic-markov-reconstruction` is refuted in its stated form.
  There positivity is a relaxation, and the missing theorem was to "identify
  a finite set/hierarchy of branching identities that forces a Markov
  realization".  `lambda_{G_ns}` satisfies every such identity exactly.
  - `markovization-via-branching-traffic` inherits the refutation.
- `hyperlinear-implies-sofic-via-traffic-lift` is invalidated.  Its
  "realizing that law by an actual action" is RL, asserted there without
  argument.  With finiteness-sensitive positivity the repaired premise becomes
  the target, window by window.
- `traffic-branching-rounding-hierarchy` is not refuted.  In its weak reading
  it is witnessed by `lambda_G` for every group, with no microstate, so it says
  nothing.  In its strong reading it is the target.

The proof is `cayley-traffic-law-refutes-markov-reconstruction-proof`.
