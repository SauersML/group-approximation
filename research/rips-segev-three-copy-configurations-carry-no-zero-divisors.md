---
rg: 2
id: rips-segev-three-copy-configurations-carry-no-zero-divisors
kind: claim
title: In Steenbock's Rips--Segev core no relation alpha (u(a) + w(a) b) = 0 with alpha, w != 0 has alpha u and alpha w supported on the union of three translates of g(V(Gamma)), because two active cosets whose port supports add injectively force u = c w, so each copy has at most one clean active line and at most 12 active cosets close a positive relation of length at most 24
distinct_from:
  rips-segev-two-copy-configurations-carry-no-zero-divisors: that handles two translates and leaves three translates open at a mixed-flank lemma; this handles three translates by a rank-one argument on port tensors, which makes the flank analysis (and the mixed-flank lemma) unnecessary for every number of copies.
  rips-segev-one-copy-configurations-carry-no-zero-divisors: that handles one translate by row separation and forbidden x_1/x_2 targets; the rank-one lemma here re-proves it in one step (two active lines in one copy already force u = c w).
  rips-segev-core-large-gap-two-layer-elements-are-regular: that uses only the extreme degrees of the ports; this uses the full coefficient tensors P_T (x) Q_T' of two cosets.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this settles the two-layer relations inside three translates and reduces N >= 4 translates to a shell lemma with an exact residue.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-three-copy-no-zero-divisors-proof`.

**Setting.**  As in `rips-segev-two-copy-configurations-carry-no-zero-divisors`: `Gamma` is Steenbock's graph with
`Gr'_*(1/8)` and `gamma >= 42`.  `K` is its core, `G = G_1 *_{<a>} K *_{<b>} G_2`, and `g : V(Gamma) -> K`.  A *copy*
is `h g(Gamma)`, with vertex set `V_h = h g(V(Gamma))`.  For `alpha (u + w b) = 0`, the *port pair* of a left
`<a>`-coset `T = z_T <a>` is `P_T = f_T u`, `Q_T = f_T w` in `k[t^{±1}]`, where `alpha_T = z_T f_T(a)`.

**Rank-one lemma (any field, any group containing `<a>` and `b`).**  Let `alpha (u + w b) = 0` with
`alpha, w != 0`.  Suppose two active cosets `T`, `T'` have port supports `S_T`, `S_T'` (the supports of `P`, `Q`
together, relative to base points) with `(S_T - S_T) ∩ (S_T' - S_T') = {0}`.  Then `u = c w` for a scalar `c`, and
hence `alpha = 0`, a contradiction.
- Why: coefficientwise, `P_T Q_T' = P_T' Q_T` reads `P_T(x) Q_T'(y) = Q_T(x) P_T'(y)`.  So `P_T` is a scalar
  multiple of `Q_T`, which gives `u = c w`.
- Then `(alpha w)(c + b) = 0`, so the finite set `supp(alpha w)` is invariant under right multiplication by `b`.

**Theorem.**  Let `k` be a field, `u, w in k[<a>]`, and `alpha in k[K]`, with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then there are no `h_1, h_2, h_3 in K` with
`supp(alpha u) ∪ supp(alpha w) ⊆ V_{h_1} ∪ V_{h_2} ∪ V_{h_3}`.  The same holds in `k[G]`, with `h_m in G`.

**Consequences for every number `N` of copies.**
- A copy has at most one clean active coset (one that meets no other copy and holds no bridge endpoint).
- All clean active cosets carry the same line index of `Gamma`.
- Every port neighbour of a clean active coset is dirty.
- The `N`-copy theorem holds whenever `3N^2 - N < 5 gamma/8 - 1`, so every fixed `N` is covered for large girth.

**Toward `N >= 4` (shell lemma, proved).**  Every directed port cycle is a positive relation, and a minimal van
Kampen diagram for it has a shell face in some copy `C_M`.
- The shell's exterior arc runs through at least 11 consecutive active cosets on distinct lines of `C_M`.
- At most one of them is *pure*, meaning its port support lies in the distinguished positions of its `C_M`-line.
  This is the rank-one lemma again.
- Each impure one carries a link (shared coset or bridge) from `C_M` to another covering copy.  One other copy
  accounts for at most 3 of them.
- **So for `N = 4` a counterexample needs every shell copy of every port cycle to lie outside the covering.**  In
  that case every interior arc coset with nonzero `a`-exponent is dirty for the covering, too.

**Scope.**  The general `N` case is the whole `b`-degree-one case of
`rips-segev-groups-satisfy-kaplansky-zero-divisor`.  It stays open.  Counting cannot finish it, since both
endings grow with `N`.  What is needed is an extremal-copy argument: a copy of the covering that meets the others
in few pieces.
