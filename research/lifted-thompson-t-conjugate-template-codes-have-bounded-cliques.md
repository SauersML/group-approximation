---
rg: 2
id: lifted-thompson-t-conjugate-template-codes-have-bounded-cliques
kind: claim
title: "In T-bar, a bounded-area conjugate-template commutator code has bounded clique number and finitely colourable neighbourhoods; wandering tables die for every choice of words"
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that is the sufficient criterion for killing a mark; this is an obstruction to building its input in T-bar, restricted to conjugate templates.
  bounded-area-commuting-conjugator-localization: that is the group-independent diagram lemma; this is its T-bar consequence for codes.
---

**ESTABLISHED (written proof; not Lean-verified)** by
`lifted-thompson-t-conjugate-templates-bounded-cliques-proof`.

**Setting.**  Fix a finite presentation of `T̄`.  It is finitely presented and
torsion-free, by `lifted-thompson-t-mf-radical-dichotomy`, item 4.

A *conjugate template* is:

- a pair of words `c, h` with mark `x = [c,h] != 1`;
- a graph `G = (V,E)` with an orientation;
- words `u_v`, one for each `v ∈ V`, with
  `c_v = u_v c u_v^(-1)`, `h_v = u_v h u_v^(-1)` and `a_v = u_v`.

(CCC1) of `infinite-chromatic-commutator-code-kills-mf-mark` then holds with
`A_Delta = 0`.  Suppose (CCC2) holds with constant `A_0`: for every oriented
edge `(v,w)`, `Area([c_w, h_v]) <= A_0`.

**Statement.**  There are finite sets `F, F_1 ⊂ T̄`, depending only on
`c`, `h` and `A_0`, such that for every oriented edge `(v,w)`:

```text
C_w := u_w c u_w^(-1) ∈ u_v F u_v^(-1),     H_v := u_v h u_v^(-1) ∈ u_w F_1 u_w^(-1).   (N)
```

Vertices with equal `C` are pairwise non-adjacent, and so are vertices with
equal `H`.  Consequently:

1. every out-neighbourhood is `|F|`-colourable and every in-neighbourhood is
   `|F_1|`-colourable;
2. the clique number satisfies `omega(G) <= 2 min(|F|,|F_1|) + 1`;
3. every wandering table dies, whatever words are used.  Such a table has
   vertex set `Z`, `u_n` any word for `x0^n`, and needs `[c_m, h_n] = 1` for
   all `m != n`, that is, the complete graph.  The same holds for any
   conjugate template on a graph with unbounded cliques, such as complete
   graphs or Morita complete graphs.

**Invariant and death step.**  The code dies at the localization of the
cross commutator.  `bounded-area-commuting-conjugator-localization` puts
`k c k^(-1)`, with `k = u_v^(-1) u_w`, into `<h> (C(h) ∩ B_K)`.  Two
invariants then pin the power of `h`:

- the translation number, which is additive on commuting elements;
- the one-sided slope spectrum `Sigma` at fixed points after rotation
  normalization, on which `h^n t` moves by `n e q`, where `e != 0` is the slope
  exponent of `h` at a boundary point of its support.

**Relation to wave 17.**  The w17 lane (not yet on this branch) proved two
narrower results:

- a central mark `z` escapes every code, by the Milnor–Wood translation
  number;
- the literal shift words `x0^n` give wandering-table area that grows
  linearly, by a bridge count.

This claim covers every non-central mark, and every choice of words for the
table.

**What survives.**  Conjugate templates on infinite-chromatic graphs of
bounded clique number, in which every neighbourhood is finitely colourable.
Shift graphs are the natural candidates: they are line digraphs, which is
exactly the structure (N) allows.  Non-conjugate templates also survive.
`lifted-thompson-t-is-not-mf` stays OPEN.
