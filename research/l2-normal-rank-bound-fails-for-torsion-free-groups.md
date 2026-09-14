---
rg: 2
id: l2-normal-rank-bound-fails-for-torsion-free-groups
kind: claim
title: The first l2-Betti normal-rank bound fails for countable torsion-free groups
distinct_from:
  torsion-breaks-l2-normal-rank-bound: that records the failure in the presence of torsion, through Osin--Thom's simple groups; this is the failure for torsion-free groups, which refutes Osin--Thom's torsion-free conjecture itself.
---

**ESTABLISHED (literature import).** For every `n ∈ N` there is a countable
torsion-free group `Γ_n` with

```text
beta_1^(2)(Γ_n) = n      and      normal rank n(Γ_n) = 1.
```

Each `Γ_n` is locally free, hence locally indicable. It is not finitely
generated: it is a directed union of free groups `F(m)` of rank `n + 1`.

Source: S. P. Fisher and Y. Lodha, *A note on normal generation and the first
`ℓ^2`-betti number*, arXiv:2608.25988v1 (26 August 2026), **Theorem 1.2**. This
disproves Conjecture 1.3 of Osin–Thom, *Normal generation and `ℓ^2`-Betti numbers
of groups*, arXiv:1108.2411v2 (Math. Ann. 2013): "Let G be a torsion free discrete
group. Then β^(2)(G) ≤ nrk(G) − 1." Both statements were read from the PDF text on
2026-09-12.

## What changes

- The torsion-free Osin–Thom inequality was an imagined second road to the
  Wiegold problem, the Levin conjecture, torsion-free Kervaire (already
  Klyachko's theorem) and a case of Whitehead asphericity. That road is closed
  for arbitrary countable torsion-free groups.
- The counterexamples are not finitely generated. A finitely generated
  torsion-free form of the inequality is not refuted by this source.
- `torsion-breaks-l2-normal-rank-bound` and its dead KL route are unaffected.
  They concern groups with torsion.
