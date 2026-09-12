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
  Wiegold problem (since solved by Chen–Lodha, below), the Levin conjecture,
  torsion-free Kervaire (already Klyachko's theorem) and a case of Whitehead
  asphericity. That road is closed for arbitrary countable torsion-free groups.
- The Wiegold problem is solved by other means. L. Chen and Y. Lodha, *The
  Wiegold problem and free products of left-orderable groups*,
  arXiv:2510.26073 (v1 30 October 2025, v2 1 December 2025), abstract: "We
  show that any free product of nontrivial left-orderable groups has normal
  rank greater than one. This solves the Wiegold problem by taking free
  products of finitely generated perfect left-orderable groups". Read from the
  arXiv abstract page on 2026-09-12.
- The counterexamples are not finitely generated. A finitely generated
  torsion-free form of the inequality is not refuted by this source.
- `torsion-breaks-l2-normal-rank-bound` and its dead KL route are unaffected.
  They concern groups with torsion.
