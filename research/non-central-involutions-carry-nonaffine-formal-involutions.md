---
rg: 2
id: non-central-involutions-carry-nonaffine-formal-involutions
kind: claim
title: A group with a non-central involution carries a non-affine one-track binary automaton that is a formal involution
distinct_from:
  formalizable-binary-pairs-over-biorderable-groups-are-affine: that proves formal one-track binary pairs over bi-orderable groups are affine; this exhibits non-affine formal one-track pairs on every group with a non-central involution, so the torsion-free hypothesis there is essential.
  binary-left-inverse-pairs-need-not-be-formalizable: that is a non-formalizable one-track pair over the integers; this gives formalizable non-affine one-track pairs on hosts with torsion, including Thompson's V and the binary Leavitt unit group.
  zero-divisor-shears-are-formal-automorphisms: that is the general gate theorem; this is its explicit one-track instance with a non-affine rule.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

Let `s in G` have order two, and let `m in G` satisfy `m^(-1) s m ≠ s`. On `{0,1}^G` put
`S(h) = x(h) + x(hs)` and

```text
tau(x)(h) = x(h) + S(h)·( S(hm) + S(hsm) ).
```

Then `tau` is a formal involution: its multilinear representative composed with itself is the identity
polynomial. It is not affine.

**Proof.**
- **It is a zero-divisor shear.** It equals `x + L_N(Gamma(L_N x))` with `N = 1 + s`, `N^2 = 0` and
  `Gamma(z)(h) = z(h) z(hm)`. So it is a formal involution by `zero-divisor-shears-are-formal-automorphisms`.
- **It is not affine.** The six cells `h, hs, hm, hms, hsm, hsms` are pairwise distinct because
  `m^(-1) s m ≠ s`. So the rule is a multilinear quadratic, and such a representative is unique over `F_2`.

**Consequences.**
- **Simple hosts.** Every finitely generated simple group with 2-torsion carries such automata, since
  its centre is trivial. That includes Thompson's `V` and `L_(F_2)(1,2)^x`, whose swap is an involution.
- **One-track affine rigidity** (bi-orderable hosts) and the marker refutations over `Z` and `Q` do not
  transfer to these hosts, not even at one track.
- **Infinite dihedral group** (`m = g`): in cell coordinates `a(k) = x(g^k)`, `b(k) = x(g^k s)`, the
  automaton is `(a, b) -> (a + c, b + c)` with `c(k) = S(k)(S(k−1) + S(k+1))` and `S = a + b`.

Proof: artifact Section 3, Corollary 6, route `non-central-involution-formal-involution-proof`.
