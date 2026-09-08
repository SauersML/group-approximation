---
rg: 2
id: jacobson-joint-cells-are-two-braids
kind: claim
title: The joint Jacobson cells are two braids with exact finite-type rank restrictions
artifacts:
  - research/artifacts/jacobson-two-braid-reduction-2026-09-07.md
  - experiments/jacobson_two_braid_audit.py
  - research/artifacts/jacobson-two-braid-replay-2026-09-07.json
distinct_from:
  binary-jacobson-joint-shortest-cells-force-tail-action: that kills the head after the tail is killed; this rewrites the joint presentation and excludes separated-factor matrix representations even when the tail is retained.
  binary-jacobson-joint-shortest-cells-exclude-natural-completions: that treats a natural head with trivial spectators; this includes arbitrary separated head and tail modules and proves exact rank balances for arbitrary complex packet types at braid defects below two.
---

For `F=GL_3(F_2)_Q x GL_3(F_2)_P`, the joint shortest-cell group is

```
Gamma=<F,h | h^2=1, [h,K]=1, (h b)^3=(h d_P)^3=1>,
K=GL(<e_1,e_3>)_Q, b=(w_23,w_23), d_P=(1,w_13).
```

The controlled relator is conjugate to `(h d_P)^3`, so their operator
norm defects are equal on exact finite packets. The head mark
`w=(I+E_13,1)` is nontrivial by the explicit action on three rays.

In every finite-dimensional exact unitary packet with an overlap-central
involution and both braid defects strictly below two, the marked negative
rank is `8k` for an integer `k>=0`. More precisely, for the two standard
row four-groups, every joint character multiplicity whose head character
is nontrivial equals the same `k`. In particular, half of the marked
negative space is negative for each tail transvection.

If the head and tail act on separate direct summands and the mark
survives, the maximum braid defect is exactly two. The exact algebraic
exclusion of such separated modules holds over every field. These
restrictions do not exclude arbitrary mixed packet types.
