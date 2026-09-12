---
rg: 2
id: atlas-a4-context-network-simultaneous-hs-exactification-proof
kind: route
title: Stallings plus Gerasimova-Shchepin simultaneously exactify the context network
target: atlas-a4-context-network-simultaneous-hs-exactification
requires:
  - atlas-shortest-a4-triangle-packet
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Construct the graph of groups described in the claim.  Every vertex group is
`A8` or `A4`, every edge group is `C2` or `C3`, and the graph is finite.
Stallings' graph-of-groups theorem therefore makes each connected component of
its fundamental group virtually free.

Gerasimova--Shchepin, *Virtually free groups are p-Schatten stable*,
arXiv:2107.10032, prove stability of every finitely generated virtually free
group for normalized p-Schatten norm, hence for normalized Hilbert--Schmidt
norm at `p=2`.  Their definition is same-dimension stability: an asymptotic
homomorphism is approximated on the fixed presentation generators by genuine
representations in the original matrix spaces.

Now feed in a canonical atlas sequence.  On the two `A8` vertices all group
relations hold exactly.  At an `A4` context vertex the selected generators
already satisfy their order-three and order-two relations exactly, while the
third triangle relation is precisely one of the thirty pair-cubes from
`atlas-shortest-a4-triangle-packet`, so its defect tends to zero.

Choose a maximal spanning forest.  Send every stable letter for a non-tree edge
to `1`.  Every edge-group conjugacy/identification relation then holds exactly:
the cyclic generator on the context side and on the chart side is literally
the same atlas matrix.  Thus the only nonzero relation defects in this fixed
finite graph-of-groups presentation are the thirty pair-cube defects, all
`o(1)`.

Apply normalized-HS stability componentwise.  The resulting exact
representations are `o(1)` from the atlas assignment on every presentation
generator.  In particular every stable letter, whose input value was `1`, is
`o(1)` from `1`.  This gives one simultaneous exactification of all contexts
and their overlaps, as claimed.
