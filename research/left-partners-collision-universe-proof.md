---
rg: 2
id: left-partners-collision-universe-proof
kind: route
title: Split a partner into collision components and walk the component containing the identity
target: left-partners-lie-in-collision-universes
requires: []
---

## Proof

Let `B A = 1` with `k` of characteristic two, and write `B = sum_(b in S) [b]`,
`S = supp B`.

1. **Collision graph.** On `S` put an edge `b ~ b'` when the sets
   `b supp(A)` and `b' supp(A)` share an element of `G`. Let `C_1, ..., C_m`
   be the connected components and `B_i = sum_(b in C_i) [b]`.
2. **Disjoint products.** If `x` lies in `C_i supp(A)` and in `C_j supp(A)`,
   then `x = b a = b' a'` with `b in C_i`, `b' in C_j`, so `b ~ b'` and `i = j`.
   Hence `supp(B_i A)` lies in `C_i supp(A)`, and these sets are pairwise
   disjoint.
3. **One component carries the identity.** `B A = sum_i B_i A` is a sum of
   elements with pairwise disjoint supports, and it equals `[1]`. So exactly
   one `B_0 = B_i` has `B_0 A = 1`, and every other `B_j A = 0`.
4. **A root.** Since `1` lies in `supp(B_0 A)`, some `b in C_i` and `a in supp A`
   satisfy `b a = 1`, that is `b = a^(-1)`.
5. **Walking the component.** Every `b'` in `C_i` is joined to `b` by a path
   `b = b_0 ~ b_1 ~ ... ~ b_r = b'` with `r < |C_i|`. Each edge gives
   `b_t a = b_(t+1) a'`, so `b_(t+1) = b_t a a'^(-1)` lies in
   `b_t supp(A) supp(A)^(-1)`. Hence `b'` lies in `A^(-1) (A A^(-1))^r`.

The dual statement for a fixed right factor `B` uses the edge
`a ~ a'` when `B a` and `B a'` share an element, the root `a = b^(-1)`, and the
steps `a' = b'^(-1) b a`, giving `(B^(-1) B)^r B^(-1)`. The coefficient version
over an arbitrary field is the same argument with coefficients carried; step 3
needs only that elements with disjoint supports sum to `[1]` only if one of them
equals `[1]`. QED

## Implementation

`experiments/kaplansky_collision_partner_search.py` builds `U_r` layer by
layer, removes columns forced to zero by rows met by a single column (a sound
peeling step: a row `g != 1` met once forces that column's coefficient to be
`0`), eliminates over `F_2`, and re-verifies any hit exactly. Positive control:
`1 + x + x^2` with `x` of order seven, whose inverse is found at depth one.
