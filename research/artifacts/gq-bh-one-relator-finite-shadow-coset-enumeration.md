# Finite shadows of the gluing group for Z/2 acting on two points: coset enumeration

Computer certificate for item 2 of `research/splitting-kills-the-finite-shadow-parity-of-the-gluing-group.md`
(bh-one-relator, 2026-09-18). GAP 4.13.1, `Index` by Todd–Coxeter coset enumeration, single process, a few
seconds on an MSI node.

## What is computed

`G_f(m)` is presented by:
- generators `a_k, b_k` (`1 ≤ k < m`), the adjacent transpositions of cones `k, k+1` in copy 1 and in copy 2;
- `sg_k` (`1 ≤ k ≤ m`), the swap of the two copies over cone `k`;
- `s`, the global swap.

The relations are:
- the relations of `N_f = (S_m × S_m) ⋊ ⟨s⟩` and of `M_f = (Z/2)^m ⋊ S_m`;
- the amalgamation `d_k = a_k b_k` (diagonal transpositions) and `s = sg_1 ⋯ sg_m`;
- the disjoint-support relators `[sg_k, (l j)^(i)] = 1` for `k ∉ {l, j}`.

`H = ⟨a, b, s⟩` is the image of `N_f`. The run prints `Index(G_f(m), H)`, then the index again with the single
braid relator `(b_1 sg_2)^3` added.

Expected values:
- if `G_f(m) ≅ Sym(2m) × Z/2`, the index is `C(2m, m)`;
- if the braid-added group is `≅ Sym(2m)`, the index is `C(2m, m)/2`.

Since `|H| ≤ 2 (m!)^2` and `G_f(m)` maps onto `Sym(2m) × Z/2`, an index of `C(2m, m)` forces the isomorphism.

## Output

```
m=3 index(G_f:N_f)=20 expected_if_SymxZ2=20 braid-added index=10 expected_if_Sym=10
m=4 index(G_f:N_f)=70 expected_if_SymxZ2=70 braid-added index=35 expected_if_Sym=35
m=5 index(G_f:N_f)=252 expected_if_SymxZ2=252 braid-added index=126 expected_if_Sym=126
```

## Script

```
# Finite shadow of the gluing group for Z/2 acting on two points, with m cones.
# a_k, b_k: adjacent transpositions of cones k,k+1 in copy 1, copy 2; sg_k: swap of copies over cone k; s: global swap.
CosetTableDefaultMaxLimit := 4000000;
Shadow := function(m, addbraid)
  local F, g, a, b, sg, s, rels, T, x, k, l, j, d, G, H;
  F := FreeGroup(3*m-1); g := GeneratorsOfGroup(F);
  a := g{[1..m-1]}; b := g{[m..2*m-2]}; sg := g{[2*m-1..3*m-2]}; s := g[3*m-1];
  T := function(x, l, j) local w, k; w := x[l]; for k in [l+1..j-1] do w := x[k]*w*x[k]; od; return w; end;
  rels := [];
  for x in [a, b] do
    for k in [1..m-1] do Add(rels, x[k]^2); od;
    for k in [1..m-2] do Add(rels, (x[k]*x[k+1])^3); od;
    for k in [1..m-1] do for j in [k+2..m-1] do Add(rels, Comm(x[k], x[j])); od; od;
  od;
  for k in [1..m-1] do for j in [1..m-1] do Add(rels, Comm(a[k], b[j])); od; od;
  Add(rels, s^2);
  for k in [1..m-1] do Add(rels, s*a[k]*s^-1*b[k]^-1); od;
  for k in [1..m] do Add(rels, sg[k]^2); for l in [k+1..m] do Add(rels, Comm(sg[k], sg[l])); od; od;
  for k in [1..m-1] do
    d := a[k]*b[k];
    Add(rels, d*sg[k]*d^-1*sg[k+1]^-1);
    for j in Difference([1..m], [k, k+1]) do Add(rels, Comm(d, sg[j])); od;
  od;
  Add(rels, s^-1*Product(sg));
  for l in [1..m] do for j in [l+1..m] do for k in Difference([1..m], [l, j]) do
    Add(rels, Comm(sg[k], T(a, l, j))); Add(rels, Comm(sg[k], T(b, l, j)));
  od; od; od;
  if addbraid then Add(rels, (b[1]*sg[2])^3); fi;
  G := F/rels;
  H := Subgroup(G, Concatenation(GeneratorsOfGroup(G){[1..2*m-2]}, [GeneratorsOfGroup(G)[3*m-1]]));
  return Index(G, H);
end;
for m in [3, 4, 5] do
  Print("m=", m, " index(G_f:N_f)=", Shadow(m, false), " expected_if_SymxZ2=", Binomial(2*m, m), " braid-added index=", Shadow(m, true), " expected_if_Sym=", Binomial(2*m, m)/2, "\n");
od;
QUIT;
```
