---
rg: 2
id: k1222-planar-cover-fold-divisible-by-six-proof
kind: route
title: An exact 3^8-dimensional monomial solution for K_{1,2,2,2} over Z_3, pushed through planar covers by a spherical van Kampen diagram
target: k1222-planar-cover-fold-divisible-by-six
requires: []
artifacts:
  - experiments/odd-p-incidence-pquotient-2026-09-17/verify_monomial.py
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_p3_monomial.json.gz
  - experiments/odd-p-incidence-pquotient-2026-09-17/run_k1222_cert.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/monomial_fast.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_cert.out
---

Notation is as in the claim.

## Item 1: `J` has order 3 in `Gamma_3(K_{1,2,2,2}, delta_1)`

`J^3 = 1` is a defining relation.  For `J != 1` it is enough to find unitary
matrices `X_e, Z` that satisfy all defining relations with `Z != I`.  The
assignment `x_e -> X_e, J -> Z` is then a homomorphism, and it does not kill
`J`.

The file `k1222_p3_monomial.json.gz` lists 19 monomial matrices of size
`n = 6561`: one for each of the 18 edges, in lexicographic order (as in
`run_k1222_cert.g`), and then `J`.  Each matrix is a permutation `pi` together
with phases `c_i in Z_3`, acting by `e_i -> zeta_3^{c_i} e_{pi(i)}`.  The
script `verify_monomial.py` (graph `k1222`) rebuilds the graph and its
orientation independently.  Using only integer arithmetic, it checks:

- the `J` matrix is a scalar `zeta_3^c` with `c != 0 mod 3`;
- `X_e^3 = I` for all 18 edges;
- `X_e X_f = X_f X_e` for all pairs of edges sharing a vertex;
- at each vertex `v`, the product `prod_{e at v} X_e^{sigma(v,e)}` equals
  `J^{b_v}`.

If all checks pass, item 1 holds.  No step depends on GAP.

How the matrices were found:

1. `run_k1222.g`: the largest 3-quotient of class `<= 3` of
   `Gamma_3(K_{1,2,2,2},delta_1)` has order `3^109` and contains a nontrivial
   image of `J`.  At class `<= 2`, `J` dies, as the Lazard bound forces.
2. `reduce.g`: repeatedly factoring out a hyperplane of `Omega_1(Z)` that
   avoids `J` leaves a quotient `P` of order `3^19` with centre `<J>`, class 3
   and exponent 9.  Every relator of `Gamma` is re-evaluated on the images and
   holds.
3. `monomial_fast.g`: `P` has an abelian normal subgroup `A` with
   `C_P(A) = A`, `|A| = 3^11`, index `3^8`.  A linear character `chi` of `A`
   with `chi(J) = zeta_3` is induced to `P`, and the induced matrices are
   written out.  This uses the same mathematics as `monomial.g` with faster
   coset indexing.

## Item 2: the covering lemma

Let `G` be a connected simple graph with orientation `o` and weights `b`.
Let `phi: H -> G` be a k-fold cover with `H` finite and planar.

**(a) Covers are simple and components are covers.**  The edges at `v'` map
injectively to edges at `phi(v')`, and `G` has no loops or parallel edges, so
`H` has none either.

Let `H_0` be a component of `H`.  The image `phi(V(H_0))` is nonempty and
closed under taking neighbours, since every edge at `phi(v')` lifts to an edge
at `v'`.  Because `G` is connected, `phi` restricted to `H_0` is surjective.
It is again a cover, of some fold `k_0`.

The fibre size is constant.  For an edge `uv` of `G`, each vertex over `u` has
exactly one edge over `uv`, and so does each vertex over `v`.  Hence
`|phi^{-1}(u)| = |phi^{-1}(uv)| = |phi^{-1}(v)|`, and connectedness of `G`
gives a constant.  Summing over components, `k = sum k_0`.

**(b) Pull-back homomorphism.**  Orient `H` by `o' = o ∘ phi` and set
`b' = b ∘ phi`.  Define `psi: Gamma_m(H,b') -> Gamma_m(G,b)` by
`x_{e'} -> x_{phi(e')}` and `J -> J`.  Check each relation:

- `x^m`, `J^m` and `[x,J]`: clear.
- `[x_{e'}, x_{f'}]` for `e', f'` at `v'`: the images are edges at `phi(v')`,
  so they commute in `Gamma_m(G,b)`.
- The vertex relator at `v'`: `phi` is a bijection from the edges at `v'` to
  the edges at `phi(v')`.  The pulled-back orientation preserves `sigma`, and
  `b'(v') = b(phi(v'))`.  So the image is the vertex relator at `phi(v')`,
  with its factors in a different order.  Those factors pairwise commute in
  `Gamma_m(G,b)`, so the image holds.

**(c) Planar sphere identity.**  Let `H_0` be a component of `H` (it has an
edge, since `G` does), embedded in the sphere `S^2`.  Consider the dual map
`H_0^*`:

- the faces of `H_0^*` are the vertices `v'` of `H_0`;
- each edge `e'` gives a dual edge `e'^*` crossing it once, separating the two
  faces `head(e')^*` and `tail(e')^*`, which are distinct because `H_0` has no
  loops.

Orient `e'^*` so that `head(e')^*` lies on its left, and label it `x_{e'}`.
The counterclockwise boundary walk of the face `v'^*` crosses the dual edges
of exactly the edges at `v'`, once each, in rotation order.  It traverses
`e'^*` forwards exactly when `v' = head(e')`.  So its label is
`w_{v'} = prod_{e' at v'} x_{e'}^{sigma(v',e')}`, taken in rotation order.

`H_0^*` is a spherical diagram over the free group on the `x_{e'}`.  Delete
one face `F_0 = v_0'^*`.  What remains is a (possibly singular) disc diagram
with boundary label `w_{v_0'}^{-1}`, all of whose faces are counterclockwise
oriented with labels `w_{v'}`.  By van Kampen's lemma (Lyndon-Schupp,
Chapter V, Lemma 1.1 and the discussion of singular discs), there are words
`g_{v'}` with

```text
w_{v_0'}^{-1} = prod_{v' != v_0'} g_{v'} w_{v'} g_{v'}^{-1}
```

in the free group.

In `Gamma_m(H,b')` each `w_{v'}` equals `J^{b'(v')}`: it is the vertex
relator with its factors reordered, and those factors commute. `J` is
central, so the displayed identity becomes
`J^{-b'(v_0')} = J^{sum_{v' != v_0'} b'(v')}`.  That is,
`J^{sum_{v' in H_0} b'(v')} = 1` in `Gamma_m(H,b')`.

**(d) Conclusion.**  `sum_{v' in H_0} b(phi(v')) = k_0 sum_v b_v = k_0|b|`.
Applying `psi` gives `J^{k_0|b|} = 1` in `Gamma_m(G,b)` for every component.
Since `k = sum k_0`, it follows that `J^{k|b|} = 1`.  This is Slofstra-Zhang
Lemma 3.10; the argument above is included so the claim is self-contained.

## Items 3 and 4

Take `G = K_{1,2,2,2}`, `m = 3`, `b = delta_1`, so `|b| = 1`.

- A planar k-fold cover gives `J^k = 1` by item 2.
- `J` has order 3 by item 1.
- Hence `3 | k`.

Archdeacon-Richter (J. Graph Theory 14 (1990), "On the parity of planar
covers") show that a planar cover of a nonplanar graph has even fold, so
`6 | k`.  The same conclusion follows from item 2 at `m = 2`, using Arkhipov's
theorem that `J != 1` in `Gamma_2(G)` for nonplanar `G`.

Annor-Nikolayevsky-Payne (arXiv 2311.01672) show `k >= 14`.  So
`k in {18, 24, 30, ...}`.

For the conditional statement in the claim: if `J != 1` in `Gamma_p(G,delta)`
for infinitely many primes `p`, then item 2 forces every such `p` to divide
`k`, which is impossible for a finite `k`.
