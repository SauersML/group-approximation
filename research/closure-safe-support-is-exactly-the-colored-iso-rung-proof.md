---
rg: 2
id: closure-safe-support-is-exactly-the-colored-iso-rung-proof
kind: route
title: Colour pairs by support components, read isomorphism games back as bisynchronous games, and corner the gap in the union's quantum automorphism group
target: closure-safe-support-is-exactly-the-colored-iso-rung
requires: []
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
---

**Sources.**

- (H1) BCEHPSW, arXiv:1812.11474v2, Theorem 2.1(3),(4), read at source.
- (L1) Lupini--Mančinska--Roberson, arXiv:1712.01820v2, pp. 9--10, read at
  source.  For a quantum permutation group the antipode `S(u_(xy)) = u_(yx)`
  is *-linear.  So the group is of Kac type and its Haar state is tracial.
  The paper states this for `Qut(X)` of a graph.
- (Q) Steps 1, 5, 6 and 7 of
  `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group-proof`.

**(P0)** For projections `p, q` and a tracial state `tau`,
`tau(pq) = tau(qpq) = ||pq||_(2,tau)^2`.  So `tau(pq) = 0` iff `pq` vanishes in
the GNS representation.

**(P1)** Suppose `|I| = |O| = N`, the rows `(e_(ij))_j` are PVMs, and
`e_(ij) e_(i'j) = 0` for `i != i'`.  Then each column sum `q_j = sum_i e_(ij)`
is a projection, and `sum_j q_j = N 1`.  Under a tracial state, `tau(q_j) <= 1`
together with `sum_j tau(q_j) = N` gives `tau(1 - q_j) = 0`.  So `q_j = 1` in
any representation with a faithful trace, in particular in the GNS algebra and
in `R^U`.

**(P2) Reverse-consistent colours.**  If `v_(xa) v_(x'a') != 0`, its adjoint
`v_(x'a') v_(xa)` is nonzero too.  So both `c_X(x,x') = c_Y(a,a')` and
`c_X(x',x) = c_Y(a',a)` hold.  Refining colours to
`c'(x,x') = (c(x,x'), c(x',x))` therefore does not change `A(Iso(X,Y))`, and
we assume that colour classes are closed under transpose.  By Step 1 of (Q),
the relations say exactly that `V` intertwines each pair of colour-class
indicator matrices `(E_k^X, E_k^Y)`.

**(CS1 => CS2).**  Take `H` and a closure-safe `tau` as in (CS1).  Put
`V_X = I` and `V_Y = O`.

- **Colours.**
  - `c_X(i,i')` is the component of `S_tau` containing `(i,i')`.  Every
    question pair has positive degree, since
    `sum_(j,j') tau(e_(ij) e_(i'j')) = 1`.
  - `c_Y(j,j')` is the component containing `(j,j')` if its degree is
    positive.  Otherwise it is a fresh colour private to `(j,j')`, marked
    diagonal when `j = j'`.
- **Diagonal reservation.**  Row orthogonality gives
  `tau(e_(ij) e_(ij')) = 0` for `j != j'`, and injectivity gives
  `tau(e_(ij) e_(i'j)) = 0` for `i != i'`.  So `S_tau` joins diagonal pairs only
  to diagonal pairs, and every component is diagonal or off-diagonal.
- **qc.**  Let `M = pi_tau(A(H))''` with its faithful trace, and put
  `V_(ij) = pi_tau(e_(ij))`.  By (P1), `V` is a magic unitary.  If
  `c_X(i,i') != c_Y(j,j')`, then `(j,j')` is not adjacent to `(i,i')` in
  `S_tau`.  So `tau(e_(ij) e_(i'j')) = 0`, and `V_(ij) V_(i'j') = 0` by (P0).
  This gives a unital *-homomorphism `A(Iso(X,Y)) -> M`, hence a tracial state.
- **Not qa.**  `e_(ij) |-> v_(ij)` is a unital *-homomorphism
  `A(H) -> A(Iso(X,Y))`.  Rows sum to one.  If `lambda(i,i',j,j') = 0`, closure
  safety puts `(i,i')` and `(j,j')` in different components, and fresh colours
  match nothing, so the colours differ and `v_(ij) v_(i'j') = 0`.  A unital
  *-homomorphism `A(Iso(X,Y)) -> R^U` would compose to one for `A(H)`, and
  there is none.

**(CS2 => CS1).**  Let `H` have questions `V_X`, answers `V_Y`, and rule
`lambda(x,x',a,a') = [c_X(x,x') = c_Y(a,a')]`.

- **Bisynchronous.**  Diagonal reservation makes `H` synchronous and
  injective.  A tracial state on `A(Iso(X,Y))` gives `|V_X| = |V_Y|`, by taking
  the trace of all entries summed by rows and by columns.
- **Tracial state.**  `A(H) -> A(Iso(X,Y))`, the identity on generators, is a
  unital *-homomorphism, since the target has more relations.  It pulls the
  tracial state back.
- **Closure safety.**  Edges of `S_tau` join pairs of equal colour.  So every
  component is monochromatic, and `lambda = 1` on it.
- **No R^U model.**  A unital *-homomorphism `A(H) -> R^U` has column sums one
  by (P1).  So it factors through `A(Iso(X,Y))`, which has none.

**(Non-embeddable quantum automorphism group).**  Let `X, Y` be as in (CS2),
with colours as in (P2), and put `n = |V_X| = |V_Y|`.

- **The union.**  `Z = V_X ⊔ V_Y`, with `c_Z` equal to `c_X` and `c_Y` on the
  two parts and a new colour `cross` on mixed pairs.
- **The group.**  `G = Qut(Z)` is the quotient of `O(S_(2n)^+)` by the
  relations `U E_k = E_k U`, over the transpose-closed family of colour
  indicators `E_k`.  Its coproduct respects the relations: in
  `sum_(e,e') u_(ze) u_(z'e') (x) u_(ew) u_(e'w')`, each term vanishes on one
  leg when `c_Z(z,z') != c_Z(w,w')`.  The antipode respects them because the
  family is closed under transpose.  By (L1), `h` is tracial.
- **The central projection.**  `R = sum_(k != cross) E_k` is `J_X (+) J_Y`, and
  it intertwines `U` with itself.  So the identities (S2) of (Q), Step 3, hold,
  and `P = sum_(b in Y) u_(xb)` is central.
- **`P != 0`.**  Given `V` over `A(Iso(X,Y)) != 0`, the matrix
  `U' = [[0,V],[V^t,0]]` is a magic unitary obeying the colour relations of
  `Z`.
  - On the `XY` and `YX` blocks the products are `v_(xa) v_(x'a')`, which
    vanish unless `c_X(x,x') = c_Y(a,a')`.
  - Mixed pairs go to mixed pairs.

  So there is a homomorphism `O(G) -> A(Iso(X,Y))` with `P |-> 1`.
- **Conclusion.**  Steps 5, 6 and 7 of (Q) apply verbatim.  `h(P) = 1/2`,
  `v_(xa) |-> u_(xa)` maps `A(Iso(X,Y))` into `P O(G)`, and a Connes embedding
  of `L^infinity(G)` would give a unital *-homomorphism `A(Iso(X,Y)) -> R^U`.
