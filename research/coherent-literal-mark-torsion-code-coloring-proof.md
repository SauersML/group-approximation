---
rg: 2
id: coherent-literal-mark-torsion-code-coloring-proof
kind: route
title: Cancel the shared literal mark along each row, then colour the row-column pairs by bounded out-degree
target: coherent-literal-mark-torsion-codes-are-finitely-colorable
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

The only imported result is `finite-mark-centralizer-commutator-area-is-proper`,
abbreviated (FMC).  For a fixed finite-order word `beta` it gives constants
`A_beta>0` and `B_beta` such that every word `eta` with `[beta,eta]=1`
satisfies `Area([beta,eta]) >= A_beta d(<beta>,<beta>eta) - B_beta`,
uniformly over the words representing `eta`.  So for every bound `M` the set

```text
F_beta(M) = { g : Area([beta,eta]) <= M for some word eta of g }
```

lies in `<beta> Ball(R)` with `R=(M+B_beta)/A_beta`, and it is finite.

Two routine area facts are used throughout.

- **(a) Conjugation is free.**  `Area(g w g^(-1)) = Area(w)`, and inverting
  a word does not change its area.
- **(b) Substitution.**  Replacing one occurrence of a subword `u` by `u'`
  changes area by at most `Area(u u'^(-1))`.  A commutator contains each
  entry twice, so replacing an entry costs at most twice the comparison area.

**Step 1 (the marked-fibre identity (LM6)).**  There is a free identity

```text
[c,x^(-1)y] = c x^(-1)y c^(-1) y^(-1) x
            = (c x^(-1) c^(-1)) W (z x),     W = [c,y]z^(-1).
```

Put `u=c x^(-1) c^(-1)` and `u'=z x`.  Then `u W u' = (u W u^(-1))(u u')`.
Now

```text
u u' = c x^(-1) c^(-1) z x = x^(-1) ([c,x]^(-1) z) x,
```

and `[c,x]^(-1) z` is a conjugate of `([c,x]z^(-1))^(-1)`.  So
`Area(u u') <= A` and `Area(uWu^(-1)) = Area(W) <= A`, which gives
`Area([c,x^(-1)y]) <= 2A`.

**Step 2 (row classes are uniformly small).**  Fix a row element `c'` and a
mark label `k`.  Let `w` range over the vertices with `c_w=c'` and
`mu(w)=k`, fix one of them `w_0`, and write `c=c_(w_0)` and `x=h_(w_0)`.

- By (LM4) and (b), `Area([c,h_w] z_k^(-1)) <= A_Delta+2C` for all such `w`.
- Step 1 gives `Area([c, x^(-1)h_w]) <= 2A_Delta+4C`.
- By (LM3) and (b), replacing `c` by `e rho e^(-1)` costs at most `2B`.
- Conjugating by `e^(-1)` gives

  ```text
  Area([rho, e^(-1)x^(-1)h_w e]) <= 2A_Delta+4C+2B.
  ```

So `e^(-1)x^(-1)h_w e` lies in `F_rho(2A_Delta+4C+2B)`.  Hence the column
elements carried by `c'` with label `k` number at most
`D_2 = max_rho |F_rho(2A_Delta+4C+2B)|`, and all column elements carried by
`c'` number at most `D_row = t D_2`.

**Step 3 (out-neighbour rows are uniformly few).**  Fix a column element `h`
and all vertices `v` with `h_v=h`.  Fix one of them `v_0`, and write
`b=b_(v_0)` and `beta` for its prototype.

- For every edge `v -> w`, (LM2), (LM4) and (LM3) give
  `Area([c_w, b beta b^(-1)]) <= A_0+2C+2B`.
- Conjugating by `b^(-1)` puts `b^(-1)c_w b` in `F_beta(A_0+2C+2B)`.

So the out-neighbours of all vertices carrying `h` have at most
`D_col = max_beta |F_beta(A_0+2C+2B)|` distinct row elements.

**Step 4 (colouring).**  Let `P` be the finite set of pairs
`(c_v,h_v)`, taken in `Gamma x Gamma`.  Let `Q` be the directed graph on `P`
with an arc `pair(v) -> pair(w)` for every edge `v -> w` of `G`.

- **No loops.**  If `pair(v)=pair(w)` then `[c_w,h_v]=[c_v,h_v]=z_(mu(v)) != 1`
  in `Gamma`, which contradicts (LM2).
- **Bounded out-degree.**  By Steps 3 and 2, a pair `(c,h)` has arcs to
  pairs with at most `D_col` first coordinates, and each first coordinate
  has at most `D_row` second coordinates.  So the out-degree is at most
  `K=D_col D_row`.
- **Degeneracy.**  Every finite subgraph of the underlying undirected graph
  of `Q` has at most `K` times as many edges as vertices, so it has a vertex
  of degree at most `2K`.  Greedy colouring gives `chi(Q) <= 2K+1`.
- **Pullback.**  A colouring of `Q` pulls back along `v -> pair(v)` to a
  proper colouring of `G`, because every edge of `G` maps to an arc between
  distinct pairs.

This proves (LM5).  ∎

**Corollary (LM7).**  Work in `St_20(L_(F_2)(1,2))` and fix `i`, the word
`c_i` and `j_0=i+1`.  Suppose `Area([c_i,h_(ij)]z^(-1)) <= A` for infinitely
many `j`.

- Step 1 puts `h_(ij_0)^(-1)h_(ij)=x_23(D_(ij_0)+D_(ij))` in
  `F_(c_i)(2A)`.  Here (FMC) is applied to the single fixed finite-order word
  `c_i`, which has order two.
- Two of these elements lie in one `<c_i>`-coset only if
  `x_23(D_(ij)+D_(ij'))` lies in `{1, x_12(A_i)}`.  In `E_20` its image is
  an elementary matrix at position `(2,3)`, so this forces
  `D_(ij)=D_(ij')`, that is `j=j'`.
- So infinitely many cosets would occur inside the finite set `F_(c_i)(2A)`,
  which is impossible.

For vertex-dependent row words, substitution (b) adds `2 kappa_(ij)` to each
diagonal area, and the same argument applied along any subsequence gives the
limit statement.  ∎
