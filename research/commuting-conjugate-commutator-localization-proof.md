---
rg: 2
id: commuting-conjugate-commutator-localization-proof
kind: route
title: Push the boundary chain of the commutator into the free Z[H]-module of edges, divide by (1-x)(1-y), and read a short Schreier path off the quotient chain
target: commuting-conjugate-commutator-area-localizes-conjugators
requires: []
---

This is a complete direct proof.

## Notation

`X = Cay(Gamma, S)` is the Cayley graph, with vertex set `Gamma` and edges
`g e_s = (g, gs)` for `g in Gamma`, `s in S`.  `Gamma` acts freely on the left.
`C_0 = Z[Gamma]` and `C_1 = ⊕_{s in S} Z[Gamma] e_s` are the finitely
supported integral chains, with `∂(g e_s) = gs - g`, and `||·||` is the `l^1`
norm on coefficients.  For a word `w` and a vertex `g`, `g P_w in C_1` is the
signed edge chain of the path that starts at `g` and reads `w`.  For words
`u, v` with elements `ū`:

```text
P_(uv) = P_u + ū P_v,     P_(u^(-1)) = -ū^(-1) P_u,
∂P_u = ū - 1,             ||P_u|| <= |u|.                      (N1)
```

## Step 1: the diagram bounds a chain

Let `W` be a null-homotopic word with a van Kampen diagram of area `A`.  Each
2-cell `f` maps to a translate `g_f` of the loop of a relator `r_f`.  Interior
edges of the diagram cancel in pairs, so the chain of the boundary loop is

```text
P_W = Σ_f ± g_f P_(r_f),       ||P_W|| <= A M.                    (N2)
```

(Spurs and degenerate pieces of the diagram contribute cancelling pairs, so
they do not affect `(N2)`.)

## Step 2: the boundary chain of the commutator

Put `X_w = delta c delta^(-1)` and `Y_w = epsilon kappa epsilon^(-1)`, so that
`W = X_w Y_w X_w^(-1) Y_w^(-1)`.  By `(N1)`,

```text
P_(X_w) = P_delta + d P_c - d c d^(-1) P_delta = (1-x) P_delta + d P_c,
P_(Y_w) = (1-y) P_epsilon + e P_kappa.
```

Since `x` and `y` commute, `(N1)` gives

```text
P_W = P_(X_w) + x P_(Y_w) - x y x^(-1) P_(X_w) - x y x^(-1) y^(-1) P_(Y_w)
    = (1-y) P_(X_w) - (1-x) P_(Y_w).
```

Substituting, and using that `1-x` and `1-y` commute,

```text
(1-x)(1-y) Q = P_W - (1-y) d P_c + (1-x) e P_kappa,
Q := P_delta - P_epsilon,        ∂Q = d - e.                      (N3)
```

By `(N1)`, `(N2)` and `(L1)`,

```text
|| (1-x)(1-y) Q ||  <=  A M + 2|c| + 2|kappa|  =  2R.             (N4)
```

## Step 3: few edge orbits

Choose a right transversal `T` for `H` in `Gamma`, so that `Gamma` is the
disjoint union of the cosets `H t`.  As a left `Z[H]`-module,

```text
C_1 = ⊕_{t in T, s in S} Z[H] · t e_s,
```

and the `l^1` norm is the sum of the `l^1` norms of the components.  Write
`Q = Σ_{t,s} q_(t,s) · t e_s` with `q_(t,s) in Z[H]`.  Left multiplication by
`(1-x)(1-y)` acts componentwise.

`H` is a finitely generated torsion-free abelian group, so `H ≅ Z^k`.  Fix a
total order on `H` compatible with the group law.  For `0 != p in Z[H]`, the
largest and the smallest monomials of a product are the products of the
largest and the smallest monomials of the factors, so they have nonzero
coefficients.  Since `x != 1` and `y != 1`, each of `1-x` and `1-y` has two
distinct monomials, so the largest and smallest monomials of
`(1-x)(1-y)p` are distinct.  Hence

```text
p != 0   ==>   || (1-x)(1-y) p ||  >=  2.                          (N5)
```

(When `x, y` are a basis of `H ≅ Z^2`, the Newton polygon of `(1-x)(1-y)p` is
the Minkowski sum of that of `p` with a unit square.  It has at least four
vertices, so the bound improves to `4`.)

By `(N4)` and `(N5)`, the set

```text
O = { (t,s) : q_(t,s) != 0 }       has      |O| <= R.              (N6)
```

## Step 4: a short Schreier path

Let `Y = H \ X` be the Schreier graph: its vertices are the cosets `Hg`, and
its edges are `(Hg, Hgs)`.  The quotient map `π` is a morphism of graphs.  On
chains it sends `h t e_s` to the edge `(Ht, Hts)` and commutes with `∂`.  So

```text
π(Q)   = Σ_{(t,s) in O} ε(q_(t,s)) · (Ht, Hts),
∂ π(Q) = π(d - e) = Hd - He,                                       (N7)
```

with `ε` the augmentation.  Let `Σ` be the subgraph formed by the edges of
`π(Q)` with nonzero coefficient.  By `(N6)` it has at most `R` edges.

If `Hd = He`, then `(L2)` holds with the empty word.  Otherwise `He` has
coefficient `-1` in `∂π(Q)`, so it is a vertex of `Σ`.  Let `Σ_0` be its
connected component.  The restriction of `π(Q)` to `Σ_0` has boundary equal to
the restriction of `∂π(Q)` to the vertices of `Σ_0`, and that boundary has
augmentation zero.  Its only possible support points are `He` and `Hd`, so
`Hd in Σ_0`.  Therefore some path in `Σ_0`, reading a word `w` with
`|w| <= R`, joins `He` to `Hd`.

Lift this path to `X` starting at the vertex `e`.  It ends at `e w̄`, which lies
over `Hd`.  So `H e w̄ = H d`, that is,

```text
d  in  H · e · B_R.                                                (L2)
```

## Special case

Take `epsilon` empty and `d in C(c) ∩ C(kappa)`.  Then `e = 1`, `x = c`,
`y = kappa`, and `H = <c, kappa> ⊂ D = C(c) ∩ C(kappa)`.  By `(L2)`, `d = h g`
with `h in H` and `|g| <= R`, and `g = h^(-1) d in D`.  Thus every `d` with
`f(d) <= A` lies in `H · (D ∩ B_R)`.  That set meets at most `|B_R|` classes of
`D/H`.

## Corollary (star finiteness)

Apply `(L2)` with `delta = u_b`, `epsilon = u_a`, `kappa = h`.  Then
`x = C_b` and `y = H_a` as elements.  They commute by hypothesis, and they
generate a torsion-free abelian group because `Gamma` is torsion-free.  So
`t_b = x^i y^j t_a w̄` with `|w| <= R`.  Conjugating `c` by both sides and using
`[x, y] = 1`,

```text
x = t_b c t_b^(-1) = x^i y^j (t_a w̄ c w̄^(-1) t_a^(-1)) y^(-j) x^(-i),
```

hence `t_a w̄ c w̄^(-1) t_a^(-1) = y^(-j) x y^j = x`.  Thus `C_b` lies in the
set `{ t_a w̄ c w̄^(-1) t_a^(-1) : |w| <= R }`, which has at most `|B_R|`
elements.  The statement for `H_a` is symmetric: `(L2)` also gives
`t_a in H t_b B_R`, since `B_R` is closed under inverses.

## Remarks

- No diagram surgery, no annulus, and no covering-space argument are used.
  The only facts needed are `(N2)` and the injectivity of `(1-x)(1-y)` on the
  domain `Z[H]`, with its two-term lower bound.
- Torsion-freeness of `H` is used only in `(N5)`.  If `x` had finite order
  `n`, then `1-x` would be a zero divisor, since
  `(1-x)(1+x+...+x^(n-1)) = 0`, and the bound would fail.
- Nothing about `delta` or `epsilon` (shortest, reduced, compatible) is used.
  Every word for `d` obeys the same bound, which is why the conclusion is
  uniform over all systems of vertex words in a template.
- **Sanity check** in `Z^3 = <c, kappa, t>` with commutator relators:
  `delta = t^n`.  Here `(N4)` forces `4n <= 4A + 4`, so `A >= n - 1`.  The true
  area is `2n`: the boundary contains `4n` `t`-edges and each square carries
  two of them.  So the bound has the right order.  It is also consistent with
  `f(c_K^q) = O(1)`, because `c_K^q in H`.
