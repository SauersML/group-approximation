---
rg: 2
id: factorization-amenable-extension-induced-compression-proof
kind: route
title: Induce a Hilbert-Schmidt model of the kernel to the extension and compress it to a Folner window
target: factorization-property-closed-under-amenable-extensions
requires: []
artifacts:
  - research/artifacts/factorization-amenable-extensions-2026-09-05.md
---

Write `p : G -> Q` for the quotient map, fix a set-theoretic section
`s : Q -> G` with `s(e) = e`, and use Brown's characterisation
(Theorem 3.1.6): a trace `tau` on a unital C*-algebra `A` is amenable if and
only if there are u.c.p. maps `Phi_n : A -> M_(k_n)` with
`||Phi_n(ab) - Phi_n(a)Phi_n(b)||_2 -> 0` and `tr o Phi_n -> tau` pointwise,
where `||.||_2` is the normalized Hilbert--Schmidt norm.  For a group algebra
it suffices to check both conditions on group elements: the u.c.p. maps are
contractive for `||.||_2` in the sense `||Phi(a)||_2 <= ||a||`, the group
elements span a dense *-subalgebra, and the defect on a product of sums is a
finite sum of defects on group elements.

**Step 1 (the kernel's models).**  Let `F subset G` be finite and `eps > 0`.
Since `Q` is amenable there is a finite `Phi subset Q` with
`|p(g)Phi triangle Phi| <= eps |Phi|` for all `g in F`.  For `g in F` and
`x in Phi` with `p(g)x in Phi` put

```text
c(g,x) = s(p(g)x)^(-1) g s(x)   in N,
```

the cocycle coordinate of `g` at `x`; `C subset N` denotes the finite set of
all these coordinates together with their pairwise products and inverses.
Because `N` has the factorization property, there is a u.c.p. map
`psi : C*(N) -> M_k` with `||psi(cc') - psi(c)psi(c')||_2 < eps` for
`c, c' in C` and `|tr psi(c) - delta_(c,e)| < eps` for `c in C`.
By Stinespring, `psi(a) = V^* sigma(a) V` for a unitary representation
`sigma` of `N` on a Hilbert space `K` and an isometry `V : C^k -> K`.

**Step 2 (induction).**  Let `pi = Ind_N^G sigma` act on
`ell^2(Q) tensor K` by

```text
pi(g)(delta_x tensor xi) = delta_(p(g)x) tensor sigma(s(p(g)x)^(-1) g s(x)) xi .
```

This is a unitary representation of `G` (the standard induced
representation written in the coordinates of the section `s`); for `g in N`
it acts diagonally by `sigma(s(x)^(-1) g s(x))`.

**Step 3 (compression).**  Let `P = 1_Phi tensor VV^*`, the projection onto
`ell^2(Phi) tensor V C^k`, identified with `C^Phi tensor C^k = M_(|Phi| k)`'s
underlying space.  Define the u.c.p. map

```text
Theta(a) = P pi(a) P   restricted to the range of P,   a in C*(G).
```

For `g in F` one reads off from Step 2 that

```text
Theta(g) = sum_(x in Phi, p(g)x in Phi) e_(p(g)x, x) tensor psi(c(g,x)).
```

**Step 4 (multiplicativity).**  For `g, g' in F` and `x in Phi` with
`p(g')x in Phi` and `p(gg')x in Phi`, the cocycle identity gives
`c(gg',x) = c(g, p(g')x) c(g',x)`.  Hence the `(p(gg')x, x)` block of
`Theta(gg') - Theta(g)Theta(g')` equals
`psi(c(g,p(g')x) c(g',x)) - psi(c(g,p(g')x)) psi(c(g',x))`, of `||.||_2`-norm
below `eps`, while the blocks with `p(g')x notin Phi` or `p(gg')x notin Phi`
number at most `2 eps |Phi|` and each has operator norm at most `1`.  Since
the blocks occupy distinct matrix positions,

```text
||Theta(gg') - Theta(g)Theta(g')||_2^2
   <= (1/|Phi|) ( |Phi| eps^2 + 2 eps |Phi| ) = eps^2 + 2 eps .
```

**Step 5 (trace).**  `tr Theta(g) = (1/|Phi|) sum_(x in Phi, p(g)x = x) tr psi(c(g,x))`.
If `g notin N` no `x` contributes, so `tr Theta(g) = 0 = tau_G(g)`.  If
`g in N` then `c(g,x) = s(x)^(-1) g s(x)`, which is `e` exactly when `g = e`,
so `|tr Theta(g) - delta_(g,e)| < eps`.

Letting `F` increase to `G` and `eps -> 0` gives the required models, and
Brown's Theorem 4.1.9 converts amenability of the canonical trace of `C*(G)`
into Kirchberg's factorization property for `G`.

When the extension splits and `sigma` is taken to be a finite quotient
representation of a finitely generated subgroup of `N`, Steps 2 to 5 are
exactly the window construction of `literal-fp-via-folner-rf-core`; the only
new point is that a section `s` and the cocycle `c` replace the action
`alpha`, so no crossed-product identification of `C*(G)` is needed.
