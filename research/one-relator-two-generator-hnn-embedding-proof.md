---
rg: 2
id: one-relator-two-generator-hnn-embedding-proof
kind: route
title: Shift the Magnus free bases through one stable letter
target: one-relator-two-generator-torsion-spectrum-embedding
requires: [hnn-torsion-orders-equal-base-torsion-orders]
---

Let

```text
G = <x_1,...,x_n | r>
```

with `r` nontrivial and cyclically reduced. Assume first `n>=2`. Arrange
that both `x_1` and `x_n` occur in `r`. If its support has at least two
letters, relabel two occurring letters as the endpoints. If its support is
only `x_1`, then `r=x_1^m`; the Nielsen basis

```text
y_1=x_1*x_n^(-1),  y_n=x_n
```

changes the relator to `(y_1*y_n)^m`, so after renaming it involves both
endpoints.

Magnus' Freiheitssatz makes

```text
A=<x_1,...,x_(n-1)>  and  B=<x_2,...,x_n>
```

free on the displayed bases. Hence `x_i |-> x_(i+1)` is an isomorphism
`A->B`. Form the HNN extension

```text
H = <G,t | t^(-1)x_i t=x_(i+1), 1<=i<n>.
```

Britton normal form embeds `G`. Eliminating `x_2,...,x_n` gives the
two-generator one-relator presentation

```text
H = <x,t | r(x,t^(-1)xt,...,t^(-(n-1))x t^(n-1))>.
```

The substituted relator is nontrivial: the conjugates
`{t^(-j)x t^j:0<=j<n}` lie in the standard free basis of the kernel of
`F(x,t)->Z`, so substitution is injective on the original free group.

Every finite-order element of an HNN extension is conjugate into its vertex
group. The reverse inclusion of torsion orders follows from the embedded
copy of `G`. Thus
[[hnn-torsion-orders-equal-base-torsion-orders]] gives
`Tord(H)=Tord(G)`.

For `n=1` and nontrivial relator `x^m`, use
`H=G*Z=<x,t|x^m>`; torsion in a free product is conjugate into a factor,
so the torsion-order set is again unchanged. If trivial relators are admitted,
replace `<X|1>` by the genuine one-relator presentation `<X,z|z>` before
the construction (and use `Z^2=<x,t|[x,t]>` in the one-generator free
case).

This is the classical Magnus embedding recorded in
Magnus--Karrass--Solitar, *Combinatorial Group Theory*, Corollary 4.10.1,
with the torsion-spectrum conclusion supplied by the HNN torsion theorem.
QED
