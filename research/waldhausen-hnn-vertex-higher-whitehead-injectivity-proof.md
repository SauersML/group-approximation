---
rg: 2
id: waldhausen-hnn-vertex-higher-whitehead-injectivity-proof
kind: route
title: Use the constant Nil coordinate in the full HNN Whitehead-space fibration
target: waldhausen-hnn-vertex-higher-whitehead-injectivity
requires: []
---

Remark 3 after Corollary 17.2.3 of Waldhausen, *Algebraic K-theory of
generalized free products, Part 2*, Ann. of Math. (2) 108 (1978), 205--256,
DOI 10.2307/1971166, gives in the general HNN case a sequence of the
homotopy type of a fibration

```text
Omega BQ(Nil) x Wh_Z(L) -> Wh_Z(V) -> Wh_Z(H)^*.
```

The displayed map from the Nil factor is literally labelled `pt`; it is
constant. The other coordinate factors through `Wh_Z(L)`. If
`Wh_Z(L)` is contractible, the first arrow induces zero on every homotopy
group.

Exactness therefore makes

```text
pi_i Wh_Z(V) -> pi_i Wh_Z(H)^*
```

injective for every `i>=0`. Degree zero is included: Definition 15.4
defines these Whitehead spaces as loop spaces, the displayed fibration is
obtained after passing to loop spaces, and its degree-zero homotopy sequence
is an exact sequence of groups.

Remark 2 after Corollary 17.1.3 explains the star notation: the starred
space is a union of components of the ordinary Whitehead space; the HNN
statement uses the same notation. Its inclusion into `Wh_Z(H)`
is an isomorphism on based homotopy groups in positive degrees and injective
on components. The composite into `Wh_Z(H)` is therefore injective on
every `pi_i`, `i>=0`. QED
