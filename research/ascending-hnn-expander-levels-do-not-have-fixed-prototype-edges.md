---
rg: 2
id: ascending-hnn-expander-levels-do-not-have-fixed-prototype-edges
kind: claim
title: Finite-index HNN expander levels cannot have fixed-prototype edge words
distinct_from:
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that proves unbounded endpoint correction for a two-transitive infinite orbit; this treats a bounded-neighbor tower of finite Schreier expanders with no two-transitivity assumption.
  ascending-hnn-cannot-create-nonhyperlinearity: that is a closure theorem for the bare HNN group; this identifies the quantitative occurrence-word failure inside the otherwise promising finite-index expander tower.
  finite-telescope-level-coset-orbits: that proves the level orbits are finite; this proves that their fixed-scale edges are not conjugates of one bounded prototype.
---

Let `K` be finitely generated, let `phi:K->K` be injective of finite index
`q>1`, and form

```text
V=<K,t | t k t^-1=phi(k)  (k in K)>.                            (HNE1)
```

If a base occurrence `a` is fixed by `K`, then

```text
a_n=t^n a t^-n
```

is fixed by `phi^n(K)` and its `K`-orbit is the finite Schreier level
`K/phi^n(K)`, of size `q^n` when the displayed stabilizer is exact.  If `K`
has property `(T)`, the Schreier graphs for a fixed generating set `S` are a
uniform expander family.

Nevertheless the fixed-scale edge from `a_n` to `s a_n s^-1`, `s in S`, is
not obtained by conjugating one fixed prototype edge.  Conjugating the base
edge by `t^n` replaces `s` by `phi^n(s)`, which lies in the stabilizer of
`a_n`; the alleged edge becomes a loop.  Conjugating the level-`n` edge back
to the base replaces `s` by `t^-n s t^n`, an unbounded scale-dependent word.

More invariantly, simultaneous conjugacy of an addressing subgroup and an
occurrence stabilizer preserves their index, whereas

```text
[K:phi^n(K)]=q^n.                                                (HNE2)
```

Thus the two attractive features of this tower split:

- stabilizer relations at depth `n` are conjugates of the base stabilizer
  relations;
- the fixed `S`-edges which give the expander gap are not conjugates of a
  finite depth-independent edge menu.

The tower therefore does not by itself close the finite-orbit occurrence
Pauli compiler.  A successful use needs a new bounded scale-conversion cell
which controls the words `t^-n s t^n`, or a different finite-template
expander architecture.

