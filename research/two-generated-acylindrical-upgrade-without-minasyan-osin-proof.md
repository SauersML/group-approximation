---
rg: 2
id: two-generated-acylindrical-upgrade-without-minasyan-osin-proof
kind: route
title: Re-amalgamate the two-generated overgroup over a fixed malnormal rank-4 subgroup of F(a,b) and read acylindricity off the tree
target: two-generated-acylindrical-upgrade-without-minasyan-osin
requires:
  - amalgam-torsion-permanence-needs-no-cyclic-reduction
  - malnormal-edge-amalgam-tree-action-is-acylindrical
artifacts:
  - experiments/malnormal-edge-router-2026-09-17/search_malnormal.py
  - research/two-generated-acylindrical-normal-generation-upgrade-proof.md
---

## Tools

(AM), (TF), (NF) and (FP) are as in
`two-generated-acylindrical-normal-generation-upgrade-proof`.

* (AM): the factors of an amalgam embed.
* (TF) is `amalgam-torsion-permanence-needs-no-cyclic-reduction`.
* (NF): normal forms in free products and in free groups.
* (FP): an amalgam of finitely presented groups over a finitely generated
  subgroup is finitely presented.

(ACYL) is `malnormal-edge-amalgam-tree-action-is-acylindrical`.

Two finite computations are run by
`experiments/malnormal-edge-router-2026-09-17/search_malnormal.py`, whose
default mode prints `VERIFIED`:

* **(MAL)** the Stallings graph of `C' = <a, y_1, y_2, y_3>` in `F(a,b)`, with
  `y_1 = b a^2 b^2`, `y_2 = b a b a^{-1} b` and `y_3 = b^3 a b^{-1}`.  It has
  8 vertices and 11 positive edges, so rank `4`, and the four words are a
  free basis.  There is no closed `b`-path at the base, so `b notin C'`.  `C'`
  is malnormal by the Kapovich--Myasnikov criterion: every off-diagonal
  component of the pullback `Γ x Γ` is a tree.  A brute-force search over all
  conjugators of length `<= 6` agrees.
* **(TC)** `G_0 = <t,b | t^{-1} b t^8 b^2, t^{-2} b t^4 b t^{-4} b, t^{-3} b^3 t^4 b^{-1}>`
  has order `1`.  This is Todd--Coxeter enumeration over the trivial subgroup,
  also over `<b>` and `<t>`.  The enumerator is first validated on `Z_2^2`,
  `S_3`, `S_4`, `A_5`, `PSL(2,7)` and `Z_31 x| Z_18`.  SymPy's
  `coset_enumeration_r` gives the same answer when installed.

The edges of the Stallings graph, with base `0`, are:
`0-a->0`, `0-b->1`, `1-a->6`, `6-a->3`, `3-b->4`, `4-b->0` (reading `y_1`);
`6-b->7`, `4-a->7` (reading `y_2 = b·a·b·a^{-1}·b` through `0,1,6,7,4,0`);
and `1-b->10`, `10-b->11`, `11-a->1` (reading `y_3` through `0,1,10,11,1,0`).
The graph is folded: no vertex has two outgoing edges with the same label.

## Step 1: the first amalgam (no acylindricity needed)

Steps 0--5 of `two-generated-acylindrical-normal-generation-upgrade-proof` use
only (AM), (TF), (NF) and (FP).  Minasyan--Osin enters only at its Step 6.
They give an injection `P -> Q_1` with the following properties:

* `Q_1 = (P*<s>) *_C F(a,b)` is finitely presented and torsion-free;
* `Q_1 = <s,c>`, where `c` is the free generator called `b` there;
* `normalClosure_{Q_1}(P) = Q_1`.

Also `s notin C` and `c notin C` (Claims 1 and 2 there).

## Step 2: three distinct nontrivial elements

Put `r_1 = s`, `r_2 = c` and `r_3 = sc`.  These are nontrivial, because
`s in P*<s>` and `c in F(a,b)` are nontrivial and the factors embed.  If
`s = c`, then `s in (P*<s>) cap F(a,b) = C`, which contradicts `s notin C`.
Finally `sc ≠ s` since `c ≠ 1`, and `sc ≠ c` since `s ≠ 1`.

## Step 3: the free subgroup `C_1 <= A' = Q_1 * <t>`

Put `x_0 = t^4` and `x_k = r_k t^k` (`k=1,2,3`), and `C_1 = <x_0,...,x_3>`.

**Claim 3.**  The `x_i` freely generate `C_1`, and `t, t^2 notin C_1`.

*Proof.*  This is Claim 1 of the first proof verbatim, with `m=3`, `N=4`,
`P` replaced by `Q_1` and `p_k` by `r_k`.  That argument uses only that the
`p_k` are pairwise distinct and nontrivial, and that `0<k<N`.  A reduced word
containing some `x_k^{±1}` with `k>=1` has a nontrivial `Q_1`-syllable, while
`x_0^n = t^{4n}` is neither `t` nor `t^2`.  ∎

## Step 4: the second amalgam

By Claim 3 and (MAL), `x_0 |-> a` and `x_k |-> y_k` define an isomorphism
`C_1 -> C'`.  Put

```text
Q_2 = A' *_{C_1 = C'} F(a,b)
    = < Q_1, t, a, b | t^4 = a,  s t = b a^2 b^2,  c t^2 = b a b a^{-1} b,  sc t^3 = b^3 a b^{-1} >.
```

* `P -> Q_1 -> A' -> Q_2` is injective, by (AM).
* `Q_2` is torsion-free by (TF), since `A' = Q_1 * <t>` and `F(a,b)` are
  torsion-free.
* `Q_2` is finitely presented by (FP).

## Step 5: `Q_2 = <t,b>`

`a = t^4`, so `F(a,b) <= <t,b>`.  Then `r_k = y_k t^{-k} in <t,b>`, which
gives `s = r_1` and `c = r_2`, so `Q_1 = <s,c> <= <t,b>`.  Since `Q_1`, `t`,
`a` and `b` generate `Q_2`, `Q_2 = <t,b>`.  ∎

## Step 6: `normalClosure_{Q_2}(P) = Q_2`

`N := normalClosure_{Q_2}(P)` contains `normalClosure_{Q_1}(P) = Q_1`.  So
`Q_2/N` is a quotient of `Q_2/normalClosure(Q_1)`.  Adding `Q_1 = 1` to the
display of Step 4 kills every `r_k`.  Eliminating `a = t^4` then leaves the
presentation `G_0` of (TC), so `G_0 = 1` and `N = Q_2`.  ∎

A consistency check: the relation matrix of `G_0^{ab}` has rows `(-7,-3)`,
`(2,-3)` and `(-1,-2)`.  Its `2x2` minors are `27`, `11` and `-7`, with gcd `1`.

## Step 7: acylindrical hyperbolicity

Apply (ACYL) to `Q_2 = A' *_{C'} F(a,b)`.

* `C'` is malnormal in `F(a,b)`, and `C' ≠ F(a,b)` because `b notin C'` (MAL).
* `t in A'` satisfies `t, t^2 notin C_1` (Claim 3).

So `Q_2` acts acylindrically on its Bass--Serre tree, and `tb`, `bt` are
independent loxodromics.  `Q_2` is acylindrically hyperbolic.  ∎

## Conclusion and effect on the route

`Q_2` has everything `two-generated-acylindrical-normal-generation-upgrade`
delivers: two generators, a finite presentation, no torsion, acylindrical
hyperbolicity, and normal generation by `P`.  None of it uses an imported
acylindricity theorem.  In
`property-t-free-torsion-free-via-embedding-router`, the chain `(EMB)`
followed by this lemma and then `mf-radical-saturation-along-any-homomorphism`
imports nothing from the literature except the seed.

The remaining trust debt is the two machine computations.  (MAL) is a
bounded graph search on 64 vertex pairs.  (TC) is a Todd--Coxeter run; for
Lean, it needs a certificate, meaning an explicit product of conjugates of the
three relators equal to `t` and to `b`.
