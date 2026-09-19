---
rg: 2
id: one-ended-root-killable-lamp-covers-have-torsion
kind: claim
title: Over a one-ended base with torsion, a lamp cover whose class dies once lamp roots are adjoined always has torsion, so algebraic root-untwisting never reaches a torsion-free cover
distinct_from:
  abelianized-cover-injective-corona-model-carries-nonzero-twist: that proves an injective model of E must carry a nonzero pushed twist class in the ANALYTIC coefficients U(C*(rho(M))); this localizes the vanishing of that class to spectral gaps in lamps, and proves that the algebraic way of making it vanish (a class killed by adjoining lamp roots) is incompatible with torsion-freeness over a one-ended base.
  free-abelianized-cover-is-torsion-free: that proves E is torsion-free for every presentation; this shows that the class xi of E has infinite order even rationally over a one-ended base, and that no torsion class over an induced-from-finite lamp module can give a torsion-free cover.
  torsion-free-central-cover-forces-abelian-finite-subgroups: that rules out torsion-free covers with CENTRAL kernel; this rules out torsion-free covers with induced-from-finite permutation-lattice kernel and TORSION class, with no hypothesis on the finite subgroups.
artifacts:
  - research/one-ended-root-killable-lamp-covers-have-torsion-proof.md
---

**ESTABLISHED** (proof in `one-ended-root-killable-lamp-covers-have-torsion-proof`).

**Setting.**  `G` is a finitely generated group.  `(C_i)_{i in I}` is a
family of nontrivial finite cyclic subgroups, `C_i = <s_i>` of order `m_i`.
The *lamp lattice* is the permutation module

```text
P = (+)_{i in I} Z[G/C_i]        (basis vectors e_i = the coset C_i in summand i).
```

A *lamp cover* is an extension `1 -> P -> Gamma -> G -> 1` (class
`c in H^2(G;P)`) together with lifts `t_i in Gamma` of `s_i` such that
`t_i^{m_i} = e_i`.  The *lamps* are the `Gamma`-conjugates of the `e_i`.
Let `D : P -> P` be the `G`-map that multiplies summand `i` by `m_i`, and
call `c` **root-killable** if `D_* c = 0`.  Equivalently, the pushout
`Gamma' = Gamma x_P P` along `D` (which adjoins an `m_i`-th root of every
lamp `e_i`, fixed by `C_i`) splits over `G`.

**(A) Root-untwisting.**  Suppose `Rad_MF(G) = G` and `c` is root-killable.
Let `rho : Gamma -> U(Q)` be any homomorphism into the unitary group of a
matrix corona `Q = prod M_(k_n) / (+) M_(k_n)`.  (More generally, `Q` can be
any unital C*-algebra such that every homomorphism `G -> U(Q)` is trivial.)
If every
`rho(e_i)` has spectrum different from the whole circle, then `rho(Gamma)`
is abelian.  In particular `rho` kills `[Gamma, Gamma]`, which contains
`[Gamma, P]`.

**(B) One-ended obstruction.**  Suppose `G` is one-ended, that is, its Cayley
graph has exactly one end.  Then every torsion class `c in H^2(G;P)`
satisfies

```text
Res_{C'} c = 0 in H^2(C'; P)     for every subgroup C' <= G of prime order.
```

The same holds when `P` is replaced by any `G`-direct summand of `P`.
Consequently, every element of prime order `p` in `G` lifts to an element of
order `p` in `Gamma`.  So **if `G` has torsion, no extension of `G` by a
summand of `P` with torsion class is torsion-free.**  A root-killable class
is componentwise torsion, since `D_* c = 0` forces `m_i (p_i)_* c = 0`
for the projection `p_i` to each summand, and that is all the argument
uses.  Hence every
root-killable lamp cover over a one-ended `G` with torsion has torsion.

**(C) Rational non-splitting of the relation cover.**  If `G = F/R` is
one-ended and infinite, `M = R/[R,R]` and `E = F/[R,R]`, then the class `xi`
of `E` has nonzero image in `H^2(G; M (x) S)` under `m -> m (x) 1`, for every
nonzero commutative ring `S`: for example `S = Q`, `Z[1/k]` or `Z/k`.  So
adjoining roots of the relation lattice, of any orders and all at once
(`S = Q`), never splits `E` over `G`.

**What this kills.**  Consider approaches to `full-mf-radical-abelianized-cover-is-not-mf`,
or to any torsion-free non-MF cover of a full-radical base, of the following
form:

1. build a torsion-free lamp cover `Gamma` (or a summand version) of `G`;
2. show that its class `c` is root-killable, so that a gapped model takes
   equivariant roots;
3. conclude by (A) that every gapped model is abelian, leaving only
   full-spectrum lamps to handle.

The invariant is the restriction `Res_{C'} c` to prime-order subgroups.
Over a one-ended base with torsion, such as `St_20(L_(F_2)(1,2))`, every
member dies at the junction of steps 1 and 2.
- Torsion-freeness forces `Res_{C'} c != 0` for every prime-order `C'`.
- By (B), a root-killable `c` has `Res_{C'} c = 0` for all of them.

Each step on its own is fine: (A) is proved, and torsion-free covers exist,
for example `E` itself.  What is impossible is the conjunction.

Any proof that such a cover is non-MF must therefore handle lamps whose
model spectra fill the whole circle ("odd winding"), or must use the
infinite-order part of the class.  (C) says the same for the relation cover
`E`: its class is not killed by any algebraic root extension.

`St_20(L_(F_2)(1,2))` is one-ended because it is infinite, finitely generated
and has Kazhdan's property (T).  Property (T) implies property (FA) (Watatani),
and a group with (FA) has no splitting over a finite subgroup, so by
Stallings' theorem it has at most one end.  This fact is used only to apply
the kill to that base.  It is not imported into any route of
`property-t-free-manuscript-results`.
