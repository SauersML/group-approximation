---
rg: 2
id: relator-width-bounded-over-simple-iterated-wreath-products
kind: claim
title: A finitely presented group with no finite quotient has depth-uniform relator width over iterated wreath products of nonabelian simple transitive groups
distinct_from:
  simple-nonsofic-relator-width-over-iterated-wreath-products: that asks for the depth-uniform bound for simple nonsofic groups over towers of arbitrary transitive groups, including solvable ones; this proves it when every vertex group is nonabelian simple, for every finitely presented group without finite quotients, with no soficity hypothesis.
  simple-nonsofic-width-over-bounded-base-symmetric-wreath: that treats depth two with the full symmetric top and needs nonsoficity; this treats every depth with small simple tops and needs only no finite quotient.
  relator-width-over-nilpotent-by-locally-finite-groups: that covers nilpotent kernels over bounded tops; these towers have trivial Fitting subgroup and are covered by neither.
---

**ESTABLISHED** through `relator-width-bounded-over-simple-iterated-wreath-products-proof`. Its
prerequisite `iterated-simple-wreath-bounded-commutator-width` rests on Nikolov--Segal and
Lucchini--Menegazzo, both of which use the classification of finite simple groups. Unreviewed.

Let `G = <X | R>` be a finitely presented group with no nontrivial finite quotient. For a finite group
`Q` and `a in Q^X`, `w_Q(a)` is the least `K` such that every generator `a_x` is a product of at most
`K` `Q`-conjugates of relator values `r(a)^(+-1)`.

**Theorem.** Fix `m`. Let `W = T_1 wr T_2 wr ... wr T_d` be an iterated permutational wreath product
acting on a rooted tree, with every vertex group `T_i <= Sym(m_i)`, `m_i <= m`, transitive and
nonabelian simple. Let `c(m)` bound the commutator width of all such towers
(`iterated-simple-wreath-bounded-commutator-width`). Then
```text
w_W(a)  <=  max_x sum_r |n_(x,r)|  +  2 |R| ( m! + m - 1 + 2 c(m) )
```
for every depth `d` and every `a in W^X`. Here `n_(x,r)` are fixed integers with
`e_x = sum_r n_(x,r) e_r`. Moreover one fixed word in `R^(+-1)` serves every `d` and every `a` as a
template, with conjugators depending on `a`.

**Consequences.**
- **No weak models in simple towers.** A finitely presented simple group (sofic or not) has no weak
  models, with any bi-invariant lengths, in iterated wreath products of nonabelian simple groups of
  bounded degree. For the binary Leavitt unit group this settles the non-nilpotent-top deep wreath
  family of `fg-simple-weakly-sofic-groups-are-sofic` when every vertex group is simple.
- **Nonsoficity is not needed here.** The obstruction comes from perfection of the tower and the
  absence of finite quotients of `G`, not from any soficity input.
- **Solvable layers are what remain.** Interleaved abelian layers remain open inside
  `simple-nonsofic-relator-width-over-iterated-wreath-products`, for example `C_2 wr Alt(5) wr C_3 wr ...`.

**Mechanism.**
- **Top reduction.** The lowest level at which `<a>` acts is the lowest at which some relator value
  acts. So `a` lies in a level stabilizer, which is a direct product of subtree groups. A balanced
  template is valid coordinatewise, so it suffices to treat tuples acting at the root of `H wr T`,
  with `H` the subtree group.
- **Top covering.** Some `r*(a)` has a nontrivial root label `tau`. The balanced block `(r* r*^-1)^(|T|)`
  covers `T`, because `C C^-1` generates `T` for the class `C` of `tau`.
- **Base.** The error lies in `H^m`. Dipoles `[(h at i; 1), (1; pi) r*(a) (1; pi)^-1]` along a spanning tree
  of the connected graph `{i, sigma(i)}`, `sigma in C`, solve every coordinate but one, using `m - 1`
  pairs. The last coordinate carries an arbitrary `z in H = [H, H]`, which is a product of `c(m)`
  commutators. Each commutator `[k, l]` at `i` is the nested commutator
  `[[(k at i; 1), L], (l at i; 1)]`, four letters, with `L` a conjugate of `r*(a)` moving `i`.
