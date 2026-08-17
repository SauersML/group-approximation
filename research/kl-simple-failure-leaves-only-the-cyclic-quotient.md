---
rg: 2
id: kl-simple-failure-leaves-only-the-cyclic-quotient
kind: claim
title: Over a nonabelian simple group a Kervaire--Laudenbach failure leaves exactly the cyclic quotient
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Fix `m != 0`, let `pi_m : G * <t> -> C_m` kill `G` and send `t` to a
generator, and let

    N_m  =  ker pi_m  =  { x in G * <t>  :  m divides deg_t(x) } ,

a description independent of which generator `t` is sent to.

**(a) Simple case.**  Let `S` be nonabelian simple, `w in S * <t>` with
`deg_t(w) = m != 0`, and `H = (S * <t>)/<<w>>`.  If `S -> H` is not
injective then

    H  =  C_|m|      and      <<w>>_{S*<t>}  =  N_m .

So over `S` the conjecture is exactly: no `w in N_m` of exponent sum `m`
normally generates `N_m` in the ambient group.  At `m = ±1` this is the
classical statement that `S * Z` does not have weight one.

**(b) The converse direction needs no simplicity.**  For **any** nontrivial
group `G` and any `w in N_m` with `deg_t(w) = m`, if `N_m = <<w>>_{G*<t>}`
then `G_w = (G * <t>)/N_m = C_m`, every element of `G` dies, and `(G, w)` is
a counterexample.

## Why (b) is stated separately

The external audit states the equivalence only for simple coefficient groups,
where it is an equivalence.  Direction (b) is what the falsification lane
actually needs, and it holds for every nontrivial group — in particular for
the binary Leavitt unit group, which this repository knows to be perfect
(`leavitt-gl-equals-el-and-perfect-unit-group`) but does not know to be
simple.  Recorded as `leavitt-kl-violation-via-total-cyclic-collapse`.

## What the rigidity rules out

An "accidental" counterexample, in which one unlucky coefficient relation
happens to hold.  Over a simple coefficient group there is no such thing: a
single relative relator either injects the whole group or annihilates it.
Any proposed violation must therefore be checked against a total-collapse
requirement, not against the death of one element — which is a far stronger
demand on a candidate word, and the reason a large finite list of relators
over a chart group is not evidence of anything.
