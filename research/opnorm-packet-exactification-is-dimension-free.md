---
rg: 2
id: opnorm-packet-exactification-is-dimension-free
kind: claim
title: Operator-norm approximate matrix-unit packets exactify onto a common carrier with a dimension-free modulus
distinct_from:
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that begins after both packets are already exact on one projection and computes the rank consequence; this is the step that produces those exact packets and that common projection from operator-norm-approximate data, and is the reason the exactification clause is not an extra analytic hypothesis.
  opnorm-leavitt-coarse-fine-return-row: that asks the Leavitt relators to RECOVER an approximate coarse/fine packet pair with approximately equal identities and to control the return row; this only rounds such a pair, once recovered, to exact packets on one carrier -- the free half of that node's clause 2.
  finite-group-opnorm-support-profile: that stabilizes the support profile of a fixed finite-GROUP operator-norm model across coordinates; this rounds an approximate system of matrix units to an exact one inside a single coordinate, with no group and no profile.
  low-gap-witness-spike-or-balanced-cut: that clips an operator-norm witness inside an optimization to isolate a vanishing-rank obstruction; this perturbs a fixed finite relation set to its exact solution set and involves no optimization.
---

**ESTABLISHED.**  Fix `r>=1`.  There is a modulus `eps_r(delta) -> 0` as
`delta -> 0`, **depending only on `r`** -- not on the ambient matrix
dimension `d`, not on any trace, and not on any density -- such that the
following holds.

Let `(E_ij)_(i,j<=r)` in `M_d(C)` be a `delta`-approximate system of matrix
units:

```text
||E_ij^*-E_ji||<=delta,
||E_ij E_kl - [j=k] E_il||<=delta.                        (EXA1)
```

Then there is an **exact** system `(e_ij)_(i,j<=r)` of matrix units in
`M_d(C)` with

```text
||e_ij-E_ij||<=eps_r(delta)  for all i,j,                 (EXA2)
```

and its identity `P=sum_i e_ii` is nonzero as soon as `||E_11||>1/2`; in that
case `r` divides `rank(P)` and `rank(P)>=r`.

**Common carrier.**  If `(F_ab)_(a,b<=s)` is a second `delta`-approximate
system with

```text
||sum_i E_ii - sum_a F_aa||<=delta,                        (EXA3)
```

then after conjugating the exactified fine system by a unitary `u` with
`||u-1||<=eps_(r,s)(delta)` the two exact systems have one and the same
identity `P`, and `s` divides `rank(P)`.

## Why this is worth a node

It **discharges clause 2** of
`authenticated-coarse-fine-return-forces-mf-collapse`.  The audit that
proposed that theorem listed "one may operator-norm exactify the fixed packet
on a nonzero carrier" as a hypothesis.  It is not a hypothesis: the
matrix-unit relations are a finite relation set on finitely many variables
with a dimension-free stability modulus, so the exactification is free
whenever the approximate packet is in hand, and the perturbation adds only
`O(eps)` to the return row of `(ROW8)` by fixed-word telescoping.

The credit is standard and the node does not rest on it: this is Glimm's
matrix-unit perturbation lemma (Glimm, *On a certain class of operator
algebras*, Trans. Amer. Math. Soc. **95** (1960) 318--340), equivalently the
semiprojectivity of finite-dimensional C*-algebras (Loring, *Lifting
Solutions to Perturbation Problems in C\*-Algebras*, Fields Institute
Monographs 8, 1997).  The route gives the finite-dimensional argument in
full, so nothing downstream is conditional on the citation.

## Exactly what remains open, and it is not this

Two things are needed to feed
`authenticated-coarse-fine-return-forces-mf-collapse`, and only the second is
supplied here:

* **recovery** -- the relators must produce approximate coarse and fine
  packets at all, with approximately equal identities `(EXA3)`;
* **exactification** -- rounding those to exact packets on one carrier.

`(EXA3)` is the load-bearing half and it is an **additive** statement.  In the
Leavitt ring both packets sum to the active identity `A`; in a Steinberg/root
presentation coefficient addition is encoded as multiplication inside a root
subgroup and never as an operator sum, so no relator can say
`sum_i e_ii = sum_a f_aa`.  That is the same firewall recorded by
`factoriality-does-not-finitize-leavitt-root-data`,
`finite-root-algebra-forces-steinberg-triviality` and
`complex-hyperlinear-leavitt-idempotent-mismatch`, and `rectangular-escape`
is precisely the model in which the two identities differ by trading label
dimension against spectator multiplicity.  Recovering `(EXA3)` is therefore
the content of `opnorm-leavitt-coarse-fine-return-row`.
