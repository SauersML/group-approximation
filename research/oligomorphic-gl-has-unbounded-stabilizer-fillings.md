---
rg: 2
id: oligomorphic-gl-has-unbounded-stabilizer-fillings
kind: claim
title: Oligomorphic GL Pauli addressing has unavoidable stabilizer filling loss
distinct_from:
  finitely-presented-oligomorphic-linear-pauli-addresser: that constructs the finite presentation, the common sign, and all finite Pauli ranks; this proves why its finite tuple-orbit relations do not have uniform normalized-HS cost for globally named questions.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that gives the abstract two-role section obstruction; this identifies its concrete infinite centralizing stabilizer in the finitary-linear Pauli semidirect product and applies the stronger filling-area theorem.
  colored-cayley-pauli-incidence-separation: that avoids global sections by using actual bounded-neighbor Cayley addresses; this rules out the direct dense oligomorphic-orbit shortcut and leaves that bounded-neighbor placement route intact.
---

Let `V=F_2^(X)` and let the finitary linear group act on the Pauli extension

```text
P(V)=<X_v,Z_phi,J | [X_v,Z_phi]=J^(phi(v)), ...>.
```

The oligomorphic envelope from
`finitely-presented-oligomorphic-linear-pauli-addresser` is finitely
presented, contains every finite-rank Pauli group with the same `J`, and has
the exact Schrodinger model on `ell^2(V)` with `J=-I`.  Moreover bounded
vector/covector tuples have finitely many actor orbits: linear-dependence
kernels and pairing matrices classify them.  Thus the proposed actor solves
the algebraic orbit-enumeration and exact marked-model problems.

It does not give uniform HS query names.  Fix `e!=0`, put `x=X_e`, and let

```text
H=Stab(e).
```

The group `H` is infinite and every element of it centralizes the finite-
order word `x`.  Choose any section `t_v` with `t_v e=v` and globally name

```text
x_v=t_v x t_v^(-1).                                    (OGS1)
```

If a prototype occurrence is transported contextually by `g`, comparison
with `(OGS1)` inserts

```text
h=t_v^(-1)g u in H                                     (OGS2)
```

for the appropriate prototype endpoint `u`.  Replacing the contextual word
by the global name is exactly a conjugate of `[h,x]`.

By `bounded-centralizer-fillings-force-finite-stabilizer`, for every finite
presentation of the ambient group and every choice of representative words,

```text
sup_(h in H) Area([h,x])=infinity.                      (OGS3)
```

Hence finite generation of `H`, finite tuple-orbit count, or even a finite
list of stabilizer relators cannot make the contextual-to-global transfer
dimension independent.  For simultaneous BLR/Weyl pair transports,
`two-transitive-occurrence-sections-have-unbounded-pair-holonomy` further
shows that the two endpoint corrections cannot both remain in bounded word
balls.

There is an independent semantic firewall.  One may choose the
oligomorphic envelope amenable, so the full Pauli semidirect product is
amenable and hyperlinear while `J` remains nontrivial in the exact
Schrodinger model.  If its five BLR/Weyl tuple orbits really supplied global
words with uniformly bounded relation area, then
`literal-blr-weyl-metapixel-is-nonhyperlinear` would make this amenable group
nonhyperlinear.  Thus some uniform transfer must fail, and `(OGS3)` locates
it exactly.

Gauge-covariant payloads do not remove this syntactic issue.  A nonlocal
game may keep separate contextual occurrences and test their consistency,
but its strategy still assigns one fixed PVM to each repeated question.
Degree-reducing those occurrence equalities replaces the dense orbit by
growing expander clouds.  Actual Cayley addresses can give bounded
consistency edges without sections, as in
`fp-cayley-expanders-give-bounded-occurrence-edges`; the remaining typed
row/column and sign placement is precisely
`colored-cayley-pauli-incidence-separation`.

Therefore a finite-support GL or Thompson-style oligomorphic envelope does
not close `uniform-halting-pauli-word-oracle`.  The surviving route must use
section-free bounded-neighbor occurrence geometry, or an analytic
exactification theorem stronger than van Kampen transport.  The direct
claim that dense Pauli queries are conjugates of finitely many prototypes is
insufficient.
