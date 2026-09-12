---
rg: 2
id: elementary-abelian-harris-lift-compiles-bcs-consistency
kind: claim
title: An elementary-abelian Harris lift compiles all BCS consistency rules to phase-label equality
distinct_from:
  harris-bisynchronous-game-algebra-preservation: that uses a cyclic regular action on an arbitrary common answer alphabet and preserves the whole game algebra; this chooses the Boolean translation group so overlap consistency becomes an explicit equality of source and target pair labels.
  finite-phase-monomial-game-algebra-dictionary: that identifies games already defined by one monomial intertwiner; this computes the part of a BCS acceptance tensor which has exactly that finite-gain equality form.
  finite-predicate-signed-permutation-sector: that realizes an arbitrary local predicate inside one selected finite-group irreducible; this compiles shared-variable consistency uniformly but leaves local predicate validity uncompiled.
  harris-circulant-one-matrix-compiler-forces-affine-support: that proves a direct one-matrix Harris compiler can retain only affine full answer supports; this identifies the positive affine component, namely overlap consistency, before the nonlinear local-support obstruction is encountered.
---

**ESTABLISHED PARTIAL COMPILER.**  Let the variables of a finite BCS be
contained in `V=F_2^q`.  For each context `c`, use a PVM

```text
(e_(x,c))_(x in V),
```

with `e_(x,c)=0` unless `x` is supported on the variables of `c` and
satisfies its local predicate.  Put source and target vertices `(r,c)` and
`(a,c)`, respectively, for `r,a in V`, and define

```text
p_((a,c),(r,d))=delta_(c,d)e_(a-r,c).                  (EAH1)
```

Then `p` is a magic unitary, and `e_(x,c)=p_((x,c),(0,c))`; hence this is the
elementary-abelian version of the Harris square completion.

For contexts `c,d`, let `pi_(cd):V->F_2^(U_c intersection U_d)` be overlap
restriction.  The decoded answers `x=a-r` and `y=b-s` are consistent exactly
when

```text
pi_(cd)(r-s)=pi_(cd)(a-b).                             (EAH2)
```

Thus every shared-variable consistency rule is equality of one finite source
pair label and one finite target pair label.  In the `s=1` weighted
quantum-isomorphism case, encode the finitely many labels by distinct scalar
matrix entries.  For general finite `s`, choose the scalar entries in
distinct `mu_s`-orbits (for example, distinct positive magnitudes).  Then the
rule `alpha A_(ij)=beta B_(kl)` holds exactly when the overlap labels match
and the two output phases agree.  This puts every consistency row in the
monomial-isomorphism syntax of
`finite-phase-monomial-game-algebra-dictionary`.

Using distinct `s`-th roots themselves would **not** work: all nonzero roots
lie in one `mu_s`-orbit, and the answer phases can absorb their ratios.

This does not compile local predicate validity.  If the zero relations
`e_(x,c)=0` for rejecting `x` are omitted, any global Boolean assignment
`x in V` gives the classical translation permutation

```text
(r,c) |-> (r+x,c),                                    (EAH3)
```

which preserves every overlap label `(EAH2)`, whether or not `x` satisfies
the context predicates.  Therefore the remaining
`bisynchronous-to-monomial-game-algebra-compiler` problem is not
cross-context synchronization: it is a finite monomial gadget which kills
the rejecting translations while preserving the non-CE tracial algebra (up
to a full corner or trace-preserving Morita equivalence).
