---
rg: 2
id: transitive-controller-orbit-common-twist-preserves-zero-lcu
kind: claim
title: A transitive controller orbit turns all orientation errors into one harmless LCU factor
distinct_from:
  finite-symmetry-equivariant-edge-has-one-holonomy: that proves one equivariant edge has one multiplicity holonomy over its symmetry orbit; this computes the resulting LCU zero test.
  grading-zero-corner-does-not-orient-controlled-payload: that treats unrelated controlled gates with independent orientations; this shows that a genuinely common orientation need not be chosen at all.
  tailored-checks-to-common-marked-group-extensions: that must compile arbitrary verifier words on one decoded strategy; this applies only after their controllers have been realized as one finite symmetry orbit.
---

**ESTABLISHED.**  Let a finite group `H` act transitively on a finite label
set `I`.  Suppose one `H`-equivariant controller edge has, on a marked exact
packet carrier, the representation form

```text
B_i=C_i tensor V,             i in I,                  (TCO1)
```

where the `C_i` are the intended label/payload operators and `V` is the one
common multiplicity unitary supplied by
`finite-symmetry-equivariant-edge-has-one-holonomy`.  If
`q=q_0 tensor I` is the authenticated LCU corner, then for scalars `a_i`

```text
q (sum_i a_i B_i) q
  = (q_0 (sum_i a_i C_i) q_0) tensor V.                (TCO2)
```

Consequently the left side vanishes exactly when the intended LCU
compression vanishes.  More quantitatively, tensoring by `V` preserves
normalized Hilbert--Schmidt norm, so a fixed-orbit approximate realization
with controller errors at most `eta` changes the LCU compression by at most

```text
(sum_i |a_i|) eta.                                     (TCO3)
```

Thus orientation synchronization is strictly weaker than orientation
selection: for a zero-compression verifier a common spectator factor is
harmless.

## Exact boundary

Transitivity is useful only when the **intended controllers themselves** are
one `H`-orbit.  Conjugating the controller covariance relation transports
its payload word as well.  For arbitrary verifier words `w_i`, imposing

```text
h_i w_0 h_i^-1=w_i                                    (TCO4)
```

adds a unitary-equivalence symmetry not satisfied by a general perfect
strategy.  Replacing the one payload by independently renamed orbit copies
restores exact completeness, but then the LCU terms are evaluated on
different strategies and no longer form the original losing polynomial.

Hence finite transitive control removes the multiplicity-orientation wall
for orbit-symmetric checks.  It does not by itself turn an arbitrary LCU
menu into such an orbit; that remaining operation is precisely shared-payload
holonomy/coherent-oracle groupification, not another spectator-gauge issue.

## Cyclic inner-HNN hostile test

The standard clock trick does not manufacture the missing symmetry.  Put
copies of one payload representation `pi` on clock fibers `K_i`, and ask one
clock letter `T` to carry `K_i` to `K_(i+1)` while implementing the inner
edge map `Ad(w_i)`.  Writing its edge block as `T_i:K_i->K_(i+1)`, covariance
gives

```text
pi(w_i)^* T_i in pi(Gamma)',
T_i=pi(w_i)V_i,             V_i in pi(Gamma)'.          (TCO5)
```

For the uniform clock projection `q_unif`, therefore,

```text
q_unif T q_unif
  =(1/|I|) sum_i pi(w_i)V_i.                            (TCO6)
```

The cycle return constrains only the ordered product of the `V_i` (up to
the payload holonomy).  Even for irreducible `pi`, there remain `|I|-1`
independent scalar phases.  Thus `(TCO6)` is not the desired LCU sum.

Adding a rotation which commutes with the whole edge cell does identify the
`V_i`, but conjugating the covariance rows then identifies the edge maps as
one symmetry orbit too.  This recovers `(TCO1)` exactly when the `w_i` already
satisfy `(TCO4)` and otherwise imposes new payload relations.  The clock
construction therefore restates, rather than solves, the common-orientation
holonomy problem.
