---
rg: 2
title: STW X(1) amenable-versus-quasidiagonal trace frontier (2026-08-30)
kind: artifact
---

# Status and primary-source screen

STW Problem X(1) asks whether every amenable trace on a C*-algebra is
quasidiagonal.  A primary-source search through 30 August 2026 found no
general solution or counterexample.  The full-group-algebra candidate already
in the graph remains conditional: its canonical trace is proved non-QD, but
amenability still requires the literal group's open factorization property.

The main positive sources remain Brown's foundational memoir
arXiv:math/0304009v2, Tikuisis--White--Winter and Gabe for separable exact UCT
algebras, and Gabe's cone theorem.  Neagu, arXiv:2211.01666, proves homotopy
invariance in a separable exact faithful-amenable setting.  Shulman,
arXiv:2508.00125 (31 July 2025), proves a newer homotopy-domination theorem:
if either `A` or `B` is exact, `A` is homotopy dominated by `B`, and all
amenable traces on `B` are QD, then the same holds for `A`.  None of these
sources claims the universal assertion.

# New local permanence

`directed-unions-preserve-trace-approximations` proves that amenability and
quasidiagonality of a trace are each equivalent to the same property on every
member of a unital directed dense family.  The proof extends a stage u.c.p.
map to the ambient algebra and tracks finite-set errors; it does not assume
exactness.  Applied to full group algebras, this makes both Kirchberg's
factorization property and QD of the canonical full-group trace finitely
local.

The contrapositive recovers the separable reduction: an amenable non-QD trace
restricts to an amenable non-QD trace on some separable unital subalgebra.

# GNS kernels and quotient boundary

For exact `A`, the GNS quotient `A -> A/ker(pi_tau)` is locally liftable, so
amenability descends to the induced faithful trace; QD of that faithful trace
pulls back by composition.  This is the precise faithful-trace reduction used
by STW.  It does **not** say that a QD trace on `A` descends to its GNS image.

Nonexactness permits genuine failure of amenability descent.  If `G` is
nonamenable and has the factorization property, the canonical trace is
amenable on `C*(G)` but not on `C*_r(G)`.  Hence the regular quotient is not
locally liftable.  The free group `F_2` gives an unconditional example: its
residual-finiteness approximations make the full canonical trace QD, while an
amenable reduced canonical trace would give a left-invariant mean on `G`.

This phenomenon is a fence, not a counterexample to X(1): the full canonical
trace of `F_2` is QD.  It explains why quotienting an amenable trace to its
faithful GNS image is illegitimate without exactness or a lifting hypothesis.

# Ideal localization

For an ideal `I triangleleft A`, its central support in `A**` splits a trace
into an ideal-supported component and a component vanishing on `I`.
Amenability of both components follows from the fact that amenable traces form
a face.  Since QD traces are convex, an amenable non-QD trace must have an
amenable non-QD component on at least one side of this central split.  If the
non-QD component vanishes on `I` and `A -> A/I` is locally liftable, it
descends to an amenable non-QD trace on the quotient.

This finite central decomposition does not prove that QD traces form a face,
which STW explicitly leave open.

# Trust boundary

Imported results are Brown's equivalence between factorization and amenability
of the full canonical trace, the local-lifting amenable-descent theorem, and
the Effros--Haagerup local-lifting consequence for exact quotients.  The
directed-union finite-set proof, full-group-algebra directed-union
identification, residual-finiteness model for `F_2`, and invariant-mean
argument for the reduced trace are explicit in their routes.  No open
factorization premise is used in any established claim here.

# X(2): finitely generated weakly dense normal form

The hyperfinite-factor question admits a stronger norm-local reduction than
the general separable trace reduction.  The factor `R` is quasidiagonal if
and only if each of its finitely generated unital C-star subalgebras is
quasidiagonal.  Indeed, matrix models on `C*(1,F)` extend to `R` by Arveson's
theorem without changing the operator-norm estimates on the finite set `F`.

Fix a singly generated CAR subalgebra `D subset R` with weak closure `R`.  If
`R` is not quasidiagonal, a finite operator-norm obstruction gives a
nonquasidiagonal `B=C*(1,F)`.  Then

```text
A=C*(B,D)=C*(1,F,g)
```

is finitely generated, weakly dense in `R`, and remains nonquasidiagonal
because it contains `B`.  Conversely, any nonquasidiagonal subalgebra of `R`
precludes quasidiagonality of `R`.  Thus X(2) is equivalent to
quasidiagonality of all finitely generated weakly dense subalgebras.

The trace ledger cleanly separates the two norms.  On `A`, the restricted
trace is faithful and amenable and its GNS closure is `R`; these are the
hyperfinite normalized-Hilbert--Schmidt models.  It is not a quasidiagonal
trace, since faithfulness would then make `A` quasidiagonal.  The
Tikuisis--White--Winter/Gabe faithful-trace theorem further forces `A` to
fail exactness or the UCT.  Weak density of the CAR core supplies no
operator-norm approximation of the finite obstruction `F`.

# X(2): exact finite-dimensional-core normal form

The CAR core can nevertheless be made algebraically exact inside any
putative quasidiagonal trace model.  For a unital finite-dimensional
subalgebra `E subset A`, an asymptotically multiplicative u.c.p. map is close
on `E` to a representation `pi`.  If `phi=V* rho(-)V` is a Stinespring
dilation, averaging `rho(u)Vpi(u)*` over `U(E)` gives an exact intertwiner.
Its polar normalization remains an exact intertwiner and stays close to
`V`.  Compression by the normalized intertwiner therefore gives a u.c.p.
map uniformly close to `phi` on the whole unit ball and having `E` in its
multiplicative domain.

Consequently a trace is quasidiagonal if and only if its matrix models can
be required to be exact over any one prescribed finite-dimensional core.
For a fixed CAR tower `D_n subset R`, X(2) is equivalent to finite-packet
models which put each prescribed `D_n` in the multiplicative domain.  Since
`D_n` is a full matrix algebra, the normalized matrix trace then agrees
with `tau_R` exactly on `D_n`; only the outside packet remains approximate.
For a separable CAR-containing subalgebra the models can be diagonalized to
a sequence exact on `D_n` at step `n`.  For all of `R` the correct
formulation is a net/finite-set criterion.

The proof uses operator-norm matrix-unit stability and cannot be applied to
the Hilbert--Schmidt models supplied merely by hyperfiniteness.  It invokes
no exactness, UCT, nuclearity, local lifting, quotient descent, or norm
density of the CAR core.
