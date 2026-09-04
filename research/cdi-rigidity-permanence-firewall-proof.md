---
rg: 2
id: cdi-rigidity-permanence-firewall-proof
kind: route
title: Pull back quotient characters and audit induction across finite index
target: standard-permanence-does-not-rigidify-the-cdi-image
requires:
  - ah-groups-fail-regular-fd-character-rigidity
  - faithful-irs-blocks-naive-ah-character-rigidity
  - cdi-character-cannot-be-promoted-by-regular-corners
  - cdi-character-rigid-image-quotient-is-an-exact-bridge
  - caprace-thom-v2-leaves-km-character-rigidity-open
  - orthogonal-kac-moody-forms-are-acylindrically-hyperbolic
  - simple-kazhdan-kac-moody-lattices-exist
artifacts:
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

If `q:G->K` is a proper quotient with `K` infinite ICC, then

```text
chi_q(g)=delta_e(q(g))                                  (CPF1)
```

is extremal, has GNS factor `L(K)`, and is nonregular on `G` because it is
one on the nontrivial kernel of `q`.  Since `K` is infinite, that factor is
infinite dimensional.  This obstructs regular-or-finite-dimensional
factor-character rigidity whenever the construction retains such a quotient.
It does not by itself obstruct regular-or-CE rigidity: the GNS factor of
`chi_q` is CE if and only if `K` is hyperlinear.  Nor can `chi_q` obstruct a
classification restricted to faithful characters, since its character
kernel is exactly `ker(q)`.

For an explicit counterexample to the stronger, incorrect obstruction, let
`K=Sym_fin(N)` and `G=K x K`.  Every nonidentity element of `K` has infinitely
many distinct conjugates obtained by moving its finite support, so `K` is
ICC.  Both groups are countable and locally finite.  For any tracial state
on `C^*(G)`, the images of the finite-dimensional group algebras of
`Sym({1,...,n}) x Sym({1,...,n})` form an increasing family whose union
generates the GNS von Neumann algebra.  That algebra is therefore
hyperfinite and Connes embeddable.  In particular all extremal characters
of `G` are CE.  Yet projection `q:G->K` is a proper infinite ICC quotient,
and `chi_q(g,h)=delta_e(g)` has infinite-dimensional hyperfinite GNS factor
`L(K)`.  Thus the proper-quotient argument distinguishes finite dimension
from CE; it cannot replace one by the other.

There is a separate, valid tensor-product calculation.  For a representation
of `H x K` obtained by tensoring the CDI representation with the regular
representation of `K`, the character is `chi(h) delta_e(k)`.  On
`H x {e}` it remains `chi`.  Thus this operation does not turn a nonregular
`chi` into the regular character of the product.  If `K` is ICC, its GNS
algebra is the factor `Q tensor L(K)`, which is non-CE because it contains
`Q tensor 1` trace-preservingly.  This calculation concerns the product
representation; it does not supply a general classification for arbitrary
free products, extensions, or their faithful image quotients.

The kernel statement follows from the last paragraph of
`cdi-character-rigid-image-bridge-proof`.  Group quotients are not functorial
quotients of a factor representation: a nonzero normal weakly closed ideal
of `Q` is all of `Q`.

For induction, finite index gives a finite matrix amplification whose
identity-coset corner contains the original GNS algebra.  This can preserve
non-CE, but it can import character rigidity only from a finite extension.
Acylindrical hyperbolicity is invariant under passage between finite-index
subgroups and overgroups, and
`ah-groups-fail-regular-fd-character-rigidity` then supplies `(CPF1)` inside
that overgroup.  As above, `(CPF1)` excludes the stronger
regular-or-finite-dimensional classification, and says nothing by itself
against the faithful regular-or-CE condition.  At infinite index, the
natural induced Hilbert space has infinitely many equal coset fibers; the canonical matrix trace is
semifinite with infinite identity, not a tracial state.  Hence the induction
does not produce the finite factorial character required by the bridge.

Finally, simplicity of the Caprace--Remy group contradicts the proper
infinite quotient consequence of non-elementary acylindrical hyperbolicity,
and the current character theorem is absent by the cited Caprace--Thom
audit.  Caprace--Hume's positive acylindrical-hyperbolicity theorem applies
to orthogonal Kac--Moody forms, not by nomenclature to every Kac--Moody
lattice.  The Glasner--Hase faithful IRS gives another precise warning: it
produces a faithful nonregular character on every acylindrically hyperbolic
source, although it does not automatically produce a factorial one.  These
facts prove the source-class and character-scope assertions and complete the
permanence audit.
