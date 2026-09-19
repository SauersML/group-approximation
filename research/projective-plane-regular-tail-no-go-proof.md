---
rg: 2
id: projective-plane-regular-tail-no-go-proof
kind: route
title: Use projective-plane augmentation representations as maximally escaping regular tails
target: pt-rigidity-allows-nontight-regular-tails
requires:
  - character-rigidity-equals-hyperfinite-hs-stability
---

Let

```text
Omega_p=P^2(F_p),             |Omega_p|=p^2+p+1,
```

and let `rho_p` be the orthogonal complement of the constants in the
permutation representation of `SL_3(F_p)` on `l^2(Omega_p)`.  Pull this
representation back to `Gamma=SL_3(Z)` by reduction modulo `p`.

The projective action is doubly transitive.  Therefore its complex
permutation representation is the direct sum of the constants and one
irreducible augmentation representation.  This proves irreducibility and
`dim rho_p=p^2+p`.  Since reduction is onto, Burnside's theorem gives

```text
C^*(rho_p(Gamma))=M_(p^2+p)(C).                          (NRP1)
```

With its normalized matrix trace this has the one-atom degree distribution
`delta_(p^2+p)`, proving maximal non-tightness.

We next compute the limiting character without invoking any approximation
theorem.  Fix `1!=g in SL_3(Z)`.  For all but finitely many primes, its
reduction `g_p` is not scalar.  A projective point is fixed by `g_p` exactly
when it is an eigenline over `F_p`.  For a nonscalar three-by-three matrix,
one eigenspace can have dimension two and every other eigenspace has total
dimension at most one.  Hence

```text
|Fix_(Omega_p)(g_p)| <= p+2.                             (NRP2)
```

The augmentation character is the permutation character minus one, so

```text
|tr_(d_p)(rho_p(g))|
 <=(p+3)/(p^2+p) ->0.                                   (NRP3)
```

At the identity the normalized trace is one.  Thus the normalized characters
converge pointwise to `delta_e`.

Finally fix a Kazhdan pair `(S,kappa)` for `SL_3(Z)`.  Conjugation by `rho_p`
is a unitary representation on `L^2(M_(d_p),tr_(d_p))`.  Irreducibility and
Schur's lemma say that its invariant vectors are exactly the scalars.  The
Kazhdan inequality on their orthogonal complement is precisely

```text
max_(s in S)||rho_p(s)x rho_p(s)^*-x||_2
 >=kappa||x||_2,            tr_(d_p)(x)=0,               (NRP4)
```

with the same `kappa` for every `p`.  Higher-rank lattice character rigidity
is the cited input recorded in
`character-rigidity-equals-hyperfinite-hs-stability`; the characters here are
finite-dimensional characters converging to the permitted regular character,
so there is no conflict with that theorem.

This proves every assertion in the target.  It also identifies the precise
logical fence for the Kac--Moody application.  If a finitely presented group
with no nontrivial finite-dimensional representations admitted a separated
regular one-block sequence with relator defect tending to zero, that sequence
would itself be a hyperlinear microstate sequence.  Conversely every
hyperlinear microstate may be regarded inside the one simple ambient block
`M_(d_n)`, whose degree distribution is `delta_(d_n)` after dimensions tend
to infinity.  Therefore a theorem excluding arbitrary such tails is not a
degree-tightness consequence of property `(T)` or character rigidity: it is
the regular-branch HS obstruction one is trying to prove.
