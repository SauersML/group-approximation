---
rg: 2
id: blsw-real-lattice-frobenius-stability
kind: claim
title: Lattices in real semisimple groups of rank at least three, and their universal-cover preimages, are Frobenius stable
distinct_from:
  fournier-facio-universal-frobenius-stable-t-embedding: that embeds recursive group content into a finitely presented Frobenius-stable Kazhdan group; this is the Bader--Lubotzky--Sauer--Weinberger theorem for irreducible lattices in real semisimple groups and for the non-residually-finite preimages of those lattices in the universal cover.
  sp2g-z-flexibly-hs-stable: that is flexible stability in the normalized Hilbert--Schmidt norm and is open; this is stability in the unnormalized Frobenius norm, where the correction estimates are submultiplicative.
---

**ESTABLISHED by citation** (`blsw-real-lattice-frobenius-stability-citation`).
Bader--Lubotzky--Sauer--Weinberger, *Stability and instability of lattices in
semisimple groups*, J. Anal. Math. 151 (2023) 1--23, arXiv:2303.08943v2.

**Conventions.** The Frobenius norm is the unnormalized `||A||_F = tr(A^*A)^(1/2)`
on `M_n(C)`. An asymptotic homomorphism `phi_n : Gamma -> U(n_k)` satisfies
`||phi_n(x)phi_n(y) - phi_n(xy)||_F -> 0` for each fixed pair `x, y`. `Gamma` is
*Frobenius stable* if every asymptotic homomorphism is pointwise
Frobenius-asymptotic to a sequence of genuine homomorphisms. For a finitely
presented group this is the uniform `epsilon`--`delta` statement on the relators.

**Imported statements.**

1. (Theorem 1.1(F), from De Chiffre--Glebsky--Lubotzky--Thom.) A finitely
   generated group with `H^2(Gamma, V) = 0` for every unitary representation `V`
   (property `[T_2]`) is Frobenius stable.
2. (Theorem 2.10.) Let `G` be semisimple with finite center and no compact
   factors, `Gamma < G` a lattice, and `Gamma~` its preimage in the universal
   cover. If every simple factor has real rank at least 3, then `Gamma~` has
   property `[T_2]`. It is therefore Frobenius stable by item 1.
3. (Corollary 2.14.) Let `N` be normal in a finitely generated `Gamma`, with
   `Gamma/N` finitely presented and `N cap PR(Gamma)` of finite index in `N`.
   If `Gamma` is Frobenius stable, so is `Gamma/N`. Here `PR` is the profinite
   radical.
4. (Theorem 2.11, Deligne.) If `Gamma` has the congruence subgroup property and
   `pi_1(G)` is infinite, then `Gamma~` is not residually finite. Its profinite
   radical is a finite-index subgroup of `ker(Gamma~ -> Gamma)`.
5. (Theorem 1.3.) If every non-compact factor of `G` has rank at least 3, an
   irreducible lattice `Gamma < G` is Frobenius stable. The possible exception is
   a factor of Hermitian type together with failure of the congruence subgroup
   property.
6. (Corollary 1.4.) For `G = Sp(2g, R)` with `g >= 3`, the preimage in the
   universal central extension of every lattice, in particular of `Sp_(2g)(Z)`,
   is not Frobenius approximated.

**Scope fence for this graph.** `Sp_4(R)` has real rank 2. So Deligne's triple
cover `E_3` of `Sp_4(Z)`, the witness in `deligne-central-mark-hs-collapse`, lies
outside items 2 and 5. The lattice has property `(T_1) = (T)` from Bader--Sauer's
`(T_(n-1))`, `n` the minimal rank, and nothing more is claimed. Frobenius
stability of `Sp_4(Z)` and of `E_3` is not established anywhere on main.

**Why the normalized problem is untouched.** The paper notes (p. 4) that these
lattices are never Hilbert--Schmidt stable, by Becker--Lubotzky, and that
`||A||_HS = n^(-1/2) ||A||_F`. The correction scheme behind item 1 uses
`||XY||_F <= ||X||_F ||Y||_F`. The normalized norm has no such inequality: an
HS-small correction can have large operator norm on a small-rank subspace.

Consumer: `deligne-symplectic-covers-are-not-schatten-approximated`.
