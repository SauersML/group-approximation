# Shulman homotopy lifting: central-HNN inversion consequence

Primary source checked: Tatiana Shulman, *Homotopy lifting, asymptotic
homomorphisms, and traces*, arXiv:2508.00125v5 (31 July 2026),
<https://arxiv.org/abs/2508.00125>.

The source statements used here are exact:

- Theorem 11: homotopic homomorphisms into a quotient lift together to
  discrete asymptotic homomorphisms when one endpoint does.
- Proposition 23: a trace is MF exactly when it is represented by a
  homomorphism into a tracial matrix ultraproduct which lifts to a discrete
  asymptotic homomorphism into the matrix product.

For the central HNN algebra `D=<A,t | [t,C]=0>`, the twofold representation
`f + f o iota` is homotopic to the representation which agrees twice with
`f|A` and sends `t` to `1`.  The explicit homotopy is the standard stable
null-homotopy of `diag(u,u*)`; it remains in the commutant of the doubled
edge algebra, so it respects the HNN relation at every time.  Theorem 11 and
Proposition 23 therefore yield the conditional trace statement recorded in
`central-hnn-inversion-symmetrized-trace-is-mf`.

## Scope audit against the live frontiers

This does not provide any of the following missing inputs:

1. **HS stability / arithmetic relative commutants.**  It assumes an
   operator-norm asymptotic lift of the particular quotient homomorphism on
   the base.  Hyperlinearity of the restricted trace supplies only a
   tracial-quotient homomorphism, not that lift.  Obtaining it uniformly is
   the correction/stability problem already open for the arithmetic pair.
2. **Perfect LCS compilation.**  The argument starts with a C-star quotient
   representation and has no perfect-completeness conversion from a general
   constraint-system game to an LCS game.
3. **Symmetric amalgamated doubles.**  It does not assert that all
   hyperlinear traces on `A *_C A` are MF.  Shulman's separate
   arXiv:2603.13564v2 proves algebra-level MF permanence, not such a trace
   theorem.
4. **Finite-dimensional invisibility.**  MF traces come from operator-norm
   approximate homomorphisms, not necessarily exact finite-dimensional
   representations.  Hence an element killed by every exact
   finite-dimensional representation need not be killed by an MF trace
   without an additional stability theorem.

The other 2025--2026 primary sources checked in this pass (Spaas on chordal
graph-product HS stability; Fournier-Facio--Willett on LLP/RFD/FD flexible
stability; Taller--Vidick on imperfect-completeness LCS RE-hardness;
Fu--Mastel--Zhang on perfect-completeness BCS synchronization; and
Dogon--Vigdorovich's conditional arithmetic construction) already have
hypothesis-accurate Cairn entries.  None supplies the missing hypothesis
above, so no duplicate literature-audit claim was added.
