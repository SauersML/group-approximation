---
rg: 2
id: laurent-sln-fq-lattices-are-charfinite
kind: claim
title: The Laurent lattices SL_n(F_q[t,1/t]), n >= 3, and every subgroup commensurable with them are charfinite
distinct_from:
  character-rigidity-equals-hyperfinite-hs-stability: that is the Dogon--Vigdorovich equivalence for lattices in real Lie groups and does not cover positive characteristic; this imports charfiniteness itself, over F_q(t), from Bader--Boutonnet--Houdayer--Peterson Theorem A.
  kazhdan-hs-instability-lives-on-properly-nonamenable-limits: that says instability of any Kazhdan group lives on limit algebras with no injective summand; this identifies those limit algebras for SL_3(F_2[t,1/t]) as exactly L(A) with the canonical trace.
  km-246-lattice-is-character-rigid: that is character rigidity of a non-linear Kac--Moody lattice, proved in the graph; this is an imported theorem about linear S-arithmetic lattices over a function field.
  laurent-sl3-central-covers-never-witness-instability: that concerns central Kazhdan covers and projective models of the Laurent lattice; this classifies the characters of the lattice and its commensurability class.
  subshift-elementary-groups-are-character-rigid: that concerns elementary groups over subshift rings; its lattice-restriction remark on EL_3(F_2[u^{+-1}]) is the charmenability input supplied here.
---

Let `q` be a prime power, `n >= 3`, `R = F_q[t,1/t]` and `A_(n,q) = SL_n(R)`.

**(CF0) Charfinite.** Every subgroup `Gamma <= SL_n(F_q(t))` commensurable with
`A_(n,q)` is charfinite in the sense of Bader--Boutonnet--Houdayer--Peterson,
arXiv:2009.09952v3, Definition `def:charmenable`.  A character there is a
normalized positive definite function invariant under conjugation, not
necessarily extremal.  Charfinite means:
1. every nonempty compact convex `Gamma`-invariant subset of `PD_1(Gamma)`
   contains a character;
2. every extremal character is supported on the amenable radical `Rad(Gamma)`
   or is von Neumann amenable;
3. `Rad(Gamma)` is finite;
4. each dimension carries only finitely many isomorphism classes of unitary
   representations;
5. every amenable extremal character is finite, meaning its GNS space is
   finite-dimensional.

Consequences for every such `Gamma`:
- **(CF1) Radical.** `Rad(Gamma) = Gamma ∩ mu_n(F_q)·I`.  Every finite normal
  subgroup of `Gamma` consists of scalar matrices.  For `(n,q) = (3,2)`,
  `Rad(A_(3,2)) = {e}`.
- **(CF2) Extremal dichotomy.** Every extremal character of `Gamma` is either
  finite, of the form `tr_k∘pi` for an irreducible `pi: Gamma -> U(k)`, or
  supported on the finite central subgroup `Rad(Gamma)`.  So `Gamma` is
  character rigid in the sense of Dogon--Glasner--Gorfine--Hanany--Levit,
  arXiv:2507.21862v1, Definition `def:character rigidity`.
- **(CF3) Normal subgroups.** A normal subgroup of `Gamma` is either finite and
  central, or of finite index.
- **(CF4) Finite images.** Every finite-dimensional unitary representation of
  `Gamma` has finite image.

For `A = A_(3,2) = SL_3(F_2[t,1/t])`:
- **(CF5) Trace decomposition.** `A` is ICC.  Every character `phi` of `A` has
  a unique decomposition

  ```text
  phi = s·delta_e + sum_i c_i·(tr_(k_i)∘pi_i),
  s, c_i >= 0,   s + sum_i c_i = 1,
  ```

  where the `pi_i` are pairwise inequivalent irreducible finite-dimensional
  unitary representations, each with finite image.  Its GNS von Neumann
  algebra is

  ```text
  pi_phi(A)'' = L(A) ⊕ ⊕_(c_i>0) M_(k_i)(C),
  ```

  with the `L(A)` summand present exactly when `s > 0`.
- **(CF6) Limit algebras of models.** Let `sigma_n: A -> U(d_n)` be an
  asymptotic representation along a free ultrafilter `omega`, with limit
  algebra `N_omega` in the tracial ultraproduct.  Then `N_omega` has no
  nonzero injective direct summand, i.e. the model is *properly non-amenable*
  in the sense of `kazhdan-hs-instability-lives-on-properly-nonamenable-limits`,
  if and only if its limit trace is `delta_e`.  In that case `N_omega ≅ L(A)`,
  a II_1 factor.  Hence `A` is flexibly (resp. strictly) HS-stable if and only
  if every asymptotic representation with limit trace `delta_e` along any
  `omega` admits the flexible (resp. strict) correction of (A3) there.

## Reading for `sl3-laurent-f2-is-flexibly-hs-stable`

- **The splitting sketch is now unconditional.**  The target's
  Kazhdan-projection bullet assumed that every extreme character of `A` is
  `delta_e` or finite-dimensional.  By (CF1), (CF2) and (CF4) that holds, and
  the finite characters factor through finite quotients.
- **Instability can only live at `delta_e`.**  Every non-roundable model of `A`
  may be taken with limit algebra exactly `L(A)` and canonical trace.  There
  are no twisted non-amenable sectors, and no limit algebra of the form
  `L(A/N)` for an infinite quotient.
- **This is not a smaller reduction.**  Restricting to the `delta_e` regime is
  already implied, for residually finite Kazhdan groups, by
  `residual-finite-regularization-removes-the-weak-ucp-quantifier` together
  with `kazhdan-weak-ucp-stability-is-flexible-stability`.
- **Charfiniteness alone cannot decide the target.**  The unstable group
  `Z^(2g) ⋊ Sp_(2g)(Z)` of `rf-kazhdan-group-not-flexibly-hs-stable` already
  has its witness at `delta_e`.  That group is not charfinite: `Z^(2g)` is an
  infinite normal subgroup of infinite index, which (CF3)-type rigidity
  forbids.  So charfiniteness removes the mechanisms that use normal
  subgroups or non-regular characters, but says nothing about the regular
  regime where the known Kazhdan instability actually occurs.

Proof: `laurent-sln-fq-lattices-charfinite-proof`.
