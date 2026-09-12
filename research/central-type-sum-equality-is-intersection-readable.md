---
rg: 2
id: central-type-sum-equality-is-intersection-readable
kind: claim
title: Equal chartwise central type sums factor through the literal subgroup intersection
artifacts:
  - research/central-type-sum-intersection-restriction-proof.md
distinct_from:
  finite-type-restriction-overlap-defect-formula: that computes pairwise canonical-trace overlaps for arbitrary transported finite types; this classifies literal equality when each whole side is central in one finite chart subgroup and identifies its exact group support.
  finite-type-additive-overlap-obeys-row-column-capacity: that gives numerical necessary row and column inequalities; this gives the exact Boolean lattice of common central sums via restriction components.
  heisenberg-subgroup-cuts-are-affine-stabilizer-flats: that classifies one Pauli subgroup-character cut; this closes arbitrary Boolean sums shared between two Pauli MASAs.
---

Let `Gamma` be a group and let `H,K<=Gamma` be finite. Put

```text
C=H intersect K.
```

Make a graph `R_C(H,K)` with vertex set `Irr(C)`. Join `nu` to `nu'`
whenever they both occur in `Res_C^H(rho)` for some `rho in Irr(H)`, or
they both occur in `Res_C^K(sigma)` for some `sigma in Irr(K)`. For a
connected component `Omega` put

```text
e_Omega=sum_(nu in Omega) z_(C,nu).                    (CTS1)
```

Then, inside `C[Gamma]`,

```text
Z(C[H]) intersect Z(C[K])
  = direct_sum_(Omega in pi_0 R_C(H,K)) C e_Omega.     (CTS2)
```

Consequently, for subsets `S subseteq Irr(H)` and
`T subseteq Irr(K)`, an equality

```text
sum_(rho in S) z_(H,rho)=sum_(sigma in T) z_(K,sigma)  (CTS3)
```

holds if and only if there is a union `U` of connected components of
`R_C(H,K)` such that both sides equal

```text
e_U=sum_(nu in U)z_(C,nu).                             (CTS4)
```

In that case `S` consists exactly of the `H`-types whose restriction to
`C` is supported in `U`, and analogously for `T`. In particular the
common projection has literal support in `C`; cancellation among
coefficients outside `C` cannot manufacture a new shared marginal.

There is a useful primitive-root consequence. If `q=z_(C,pi)` for one
`pi in Irr(C)` and a projection `P` of the form `(CTS3)` satisfies
`P<=q`, then

```text
P=0 or P=q.                                             (CTS5)
```

Thus two finite chart groups meeting only in the subgroup which carries the
primitive corner unit cannot share a proper nonzero marginal by summing
central chart types. Any successful finite-type atlas must make at least one
side of a load-bearing marginal noncentral in its chart group, or combine
types supported on genuinely different finite subgroups.

For an extraspecial Pauli packet this becomes explicit. Let `E` have center
`Z`, fix a nontrivial central character `zeta`, and put
`q=z_(Z,zeta)`. If `A,B<=E` are maximal abelian subgroups containing
`Z`, their character idempotents in the `q` sector are transported
central finite-subgroup types. Writing `C=A intersect B`, one has

```text
sum_(alpha in S)z_(A,alpha)=sum_(beta in T)z_(B,beta)
```

if and only if there is `U subseteq Irr(C)` with central character `zeta`
such that

```text
S=(Res_C^A)^(-1)(U),       T=(Res_C^B)^(-1)(U).         (CTS6)
```

Hence shared Pauli marginals are exactly restriction-fiber-saturated. If
`A intersect B=Z`, the only shared projections in the marked spin block
are `0` and `q`. The same conclusion applies to commuting classes of a
finite nice unitary error basis after passing to its finite central
extension.

The transverse `D_8` equality is the boundary, not an escape:

```text
p_+ + p_- = q = r_+ + r_-.
```

Its two chart subgroups meet in `<J>`, and `(CTS4)` says that the
displayed `q` is precisely the common sign type of that intersection. There
is no proper transverse Boolean-sum equality hidden in the cell.

In a finite-edge amalgam or HNN construction, normal form places the
intersection of opposite finite chart groups in the relevant edge group.
Equation `(CTS4)` therefore makes every chartwise-central additive equality
edge-readable. A genuinely new compiler must use a noncentral multipath
block, or a higher-dimensional relation which changes the packet
intersection while preserving the selected root type; ordinary finite-edge
Bass--Serre transport cannot supply it.
