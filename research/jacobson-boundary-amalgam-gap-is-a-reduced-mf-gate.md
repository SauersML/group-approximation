---
rg: 2
id: jacobson-boundary-amalgam-gap-is-a-reduced-mf-gate
kind: claim
title: The boundary-amalgam gap is exactly non-MF of every marked C*-image, and every argument valid in the literal reduced algebra dies
distinct_from:
  jacobson-head-collapse-is-not-a-universal-tracial-identity: that is a normalized-HS firewall for EL_28(J) in finite von Neumann algebras; this is an operator-norm firewall for the finitely presented amalgam Xi, adds stable finiteness and finite-subgroup support profiles to the killed class, and proves the exact C*-gate for gamma_Xi.
  finite-vn-toeplitz-coefficient-reconstruction-fails: that concerns the packet-headed Toeplitz group H_f and coefficient decoders; this concerns gamma_Xi and applies to every C*-algebraic step, not only ring reconstruction.
  jacobson-boundary-amalgam-gap-characterizes-mark-collapse: that identifies gamma_Xi>0 with collapse of the mark in every norm matrix corona; this converts that into non-MF of every generated C*-algebra and names the reduced algebra of the literal image as the universal test object.
  jacobson-full-boundary-packets-have-compatible-regular-models: that realizes regular finite-packet profiles in matrices without the mixed words; this uses the regular representation of the literal group, in which both mixed words are exact.
---

**ESTABLISHED FIREWALL AND GATE.**  Use the finitely presented group

```text
Xi=< F *_(L') J | (h b)^3=1, W=1 >,        w_Q=x_13,Q,
```

of `jacobson-boundary-amalgam-gap-characterizes-mark-collapse`, with its
infimum `gamma_Xi`.  Let `pi:Xi->Lambda` be the literal Jacobson action
onto its image, and `lambda` the left regular representation of `Lambda`.
Call a unital C*-algebra MF when it admits an injective *-homomorphism
into some `prod_n M_(d_n)/directSum_n M_(d_n)` (the graph's convention).

**(G1) Exact C*-gate.**

```text
gamma_Xi=0
  iff  some unitary representation sigma of Xi with sigma(w_Q)!=1
       generates an MF C*-algebra.
```

Hence `gamma_Xi>0` implies that for every marked quotient
`Xi->Lambda'` retaining `w_Q`, and every representation of `Lambda'`
retaining the mark, the generated C*-algebra is not MF.  In particular

```text
gamma_Xi>0  ==>  C*_r(Lambda) is not MF.
```

**(G2) The test object.**  The pair `(rho_F,rho_J)=(lambda pi|F, lambda pi|J)`
is an admissible pair in the unitary group of the separable unital
C*-algebra `C*_r(Lambda)`.  This algebra has a faithful tracial state and is
stably finite in every matrix amplification.  Both mixed errors vanish, and

```text
||lambda pi(w_Q)-1||=2.
```

For every finite subgroup `H<=Xi` on which `pi` is injective (in particular
`F`, `J`, and the reconstructed `Mat_(3x3)(F_2) semidirect F`), the
restriction of `lambda pi` to `H` is a multiple of the regular
representation of `H`.  Its operator-norm support profile is therefore all
of `Irr(H)`, every character orbit of every abelian normal subgroup
occurs, and each isotypic component has multiplicity at least its dimension.

**(G3) Class kill.**  No estimate of either form

```text
max(mixed errors)<eps  ==>  rho_F(w_Q)=1,
||rho_F(w_Q)-1|| <= omega(max(mixed errors)),  omega(t)->0 as t->0,
```

can hold for all admissible pairs in all unital C*-algebras with a faithful
tracial state, or in all stably finite unital C*-algebras, or in any other
class containing `C*_r(Lambda)`.  Consequently every argument whose steps are
all valid for admissible pairs in such algebras is dead as a proof of
`gamma_Xi>0`.  This class contains:

1. exact algebraic consequences of the relators (TS splitting,
   reconstruction of the first-level root group and larger finite packets);
2. finite-group averaging, intertwiner averaging and polar decomposition,
   used as dimension-free corrections;
3. trace, rank, and multiplicity identities for the faithful trace;
4. direct or stable finiteness of the target (the Toeplitz mechanism
   `TS=1 ==> ST=1`), since `C*_r(Lambda)` is stably finite;
5. support-profile exclusions on finitely many finite subgroups, since
   `lambda pi` has full profile on each.

Each dies at the single step concluding that the head is trivial (or small),
because that step applies verbatim to `lambda pi`, where the head has norm
distance two from the identity.

**What survives.**  A proof of `gamma_Xi>0` must invoke a property that
matrix algebras have uniformly in the dimension and that fails for
`C*_r(Lambda)`.  By (G1) this is not a choice: any such proof proves that
`C*_r(Lambda)` is non-MF, hence produces a Property-(T)-free separable,
stably finite, non-MF reduced group C*-algebra.  Bounded-dimension exclusions
(compactness below a fixed dimension, root-orbit fibers of bounded
multiplicity) are not killed, but they supply no uniformity, and their
uniform extension must use a strictly matricial input of this kind.

No MF or non-MF statement about `Lambda`, `Xi` or `C*_r(Lambda)` is asserted,
and the sign of `gamma_Xi` is not settled.

DERIVATION
jacobson-boundary-amalgam-gap-is-a-reduced-mf-gate-proof
