---
rg: 2
id: relative-h2-does-not-supply-passive-hs-obstruction
kind: claim
title: Relative H2 does not by itself supply an exact-core Hilbert-Schmidt obstruction
distinct_from:
  passive-core-quotient-has-relative-rational-h2: that computes the nonzero mapping-cone class for the passive-core quotient; this audits whether standard relative almost-flat machinery promotes it to the required matrix sequence.
  sl2-half-rational-h2-refutes-torsion-normalized-op-basin: that obtains an absolute operator-norm countersequence with exact torsion rows; this explains why it does not automatically exactify the opposite passive-core rows or obstruct flexible normalized-HS repair.
  authenticated-core-union-basin-is-relative-liftability: that states the positive relative HS lifting target; this proves the available relative H2 invariant has vanishing normalized density on every operator-small sequence.
---

**ESTABLISHED NO-GO FOR THE STANDARD RELATIVE PROMOTION.**  Keep the
surjective quotient

```text
q:K -> G=PSL_2(Z[1/2])                                (RHO1)
```

from `passive-core-quotient-has-relative-rational-h2`.  The nonzero class
in `H_2(Cone(Bq),Q)` does not, by the currently available relative
almost-flat correspondence, produce a quasirepresentation of `G` whose
pullback is a genuine representation of `K`.

There are two independent reasons.

## 1. Relative almost monodromy forgets the kernel of a surjection

Kubota's relative almost-monodromy theorem defines a relative
quasirepresentation for a homomorphism `phi:Lambda->Gamma` as **two**
quasirepresentations of `Gamma` whose pullbacks along `phi` are stably
approximately unitarily equivalent.  It is explicitly insensitive to
`ker(phi)` and depends only on `phi(Lambda)`; see Definition 6.2, Remark
6.3, and Theorem 6.12 of
[Almost flat relative vector bundles and the almost monodromy correspondence](https://arxiv.org/abs/1908.10575).

For `(RHO1)`, `q(K)=G`.  The relative datum therefore compares the two
quasirepresentations on all of `G`; it does not encode that one tuple
satisfies the defining relations of `K` exactly while only the two kernel
relators added by `q` are approximate.  Thus this theorem cannot supply
the exact-core countersequence required to refute
`passive-iwahori-off-zero-cb-normal-splitting`.  The absolute Dadarlat
construction likewise contains no such exact-on-`K` refinement.

There is a conditional central-extension construction, but one of its
hypotheses is presently missing.  A multiple of the free class in
`H^2(G,Z)` restricts trivially to `K`, because `H^2(K,Z)` is torsion, so its
central extension splits over `K`.  Integrally, the same amalgamated
Mayer--Vietoris calculation gives `H_2(K,Z)=0` and finite `H_1(K,Z)` (the
edge generator maps injectively to the infinite cyclic summand of the
Baumslag--Solitar abelianization); the universal coefficient sequence
therefore makes `H^2(K,Z)` finite.  If one could additionally prove that
the middle extension is residually finite with finite quotients in which
the central order tends to infinity, the usual central-character
eigenspaces would give projective almost representations of `G` whose
chosen section is multiplicative on `K`.  No such residual-finiteness
theorem for this middle extension is established here.  Hence this is a
conditional operator-norm attack, not a proved counterexample.

## 2. The fixed relative index has vanishing normalized density

Even if an exact-core operator-norm countersequence is constructed, the
two-homology invariant alone cannot give a positive normalized-HS wall.
Let `z` be one fixed integral cellular two-cycle and let `rho_n` be
matrix-valued quasirepresentations whose finitely many relator values used
by `z` have operator defects at most `epsilon_n<1/2`.  The associated
winding/pre-determinant pairing is a finite signed sum of principal
logarithms.  If its integer value is `kappa_n` in dimension `d_n`, then

```text
|kappa_n|/d_n <= C_z epsilon_n.                        (RHO2)
```

Indeed `||log U||_op<=2||U-I||_op` for `||U-I||_op<1/2`, while
`|Tr(log U)|<=d_n||log U||_op`; summing the fixed coefficients of `z` and
dividing by `2 pi d_n` proves `(RHO2)`.

Therefore every operator-norm asymptotic sequence has

```text
kappa_n/d_n ->0.                                      (RHO3)
```

The class may remain a nonzero integer and obstruct operator-norm
perturbation, exactly as a Bott index does.  But `(RHO3)` shows that it is
supported only at sublinear normalized index density.  It yields no fixed
positive lower bound in normalized Hilbert--Schmidt distance and is
compatible with an `o(d_n)` flexible boundary surgery.  A separate theorem
would be needed to amplify this sublinear topological charge to positive
trace density; relative `H_2` by itself does not do so.

## Consequence

The class computed in `passive-core-quotient-has-relative-rational-h2`
correctly warns that exact-zero Newton estimates are only local.  It does
not refute the ultimate normalized-HS passive lifting target.  At most, a
future residual-finite split-central-extension construction could refute
the **operator-norm** off-zero splitting currently used as a sufficient
Newton gate.  The arithmetic program must therefore either prove that gate
by structure beyond relative `H_2`, or replace it by a genuinely mixed
flexible argument which can discard the sublinear index carrier.
