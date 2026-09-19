# Unitary covariance controls the total fine transition variance

Date: 2026-08-14

## 1. Outcome

The single-edge transition-variance gate is already closed by the compressor
covariance equations. No multiplication relation, extension-character
representative, or commutant gauge choice is needed.

Let `alpha:F->G` be an injective homomorphism of finite abelian groups, let
`rho:F->U(M)` and `sigma:G->U(M)` be exact unitary representations, and let
`U` be unitary. For a source character `chi`, define

```text
P_chi=(1/|F|) sum_(a in F) conjugate(chi(a)) rho(a),
R_chi=(1/|F|) sum_(a in F) conjugate(chi(a)) sigma(alpha(a)). (CTV1)
```

If `(Q_zeta)_(zeta in dual(G))` is the fine target-character PVM, then

```text
R_chi=sum_(zeta composed_with alpha=chi) Q_zeta.     (CTV2)
```

Put `E=U P_chi U*` and let

```text
e_chi^2=(1/|F|) sum_a
 ||U rho(a) U*-sigma(alpha(a))||_2^2.               (CTV3)
```

Then

```text
boxed:
sum_zeta ||[E,Q_zeta]||_2^2 <=2 e_chi^2.            (CTV4)
```

The constant is independent of `|F|`, `|G|`, the number of extensions of
`chi`, and the matrix dimension.

Consequently the intrinsic transition effects

```text
A_zeta=P_chi U*Q_zeta U P_chi                       (CTV5)
```

satisfy

```text
sum_zeta tau(A_zeta-A_zeta^2) <=e_chi^2,            (CTV6)
```

and de la Salle rounding gives a PVM in the source corner with ambient total
squared error below `9 e_chi^2`.

## 2. Fourier proof

Conjugating the first Fourier sum in `(CTV1)` gives

```text
E-R_chi
 =(1/|F|) sum_a conjugate(chi(a))
   [U rho(a) U*-sigma(alpha(a))].                   (CTV7)
```

Convexity of squared Hilbert--Schmidt norm yields

```text
||E-R_chi||_2^2 <=e_chi^2.                          (CTV8)
```

Let

```text
E_Q(X)=sum_zeta Q_zeta X Q_zeta                    (CTV9)
```

be the fine block-diagonal expectation. Equation `(CTV2)` puts `R_chi` in
the range of `E_Q`. Since conditional expectation is the Hilbert--Schmidt
orthogonal projection,

```text
||E-E_Q(E)||_2 <=||E-R_chi||_2.                    (CTV10)
```

For self-adjoint `E`, the PVM commutator identity is

```text
sum_zeta ||[E,Q_zeta]||_2^2
 =2||E-E_Q(E)||_2^2.                               (CTV11)
```

Equations `(CTV8)--(CTV11)` prove `(CTV4)`.

Finally, the exact transition-effect identity from
`TRUE_TRANSITION_EFFECTS_REMOVE_THE_POSITIVIZATION_GATE.md` says

```text
sum_zeta tau(A_zeta-A_zeta^2)
 =(1/2)sum_zeta||[E,Q_zeta]||_2^2.                 (CTV12)
```

This proves `(CTV6)`, and its cardinality-free PVM-rounding bound becomes
`9 e_chi^2`.

## 3. Why the earlier apparent fiber obstruction disappears

Fourier twirling an arbitrary matrix produces an exact `alpha`-intertwining
**contraction**. On one source-character block that contraction may have
range strictly inside the target restriction fiber and may retain
off-diagonal coefficients between fine target characters.

The actual compressor matrix is unitary. Its conjugation of the explicit
Fourier projection is governed directly by `(CTV7)`. Under exact covariance,

```text
U P_chi U*=R_chi,                                   (CTV13)
```

the entire coarse target projection, not an arbitrary subprojection of it.
Thus it commutes with every fine target cut. In the approximate case,
`(CTV8)` gives the dimension-free perturbation of this exact fact.

The source-commutant gauge cancellation from
`TRUE_TRANSITION_VARIANCE_IS_SOURCE_GAUGE_INVARIANT.md` is consistent with
this proof: right multiplication by a unitary commuting with `rho(F)` leaves
both sides of `(CTV13)` unchanged.

## 4. Microstate implementation

For a growing finite coefficient envelope, include the compressor, the
finite groups `F,G`, and the necessary products in the microstate window.
Finite-group exactification makes `rho` and `sigma` exact. The group
conjugation relations give the RMS defect `(CTV3)` tending to zero. Choose
the envelope size slowly relative to the requested microstate accuracy; the
average in `(CTV3)` has no sum-to-maximum loss.

Therefore every source character cut obtains an asymptotically exact PVM of
fine extension outcomes. Summing over source characters preserves the total
error budget.

## 5. Correct remaining gate

This closes only the **single-edge measurement** problem. Different root
positions and different compressor occurrences may yield different fine
character PVMs on the same multiplicity space. Covariance does not make
those PVMs commute or make their labels satisfy the cross-root multiplication
table jointly.

The remaining theorem is therefore not fine-fiber diagonalization. It is
multi-edge compatibility:

> **Multiplication-compatible transition-PVM gate.** Show that the PVMs
> obtained from `(CTV5)` for the finite family of adjacent-root compressor
> occurrences can be jointly coupled, with total error tending to zero, so
> that their labels obey `t_l s_k=delta_lk` and the required four-root
> products on one common multiplicity coordinate.

The local Pauli countermodel explains why this does not follow from the
separate PVMs. It realizes every one-edge Fourier/covariance statement while
keeping different adjacent-root measurements noncommuting. The raw routing
and four-root packet must supply compatibility, not existence or positivity
of the individual transition measurements.
