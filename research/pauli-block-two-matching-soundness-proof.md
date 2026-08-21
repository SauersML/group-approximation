---
rg: 2
id: pauli-block-two-matching-soundness-proof
kind: route
title: Correct Pauli labels, kill their symplectic form, and scalarize the residual signs
target: pauli-block-phases-have-uniform-two-matching-soundness
requires:
  - phased-translations-reduce-to-alpha-plane-test
  - matrix-phased-translations-exact-identity-scalarize
---

Write `H=F_2^(2m)` for the Pauli label space.  Distinct Pauli labels are
orthogonal in normalized Hilbert--Schmidt inner product.  Therefore a failed
label equation contributes squared distance `2`, and

```text
Pr_(x,b)[Delta_b Delta_(alpha b) v_x !=0]
 <= epsilon_alpha^2/2.                                      (PB3)
```

For every linear functional `ell:H->F_2`, apply `(PT5)` to the Boolean
function `ell(v_x)`.  Averaging over uniform `ell`, every nonzero label
syndrome is detected with probability `1/2` on both sides.  Hence

```text
Pr_(x,a,b)[Delta_a Delta_b v_x !=0]
 <=(27/2) Pr_(x,b)[Delta_b Delta_(alpha b) v_x !=0].          (PB4)
```

The standard plurality correction for the full affine parallelogram test is
alphabet-independent: for a map from an elementary abelian group to any
abelian group, sufficiently small rejection produces an affine map differing
on at most twice the rejection fraction.  One direct corrector at `t` is the
plurality, over uniform `y,z`, of

```text
v_y+v_z+v_(t+y+z).                                           (PB5)
```

The usual two-overlapping-parallelograms argument shows that these pluralities
form one affine map.  Thus `(PB3)--(PB4)` give

```text
v'_x=v_0+Lx,                 Pr_x[v'_x!=v_x]=O(epsilon_alpha^2).
                                                                    (PB6)
```

Retain the signs in `(PB1)` and put `R'_x=sigma_x W(v'_x)`.  Orthogonality and
the four-term Lipschitz bound transfer both sampled energies from `R` to `R'`
with an `O(epsilon_alpha^2)` squared-energy loss.

Let `omega` be the Pauli symplectic form.  The identity-matching defect of the
corrected blocks is zero or maximal according as

```text
q(x,y)=omega(v_0+Lx,v_0+Ly)                                 (PB7)
```

is zero or one.  This is a binary polynomial of degree at most two on
`K x K`.  If it is nonzero, its relative weight is at least `1/4`, the minimum
distance of the order-two Reed--Muller code.  Hence, below a universal error
threshold, the transferred identity energy forces `q=0` identically.  The
corrected Pauli blocks then commute pairwise, so their identity matching is
exact.

Apply `(MP4)` to `R'` and transfer back to `R`; this proves `(PB2)` below the
threshold.  Above it, `(PB2)` follows after increasing `C`, since every unitary
commutator-difference energy is at most `4`.
