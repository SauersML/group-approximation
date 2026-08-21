# Affine–Leavitt–Steinberg normalized-HS decoder audit

Date: 2026-08-21

## Claim boundary

This audit does **not** prove that

```text
Gamma_A = St_5(L_A(k[C_aff]))
```

is nonhyperlinear.  It integrates the construction dossier after checking it
against the current graph and isolates the one remaining matrix-coordinate
lemma without hiding the exact rectangular countermodel.

## Complete pieces

- The relative Leavitt envelope faithfully retains the nonzero active
  idempotent `A` and has `AR_A ≅ AR_A ⊕ AR_A`.
- `Gamma_A` is finitely presented, has property `(T)`, and
  `w_A=x_12(A)` is nontrivial.
- Every exact finite-dimensional unitary representation kills `w_A`.
- Once contractions `S_i,T_i` and a carrier `P` satisfy

  ```text
  ||T_i S_i-P||_2 <= epsilon_i,
  ||S_0T_0+S_1T_1-P||_2 <= epsilon_sum,
  ```

  cyclic normalized trace gives

  ```text
  tr(P) <= epsilon_0+epsilon_1+epsilon_sum.
  ```

- A single uniform decoder is unnecessary.  For each fixed depth `N`, an
  estimate

  ```text
  ||w_A(U)-I||_2^2
    <= 2^-N + C_N(def(U)+sep_(F_N)(U))
  ```

  is sufficient, with unrestricted growth of `C_N`, because the canonical
  microstate limit is taken before `N -> infinity`.
- On an already square source/target label space, a near-identity
  bistochastic forward/return composition is dimension-independently close
  to one permutation and its inverse.  Square near-bijection is therefore no
  longer a separate gate.

## Exact obstruction to the tempting proof

For a finite perfect pairing `b:V×W->F_2`, set

```text
V'=V⊕V, W'=W⊕W,
b'((v0,v1),(w0,w1))=b(v0,w0)+b(v1,w1),
R_0(v)=(v,0), R_1(v)=(0,v),
L_0(w)=(w,0), L_1(w)=(0,w).
```

Then exactly

```text
b'(R_i v,L_j w)=delta_ij b(v,w).
```

The maps are deterministic, linear and translation-equivariant.  Equal
ambient Hilbert dimension does not exclude them: a source Weyl factor of
dimension `N` with multiplicity `N` and a target irreducible Weyl factor of
dimension `N^2` both occupy dimension `N^2`.  The target label space grows
while multiplicity shrinks.  This conversion iterates.

Consequently deterministic equivariance, finite-depth functoriality,
canonical Fourier marginals, and equal total matrix dimension do not prove a
decoder.  Every valid argument must either close the child maps on the same
multiplicity reservoir or pay the mass leaving it.

## Narrowed live theorem

The new open node `paired-same-reservoir-boundary-lemma` asks, at every fixed
depth, for exactly that dichotomy on the paired long-root sectors of the
actual rank-five presentation.  Once obtained:

1. square bistochastic rigidity handles diagonal return;
2. the robust paired floor handles the crossed-zero identity;
3. the closed multiplicity-cycle trace ledger handles all levels with no
   depth accumulation; and
4. the fixed-depth double-limit theorem proves nonhyperlinearity.

An equivalent geometric certificate is to recover the **same** fixed-density
carrier in two trace-independent transverse child algebras.  The established
conditional-expectation inequality

```text
dist_2(F,A)^2+dist_2(F,B)^2 >= tr(F)(1-tr(F))
```

then kills the rectangular model.  The load-bearing word remains “same.”

## Falsification checklist

A proposed final proof must:

1. defeat the explicit rectangular label/multiplicity conversion;
2. never replace HS-small by rank-small;
3. retain the expanding coefficient boundary instead of closing every shear
   into one stationary Plancherel packet;
4. use paired multiplication triangles, not only a common carrier or the
   elementary one-to-two conjugator;
5. identify one common coordinate/multiplicity reservoir across the return;
6. prove density loss, not merely dimension growth; and
7. use a finite-matrix feature that does not also kill the left regular
   representation.

The strongest honest conclusion is therefore conditional:

```text
paired same-reservoir boundary payment
   => fixed-depth canonical mark estimates
   => Gamma_A is nonhyperlinear.
```
