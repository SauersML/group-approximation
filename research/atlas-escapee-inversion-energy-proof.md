---
rg: 2
id: atlas-escapee-inversion-energy-proof
kind: route
title: Bubble-sort a two-chart word and charge every adjacent swap by its cross commutator
target: atlas-escapee-defect-charges-inversion-commutator-energy
requires:
  - atlas-true-criterion-baseline
  - atlas-full-relator-data-factor-through-double-commutant-gauge
---

# Bubble-sort proof of the escapee inversion-energy bound

Normalize Hilbert--Schmidt norm by the ambient matrix dimension.  The two
charts are exact representations, so write

```text
A_g=rho_1(g),                 B_h=U rho_2(h) U^*.
```

All these operators are unitary.

## 1. Sort the word

Starting with a two-chart word `w`, repeatedly replace an adjacent inverted
pair

```text
B_h A_g   by   A_g B_h.
```

This is the stable bubble sort: it preserves the order of all first-chart
letters and separately the order of all second-chart letters.  Every pair in
`Inv(w)` is swapped exactly once, and no other pair is swapped.  The final
operator is therefore

```text
S_w=rho_1(p_1(w)) U rho_2(p_2(w)) U^*.                (BSE1)
```

Suppose one swap occurs inside unitary prefix and suffix operators `P,Q`.
The two intermediate evaluated words differ by

```text
P(B_h A_g-A_g B_h)Q.
```

Unitary invariance of normalized Hilbert--Schmidt norm gives the exact cost

```text
||P(B_h A_g-A_g B_h)Q||_2=||[B_h,A_g]||_2.           (BSE2)
```

The triangle inequality along the entire sorting path yields

```text
||pi_U(w)-S_w||_2
 <= sum_((h,g) in Inv(w)) ||[A_g,B_h]||_2.            (BSE3)
```

No approximation or dimension-dependent constant enters this estimate.

## 2. Use the single-factor escape

Assume first that

```text
(p_1(w),p_2(w))=(a,1),       a != 1.
```

Then `(BSE1)` is `S_w=rho_1(a)`.  Because `rho_1` is a regular
amplification,

```text
tr(rho_1(a))=0,
||rho_1(a)-1||_2^2=2-2 Re tr(rho_1(a))=2.             (BSE4)
```

Thus

```text
sqrt(2)
 =||S_w-1||_2
 <=||S_w-pi_U(w)||_2+||pi_U(w)-1||_2
 <=sum_Inv ||[A_g,B_h]||_2+delta_w(U).                (BSE5)
```

This proves `(EIC2)`.  Cauchy--Schwarz gives, for `N_w>0`,

```text
(sum_Inv ||[A_g,B_h]||_2)^2
 <=N_w sum_Inv ||[A_g,B_h]||_2^2=N_w E_w(U),          (BSE6)
```

and `(EIC3)` follows.  If there are no inversions, `(BSE1)` already equals
the original evaluated word, so `(BSE4)` gives
`delta_w(U)=sqrt(2)` identically.

For `(p_1(w),p_2(w))=(1,b)`, the sorted operator is
`U rho_2(b) U^*`; its normalized trace is zero and its distance from the
identity is again `sqrt(2)`.  The same proof is unchanged.

By `atlas-true-criterion-baseline`, every one of the seventy-two Atlas
cartesian escapees has exactly one nontrivial factor product, a transvection,
so this dichotomy applies word by word.

## 3. Gauge invariance

Let

```text
U'=D U C,       D in rho_1(A)', C in rho_2(A)'.
```

Then

```text
B'_h=U' rho_2(h) U'^*=D B_h D^*.
```

Since `D` commutes with every `A_g`,

```text
[A_g,B'_h]=D[A_g,B_h]D^*.                             (BSE7)
```

Every summand of `E_w` is therefore unchanged.  This is consistent with the
stronger word-by-word identity of
`atlas-full-relator-data-factor-through-double-commutant-gauge`, and shows
that `(EIC1)` is a legal mixed-chart quantity rather than a coordinate of a
chosen block representative.

## 4. What the proof does not provide

The sorting path uses the cross commutators determined by the inversion
pattern of `w`.  Nothing above bounds these commutators by the defects of the
cartesian controls.  Establishing that separate coercive comparison, or
constructing a control-small family with positive inversion energy, is the
next branch-selecting problem.  Equal block norms cannot answer it because
`atlas-equal-block-flattening-is-commutant-gauge` changes those norms while
leaving both sides of `(BSE5)` unchanged.
