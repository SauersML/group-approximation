---
rg: 2
id: elementary-abelian-regular-normalizers-have-diffuse-fibers
kind: claim
title: Regular elementary-abelian windows classicalize only after quotienting diffuse normalizer fibers
distinct_from:
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that treats one amplified regular packet of a finite centerless simple lamp; this proves the fixed-window permutation quotient for elementary abelian lamps and gives an increasing-window, trace-faithful coherent countermodel.
  scalar-trace-of-diagonal-normalizer-is-permutation-blind: that hides trace cancellation in a diagonal phase after a full masa is normalized; this uses a Fourier unitary in the regular lamp multiplicity commutant and keeps lamp covariance and actor multiplication exact.
  kt-centralizer-normalization-hs: that is the global open relative-commutant normalization theorem for the Kazhdan pair; this settles only one invariant finite lamp window and isolates why moving windows are still different.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED SHARP LOCAL BOUNDARY.**

## 1. One invariant regular window has a classical quotient

Let `B` be a fixed finite elementary abelian two-group and let
`sigma_n:B -> Sym(V_n)` be permutation actions satisfying

```text
|Fix(sigma_n(b))|/|V_n| -> 0              for every b != 0.       (EAR1)
```

Let `H` act on `B` through a homomorphism
`alpha:H -> Aut(B)`.  Then there are genuine homomorphisms

```text
P_n:H -> Sym(V_n)                                               (EAR2)
```

such that, for every fixed `h in H` and `b in B`,

```text
d_H(P_n(h) sigma_n(b) P_n(h)^(-1), sigma_n(alpha_h(b))) -> 0.   (EAR3)
```

Indeed, all but `o(|V_n|)` points lie in free `B`-orbits.  On each free
orbit, after choosing one basepoint, use the canonical permutation

```text
x=sigma_n(b)x_0  |->  sigma_n(alpha_h(b))x_0;
```

let `H` act trivially on the exceptional set.  Thus an invariant
asymptotically regular finite lamp window has no local existence
obstruction.  Coherent unitary normalizers are not even needed for this
conclusion.

On an exactly free packet `ell^2(B) tensor C^k`, write
`P_alpha delta_b=delta_(alpha(b))`.  Every unitary `U` satisfying

```text
U (lambda_B(b) tensor 1) U^*
  =lambda_B(alpha(b)) tensor 1                                  (EAR4)
```

has the unique form

```text
U=D(P_alpha tensor 1),
D in U((lambda_B(B) tensor 1)').                                (EAR5)
```

For a coherent actor family, the `D`'s form a nonabelian one-cocycle in
this commutant.  Passing to the quotient by the commutant returns the
canonical coherent permutations `P_alpha`, but gives no metric control of
the chosen representatives.

## 2. Exact coherence and canonical trace do not control that fiber

There is a trace-faithful increasing-window model in which the cocycle in
`(EAR5)` is maximally nonmonomial.  Put

```text
A=direct_sum_(r>=1) F_2^3
```

and let `t` act on each three-dimensional block by `J=1+N`, where
`N^3=0!=N^2`.  Thus `J` has order four.  Let `B_m` be the first `m`
blocks, let `p_m:A -> B_m` be truncation, choose `k_m -> infinity`, let
`Q_m` be the permutation implementing `J` on `ell^2(B_m)`, and let
`F_(k_m)` be the normalized Fourier matrix.  Then

```text
U_m=Q_m tensor F_(k_m),
pi_m(a,t^j)
 =(lambda_(B_m)(p_m(a)) tensor 1) U_m^j                         (EAR6)
```

is an exact representation of the fixed group `A rtimes_J C_4`, factoring
through `B_m rtimes_J C_4`.  The lamp restriction is `k_m` copies of the
regular permutation representation, all covariance rows and all actor
products have zero defect, and the sequence has the canonical group trace.
The actor can even be made infinite, residually finite, and Kazhdan without
changing this phenomenon.  Take `K=SL_3(Z)`, choose separating finite
quotients `L_m` of `K`, and let `H=K times C_4` act on `A` through
the `C_4` factor.  On

```text
ell^2(B_m) tensor ell^2(L_m) tensor C^(k_m)
```

use

```text
U_m(g,t^j)
 =Q_m^j tensor lambda_(L_m)(g_bar) tensor F_(k_m)^j.             (EAR7)
```

This gives exact coherent normalizers for the Kazhdan actor `H`, a regular
lamp module of multiplicity `|L_m|k_m`, and the canonical trace of
`A rtimes H`.  The unitary for `t` has the same Fourier-row distance
bound below.

Nevertheless, for every monomial matrix `M_m` in the displayed lamp basis,

```text
||U_m-M_m||_2^2 >= 2-2/sqrt(k_m).                              (EAR8)
```

This remains sharp after arbitrary negligible block padding.  If
`d_m=|B_m|k_m`, `r_m=o(d_m)`, `Z_m in U(r_m)` is arbitrary, and
`M'_m` is any monomial of size `d_m+r_m`, then

```text
|tr((M'_m)^*(U_m direct_sum Z_m))|
 <=(d_m/sqrt(k_m)+r_m)/(d_m+r_m) -> 0.                         (EAR9)
```

Thus the squared normalized Hilbert--Schmidt distance is at least
`2-o(1)`, and the distance tends to `sqrt(2)`.  This covers every
permutation and every `B_m`-orbit-coherent monomial representative after
any `o(d_m)` padding.

Fourier diagonalization gives

```text
(lambda_(B_m)(B_m) tensor 1)'
  isomorphic_to direct_sum_(chi in dual(B_m)) M_(k_m)(C).       (EAR10)
```

In particular the tracial ultraproduct contains the diffuse algebra
`product_U M_(k_m)`, and the Fourier factor in `(EAR6)` lives entirely
there.  This is a concrete diffuse-multiplicity model, not dimension-zero
block surgery.

## 3. Exact surviving Kun--Thom gate

This result does **not** refute equivariant normalizer transfer: the canonical
permutations `Q_m tensor 1` exist in the countermodel.  It refutes only the
stronger shortcut that tries to round the given `U_m`'s themselves in
normalized Hilbert--Schmidt norm.

The Kun--Thom lamps present moving algebras `B_E -> B_(gE)`, not one
invariant finite `B`.  The remaining theorem must therefore construct
compatible commutant gauges, or directly construct permutations, across an
increasing family of moving windows so that actor products agree on almost
every point.  The cocycles live in different multiplicity algebras as the
window moves.  No finite-window quotient argument identifies them, and the
global route remains open.

DERIVATION
elementary-abelian-regular-normalizer-fiber-proof
