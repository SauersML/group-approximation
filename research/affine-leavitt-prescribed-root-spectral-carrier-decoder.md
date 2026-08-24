---
rg: 2
id: affine-leavitt-prescribed-root-spectral-carrier-decoder
kind: claim
title: Decode the relative Leavitt cell on the prescribed nontrivial spectral carrier of the marked root
distinct_from:
  affine-leavitt-steinberg-hs-coefficient-decoder: that allows an arbitrary existential carrier and is equivalent to direct marked-root collapse; this fixes the carrier canonically from the root word before choosing coefficient operators.
  marked-hs-separation-forces-spectral-density: that only lower-bounds a spectral carrier from marked separation; this asks for three approximate Leavitt products on that very carrier.
  approximate-relative-leavitt-cell-kills-active-trace: that kills the trace of any carrier already carrying the three products; this is the missing extraction of those products on the prescribed root carrier.
  hs-finite-heisenberg-windows-have-compatible-density-measures: that gives exact normalized multiplicity densities and restriction maps on every fixed additive/Heisenberg window; this must glue those local densities and coefficient maps on one uniformly positive part of the prescribed root carrier.
---

**OPEN.** Let `w_A=x_12(A)` be the fixed order-`p` marked root in
`Gamma_A=St_5(L_A(k[C_aff]))`, where `p>=5` is the characteristic of the
fixed splitting field. For every normalized-HS `delta`-representation `U`,
spectrally round `w_A(U)` to a unitary `W` with `W^p=I` and

```text
||W-w_A(U)||_2 <= kappa(delta),       kappa(delta)->0. (APC1)
```

This is possible because `w_A^p=1` has one fixed derivation from the finite
presentation. Define, before choosing any coefficient operators,

```text
P=1-1_{ {1} }(W),                                    (APC2)
```

the sum of all nontrivial spectral projections of `W`.

Prove that there is a modulus `omega(delta)->0` and contractions
`S_0,S_1,T_0,T_1` in the same matrix algebra such that

```text
||T_iS_i-P||_2 <= omega(delta),                 i=0,1,
||S_0T_0+S_1T_1-P||_2 <= omega(delta).          (APC3)
```

The carrier is not existential and cannot be replaced by zero unless the
marked word has already collapsed. Exact spectral calculus gives

```text
4 sin^2(pi/p) tr(P) <= ||W-I||_2^2 <= 4 tr(P).  (APC4)
```

Thus `(APC3)` and `approximate-relative-leavitt-cell-kills-active-trace`
force `tr(P)->0`, while `(APC1)--(APC4)` force `||w_A(U)-I||_2->0`.
The claim is therefore a genuine nonvacuous root-to-coefficient extraction
target.

The packet sought here must use finite-matrix structure: the genuine
Leavitt representation retains the nontrivial root carrier, so no universal
finite-tracial SOS or ordinary group-algebra identity can establish
`(APC3)`.

The finite-matrix step must also be **cross-typed**.
`typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier` gives an
exact depth-one rectangular model on which the prescribed root carrier is
all of the Hilbert space, the separate source/target PI degrees and
normalized Reynolds ranks are all correct, and every typed Steinberg
triangle is exact, while the three residuals in `(APC3)` have maximum at
least `1/3`.  Thus neither more typed standard-polynomial tests nor more
individual packet superrank measurements can close this claim.  The
remaining finite-coordinate assertion must identify a returned target with
the source on one physical reservoir, or charge the failure of that
cross-typed return.

The Hilbert--Schmidt finite-window input is now rigorous and does not pass
through operator-norm rank germs.
`hs-finite-heisenberg-windows-have-compatible-density-measures` exactifies
every fixed additive/three-root window in the tracial ultraproduct and gives
its exact branching density vector.  What it does not give is a common
coordinate carrier: independently exactified windows can have compatible
scalar densities while their selected matrix corners have trace-zero
intersection.  The remaining decoder can therefore be attacked as the
following tightness statement:

```text
positive prescribed root mass
 -> a uniformly positive subcarrier on which the four fixed coefficient
    roots are coherent across every required Heisenberg window.            (APC5)
```

It is enough for the subcarrier in `(APC5)` to occupy a fixed positive
fraction of `P`; the Leavitt trace inequality then kills that fraction and
hence `P`.  It need not recover the complete inverse-limit type measure.

## Additional finite-window attempts

- **Pass to the limiting tracial representation. Dead.**  The canonical left
  regular representation has the same exact finite-window branching
  densities and retains the marked root.  Any martingale, conditional-
  expectation, or inverse-limit construction performed only inside the
  tracial ultraproduct would therefore apply to that regular model and cannot
  produce `(APC3)`.  The proof must retain coordinate finiteness: each matrix
  root table has finite character support and a finite-codimensional common
  kernel, whereas the regular root spectrum is diffuse.
- Taking the inverse limit of the exact density vectors produces a measure
  on the space of compatible finite types, but no coordinate projection.
  Mass may move to finer types while every proposed nested matrix carrier
  loses trace.
- Diagonalizing the finite-group corrections does not align their
  conjugating isometries.  Scalar branching identities survive, whereas the
  cross-typed products in `(APC3)` depend on the relative placement of the
  corrected corners.
- Compressing every coefficient root back to `P` supplies contractions, but
  the boundary terms in the two inverse relations need not be small.  Paying
  those four boundary terms from the shared Heisenberg incidence is the
  concrete form of `(APC5)`.
- **Round the growing abelian root windows.**  Every fixed window can be
  rounded and a diagonal schedule can make the window radius tend to
  infinity.  The actor sends each window into a larger one, however, and the
  extensions of its partial characters can change independently around
  moving loops.  Without a uniformly equivariant finite-support PVM this is
  the rectangular/moving-address escape recorded by
  `affine-leavitt-global-active-module-exposure`; scalar compatibility of the
  window marginals does not control that loop holonomy.
