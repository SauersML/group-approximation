# Transition intertwining controls the spectral decoder

Date: 2026-08-14

## 1. Outcome

The commutator hypothesis left in
`TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md` is automatic from the natural
source--target intertwining defect of the transition block.

Let `T` be a contraction in a finite tracial matrix algebra, let `A,B` be
unitaries, and put

```text
H=T* T,                 E=T A-B T.                    (TGI1)
```

Then

```text
||[H,A]||_2 <= 2 ||T A-B T||_2.                      (TGI2)
```

This is dimension-free and uses no spectral information.

## 2. Proof

Set `X=T A` and `Y=B T`.  Both are contractions.  Left multiplication by
`A*` preserves Hilbert--Schmidt norm, and therefore

```text
||[H,A]||_2
 =||A* H A-H||_2
 =||X* X-Y* Y||_2.                                   (TGI3)
```

The difference of the two Gram operators factors as

```text
X* X-Y* Y=X* (X-Y)+(X*-Y*)Y.                         (TGI4)
```

The Hilbert--Schmidt ideal inequalities and `||X||,||Y||<=1` now give

```text
||X* (X-Y)||_2       <=||X-Y||_2,
||(X*-Y*)Y||_2       <=||X-Y||_2.                    (TGI5)
```

The triangle inequality proves `(TGI2)`.

In the squared language already used by the Lean development, the equally
useful form is

```text
||[H,A]||_2^2 <=4 ||T A-B T||_2^2.                  (TGI6)
```

There is a more general two-sided identity which is the correct interface
when the recovered arrows are contractions rather than unitaries:

```text
[T* T,A]
 =T*(T A-B T)+(T* B-A T*)T.                         (TGI6a)
```

Consequently, for arbitrary `A,B` and contractive `T`,

```text
||[T* T,A]||_2
 <=||T A-B T||_2+||T* B-A T*||_2.                  (TGI6b)
```

In squared form,

```text
||[T* T,A]||_2^2
 <=2||T A-B T||_2^2+2||T* B-A T*||_2^2.            (TGI6c)
```

Thus the unitary one-sided estimate is convenient for coordinate shifts,
while `(TGI6b)` handles the coefficient contractions used by the Leavitt
decoder.  It is enough to recover the transition law in both orientations.

## 3. Apply it to the Pauli transition block

For projections `F,G`, take

```text
T=G F,                 H=T* T=F G F.                 (TGI7)
```

Let `A_1,...,A_4` be the four source coefficient arrows and let
`B_1,...,B_4` be their target counterparts.  Write

```text
delta_k=||T A_k-B_k T||_2.                           (TGI8)
```

The spectral coarea estimate on `[1/32,1/16]`, combined with `(TGI2)`,
selects one threshold `t` such that

```text
P=1_[t,infinity)(T* T),
tau(P)>=1/120,
sum_k ||[P,A_k]||_2^2 <=64 sum_k delta_k.             (TGI9)
```

On this corner the singular values of `T` are at least `1/sqrt(32)`, so the
inverse bound is at most `4 sqrt(2)`.  Also

```text
||[P,A_k]||_2^2
 =||(1-P)A_kP||_2^2+||PA_k(1-P)||_2^2,               (TGI10)
```

and hence `(TGI9)` supplies simultaneous two-sided leakage control for all
four source arrows.

The right side of `(TGI9)` is linear rather than quadratic in the
intertwining errors because spectral coarea uses Cauchy--Schwarz once.  This
is harmless for a fixed four-arrow family: `delta_k -> 0` still gives the
required leakage convergence.

If the arrows are merely contractions, combine coarea with `(TGI6b)`
instead.  Writing

```text
delta_k^+=||T A_k-B_k T||_2,
delta_k^-=||T* B_k-A_k T*||_2,
```

one obtains the equally dimension-free bound

```text
sum_k ||[P,A_k]||_2^2
 <=32 sum_k (delta_k^+ + delta_k^-).                 (TGI9a)
```

## 4. The new terminal synchronization gate

The spectral route no longer needs a separately proved estimate

```text
||[F G F,A_k]||_2 -> 0.                              (old gate)
```

It is enough to prove the more structural statement

```text
||G F A_k-B_k G F||_2 -> 0,       k=1,...,4.         (new gate)
```

for unitary coordinate shifts.  For contraction-valued coefficient arrows,
the honest replacement is the two-orientation pair

```text
||G F A_k-B_k G F||_2 -> 0,
||F G B_k-A_k F G||_2 -> 0.                          (TGI11)
```

These are exactly transition-intertwining identities: the raw-to-comb
overlap transports each source multiplication arrow to its target arrow.
They are the direct matrix shadow of the cross-chart multiplication-module
relations.  No spectral projection, eigenvalue gap, or coordinate-dependent
choice appears in the hypothesis.

This does not yet prove the new gate.  Exact finite Pauli representations
show that local Weyl relations alone are insufficient; the proof must use
the cross-chart relations which identify the two multiplication modules.
But once those four intertwining defects vanish, positive density,
conditioning, a common invariant corner, and two-sided leakage all follow
formally from `(TGI2)` and spectral coarea.

In the reduced pairing formulation, a separate proof of these transition
laws is unnecessary even for contraction arrows.  A mass-saturation estimate
turns the diagonal defect `R* W L-W` into both the forward and reverse
transition defects with loss `eta+sqrt(2 eta)`.  See
`TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md`.  The live
work is therefore common-coordinate extraction of the three pairing defects,
not an additional invariance theorem.

## 5. Formalization status

The matrix identities and squared estimates `(TGI6)` and `(TGI6c)` have
been transcribed respectively as
`hsNormSq_transitionGram_commutator_le_four` and
`hsNormSq_transitionGram_commutator_le_two_sided` in
`GroupApproximation/Sofic/LeavittTraceFloor.lean`, using only the existing
normalized-HS transport lemmas.  The exact threshold and trace arithmetic
in `(TGI9)` is already represented by
`one_div_120_le_of_trace_flat_spectral_split` in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean`.  Per the development
constraint, the new source was not locally built; it is source-level rather
than kernel-checked until the remote verifier accepts it.  No computation was
run for this note.
