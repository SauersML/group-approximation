# An additive index cannot transduce to a fixed finite phase

Date: 2026-08-14

## 1. Outcome

The naive index-to-phase proposal

```text
KInd |-> (-1)^KInd                                    (ITP1)
```

cannot be a universal obstruction to hyperlinearity. Normalized
Hilbert--Schmidt microstates are closed under arbitrary direct-sum
amplification. A Fredholm, rank-defect, or Bott index is additive under that
operation, whereas a represented central scalar word stays the same scalar
on every summand.

Doubling therefore changes `(-1)^KInd` to `+1` while leaving the marked
phase `-I` unchanged. More generally, amplification by the order of any
finite character kills that character. Thus no finite character of an
additive matrix index can canonically equal a fixed nontrivial group phase
throughout an amplification-closed microstate class.

This does not rule out every index argument. A direct integer-index
contradiction, or an index normalized by a canonically recovered positive-
density spin multiplicity, could still be amplification-stable. What is
ruled out is precisely the proposed conversion of microscopic rank leakage
to a macroscopic central sign by applying a finite character to an ordinary
additive index.

## 2. Amplification preserves every hyperlinear statistic in scope

Let

```text
phi:F -> U(d)                                           (ITP2)
```

be a finite normalized-Hilbert--Schmidt microstate and let `k>=1`. Define

```text
phi^(k)(g)=phi(g) tensor I_k in U(kd).                 (ITP3)
```

For normalized traces,

```text
tr_(kd)(phi^(k)(g))=tr_d(phi(g)),                      (ITP4)
```

and for every pair of matrices,

```text
||X tensor I_k-Y tensor I_k||_(2,kd)
 =||X-Y||_(2,d).                                      (ITP5)
```

Hence amplification preserves exactly:

- every multiplicative defect;
- every normalized trace;
- every normalized-Hilbert--Schmidt separation; and
- the scalar value of every evaluated group word.

In particular, if a central involution has image `-I_d`, then after
amplification its image is

```text
-I_d tensor I_k=-I_(kd),                              (ITP6)
```

not `(-1)^k I_(kd)`.

## 3. Additive indices transform differently

Let `Ind(phi)` be any integer-valued statistic constructed from a compressed
transport operator and additive under orthogonal direct sums. Ordinary
Fredholm index, kernel-minus-cokernel dimension, and signed rank defect have
this property. Then

```text
Ind(phi^(k))=k Ind(phi).                               (ITP7)
```

For the parity character, `(ITP7)` gives

```text
(-1)^Ind(phi^(2))
 =(-1)^(2 Ind(phi))
 =1.                                                   (ITP8)
```

But `(ITP6)` says that a marked phase `-I` remains `-I` after the same
doubling. Therefore an identity

```text
pi(w)=(-1)^Ind(phi) I                                  (ITP9)
```

cannot hold both before and after amplification when `pi(w)=-I`.

The argument is not special to parity. If

```text
chi:Z -> roots_of_unity                                (ITP10)
```

has finite order `q`, amplification by `q` gives

```text
chi(Ind(phi^(q)))=chi(q Ind(phi))=1.                  (ITP11)
```

Thus every nontrivial finite phase extracted from an additive index is
destroyed by an allowed amplification.

## 4. Determinants do not repair the problem

The determinant is multiplicative and can detect a rank-one sign in a fixed
matrix size, but it is not a normalized-Hilbert--Schmidt invariant. Under
amplification,

```text
det(X tensor I_k)=det(X)^k.                           (ITP12)
```

For example,

```text
det(-I_d)=(-1)^d.                                     (ITP13)
```

Choosing even dimension makes this determinant `+1` although the matrix is
still the scalar `-I_d` at Hilbert--Schmidt distance `2` from `I_d`.
Hyperlinear microstates may always be doubled, so no odd-dimensional
determinant normalization can be forced.

Likewise, the determinant of every finite-dimensional commutator is one.
This is compatible with a central commutator word being represented by
`-I_d` whenever `d` is even. It supplies no contradiction.

## 5. Relation to the shifted-scale commutant defect

`TRUE_LOCALLY_FINITE_COMMUTANTS_RECOVER_BUT_AT_SHIFTED_SCALES.md` identifies
an honest integer boundary defect between the recovered commutants at
successive scales. The unilateral binary model has a factor-two dimension
jump. The calculation above says that merely taking the parity of that
defect cannot lock it to the Clifford sign.

There remain two logically different index routes.

1. **Integer obstruction.** Construct a finite-dimensional operator which
   must simultaneously have nonzero ordinary integer index and be a square
   operator between equal-dimensional spaces. This would be a direct
   contradiction and does not pass through a phase character.
2. **Normalized spin-block index.** First recover the canonical positive-
   density `M_16` spin factor, then divide an additive index by the number of
   spin blocks. Such a ratio is unchanged by amplification. It must still be
   shown to be quantized and forced by the group relations; neither point is
   automatic.

The first route is essentially the finite-multiplicity one-cut leakage
theorem. The second is a possible refinement of the eight-lamp spin
reduction. The raw transducer `(ITP1)` is closed.

## 6. Research decision

Do not use a mod-two Fredholm index, determinant sign, or any other finite
character of an additive defect as the missing hyperlinear invariant unless
an additional canonical normalization is supplied and proved invariant
under `phi |-> phi tensor I_k`.

The shortest surviving route remains scale synchronization: use the two
Leavitt branches and the cross-zero multiplication relation to recover the
three forbidden contractions in one finite multiplicity corner. An integer
one-cut index proof is equivalent in strength, but a parity-to-phase slogan
does not supply it.

No computation or local build was used in this argument.
