# The full-packet gap splits into a right-shift or multiplicity witness

Date: 2026-08-14

## 1. Outcome

The full raw-packet gap from
`TRUE_FULL_RAW_PACKET_COMMUTANT_WITNESS.md` has a canonical two-stage
decomposition. After discarding an `o(1)` exceptional summand, an exactified
trace-preserving representation of the fixed finite group `K` has the form

```text
H_n = l2(K) tensor C^(m_n),
rho_n(k)=lambda_K(k) tensor 1.                       (RSM1)
```

Let

```text
A_n = C[lambda_K(K)] tensor 1,
B_n = C[lambda_K(K)] tensor M_(m_n).                (RSM2)
```

Then `A_n subset B_n`, and the exact squared distance

```text
dist_2(F_n,A_n)^2 -> 3/16                           (RSM3)
```

splits orthogonally as

```text
dist_2(F_n,B_n)^2
 +dist_2(E_(B_n)(F_n),A_n)^2 -> 3/16.               (RSM4)
```

Consequently at least one of the following occurs along an ultrafilter-large
subsequence:

1. a member of a recovered sixteen-element right-regular packet has squared
   commutator energy at least `3/16-o(1)` against `F_n`; or
2. a unitary acting only on the multiplicity coordinate has squared
   commutator energy at least `3/16-o(1)` against `F_n`.

This does not solve the synchronization gate, but it separates its bounded
finite part from its genuinely unbounded multiplicity part.

## 2. The intermediate algebra

Let `rho_K` denote the right regular representation of `K` on `l2(K)`. It
commutes with the left regular representation. Twirling by this fixed finite
right packet gives

```text
E_(B_n)(X)
 = (1/|K|) sum_(k in K)
     (rho_K(k) tensor 1) X (rho_K(k)^* tensor 1).    (RSM5)
```

Indeed, the fixed algebra of the right regular action on `l2(K)` is the left
group algebra, while the multiplicity matrix is untouched. The expectation
from `B_n` to `A_n` is

```text
E_(A_n)|_(B_n) = id_(C[lambda_K(K)]) tensor tr_(m_n). (RSM6)
```

The composition of `(RSM5)` and `(RSM6)` is the expectation onto `A_n`.
Since conditional expectations are Hilbert--Schmidt orthogonal projections,
nested projections give the exact Pythagorean identity `(RSM4)`.

The `o(1)` qualification in `(RSM1)` is harmless. The normalized character
of a trace-preserving microstate restricted to `K` converges to the regular
character. Finite-group exactification therefore leaves only an
`o(d_n)`-dimensional nonregular summand, which contributes `o(1)` to every
normalized Hilbert--Schmidt estimate.

## 3. The right-shift case

For a finite unitary action, the Reynolds energy identity gives

```text
(1/|K|) sum_(k in K)
 ||[(rho_K(k) tensor 1),F_n]||_2^2
 =2 dist_2(F_n,B_n)^2.                              (RSM7)
```

If the first summand of `(RSM4)` is at least `3/32-o(1)`, its average
commutator energy is at least `3/16-o(1)`. At least one of the sixteen right
shifts realizes that lower bound.

This is the bounded branch of the synchronization problem. The family size
does not grow with the matrix coordinate, although its recovered placement
inside the coordinate still depends on the chosen regular decomposition.

## 4. The multiplicity case

If the second summand of `(RSM4)` is at least `3/32-o(1)`, Haar averaging over
`U(m_n)` gives a multiplicity unitary `W_n` with

```text
||[1 tensor W_n,E_(B_n)(F_n)]||_2^2
 >=3/16-o(1).                                       (RSM8)
```

The right-packet expectation commutes with multiplicity conjugation, so

```text
[1 tensor W_n,E_(B_n)(F_n)]
 =E_(B_n)([1 tensor W_n,F_n]).                      (RSM9)
```

Contractivity of conditional expectation upgrades `(RSM8)` to

```text
||[1 tensor W_n,F_n]||_2^2 >=3/16-o(1).             (RSM10)
```

This branch is pure multiplicity leakage. Adding more fixed raw Pauli words
cannot remove it: all such words act on the left regular coordinate and
commute with `1 tensor W_n`.

## 5. Refined live gate

A matrix-specific completion may now be divided into two independently
falsifiable statements:

1. **right-shift synchronization:** the cross-root/compiler relations force
   `F_n` to asymptotically commute with the recovered right-regular copy of
   the fixed group `K`;
2. **multiplicity synchronization:** after right-packet twirling, those same
   relations force the remaining operator-valued left Fourier coefficients
   to become scalar on `C^(m_n)`.

If both hold, `(RSM7)` and `(RSM10)` contradict `(RSM3)`. If the first fails,
one only needs a fixed sixteen-member counterpacket. If the first succeeds
but the second fails, the obstruction has been isolated entirely inside the
unbounded coefficient algebra, with no Pauli-coordinate ambiguity left.

This is the full-packet analogue of the parity/multiplicity split, but its
first stage uses every raw packet element and its endpoint is the exact
`3/16` Fourier gap.
