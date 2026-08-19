# A fixed adjoint-expander library binds the Pauli multiplicity gap

Date: 2026-08-14

## 1. Outcome

`TRUE_PAULI_MULTIPLICITY_HAS_ONE_SYMMETRY_WITNESS.md` produces a
dimension-independent obstruction, but its witnessing symmetry is selected
separately in every matrix coordinate. This note gives an exact sufficient
condition for replacing that moving symmetry by one member of a fixed finite
library of group words.

For the actual Pauli packet, set

```text
E=PQ,                       F=U*QU,
X=Phi_E(F)-(1/4)1,          Phi_E(F)=EFE+(1-E)F(1-E).   (FLB1)
```

The packet traces imply

```text
tr(EX)=tr((1-E)X)=0,
||X||_2^2=1/8+2y >= 1/8,    y=tr(EFEF)>=0.              (FLB2)
```

Let `V_1,...,V_k` be a fixed finite family of unitaries commuting with `E`,
and let

```text
T(Z)=(1/k) sum_i V_i Z V_i*.                            (FLB3)
```

If the one-vector adjoint gap

```text
Re <X,(1-T)X> >= kappa ||X||_2^2                       (FLB4)
```

holds for some dimension-independent `kappa>0`, then one fixed library member
satisfies

```text
||[V_i,Phi_E(F)]||_2^2 >= kappa/4.                     (FLB5)
```

Thus a presentation-level completion no longer needs to name the
coordinate-dependent Haar witness. It is enough to provide finitely many
fixed words whose adjoint channel has `(FLB4)`, while the group relations
force every commutator in `(FLB5)` to vanish asymptotically.

## 2. The binder identity

For any unitary `V` and any matrix `Z`, normalized Hilbert--Schmidt norm gives

```text
||[V,Z]||_2^2
  =||VZV*-Z||_2^2
  =2||Z||_2^2-2 Re <Z,VZV*>.                            (FLB6)
```

Averaging `(FLB6)` over the library gives the exact identity

```text
(1/k) sum_i ||[V_i,X]||_2^2
  =2 Re <X,(1-T)X>.                                    (FLB7)
```

Equations `(FLB2)`, `(FLB4)`, and `(FLB7)` imply

```text
(1/k) sum_i ||[V_i,X]||_2^2
  >=2 kappa (1/8+2y)
  =kappa/4+4 kappa y
  >=kappa/4.                                           (FLB8)
```

At least one summand is at least the average. Scalars commute with every
`V_i`, so `[V_i,X]=[V_i,Phi_E(F)]`; this proves `(FLB5)`.

The scalar expression and its floor in `(FLB8)` are formalized source-first
as `actualPacketFixedLibraryAverageEnergy` and
`kappa_div_four_le_actualPacketFixedLibraryAverageEnergy` in
`GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean`. No build or
computation was run for that edit.

## 3. The exact matrix-coordinate theorem still needed

Property (T) by itself is not enough. If the `V_i` come from a fixed Kazhdan
generating set, property (T) gives an adjoint spectral gap only on the
orthogonal complement of the common invariant algebra

```text
I={Z: V_i Z V_i*=Z for every i}.                       (FLB9)
```

Write `P_I` for the Hilbert-space projection onto `I`. Suppose the channel
has a uniform gap `delta>0` on `I`-orthogonal vectors:

```text
Re <Z,(1-T)Z> >= delta ||Z||_2^2       when P_I(Z)=0.   (FLB10)
```

Consequently the live assertion is not a generic expansion statement. In
addition to `(FLB10)`, it needs the following carrier-specific coordinate
claim for some `eta>0`:

> In every hypothetical matrix microstate of the atlas presentation, the
> block-centered transported carrier `X_n` has a uniformly positive component
> orthogonal to `I_n`; quantitatively,
> `||(1-P_(I_n))X_n||_2^2 >= eta ||X_n||_2^2-o(1)` for the invariant algebra
> of one fixed finite word library.

Equivalently, the carrier-specific part can be written

```text
||P_(I_n)(X_n)||_2^2 <= (1-eta)||X_n||_2^2+o(1).        (FLB11)
```

Combining `(FLB10)` and `(FLB11)` gives `(FLB4)` with
`kappa=delta*eta`, up to the microstate error. This is weaker than recovering
the whole Pauli multiplicity algebra and weaker than proving that every
`E_n`-commuting symmetry is harmless. It only controls one vector against
one fixed finite adjoint channel.

The relation-side requirement is also finite. Choose fixed words `s_i` whose
matrix images are the `V_i`, and impose or derive relations giving

```text
max_i ||[V_(i,n),Phi_(E_n)(F_n)]||_2 -> 0.             (FLB12)
```

Then `(FLB8)` and `(FLB12)` contradict each other whenever
`delta*eta>0`.

## 4. Why this does not silently solve the problem

The invariant algebra in `(FLB9)` can be large in reducible matrix
representations. A Kazhdan constant does not identify it, and arbitrary
amplification cannot be forbidden. Therefore asserting `(FLB10)` from
property (T) alone would control only the complement of that algebra;
asserting `(FLB11)` without using the carrier relations would merely rename
the missing relative-commutant theorem.

The gain is a sharper and falsifiable endpoint. The coordinate theorem only
has to prevent this single explicit carrier vector from hiding in the fixed
algebra of a fixed finite library. It need not recover coordinate
commutants, choose a Haar symmetry, or control every vector in the
multiplicity algebra.

The most promising source for the library remains the cross-root
multiplication module already present in the atlas construction. Its role
would be twofold:

1. furnish a fixed Kazhdan/expanding adjoint channel inside the parent-cut
   commutant, giving `(FLB10)`; and
2. use the transported-carrier relations to prove `(FLB11)` specifically for
   `X_n`.

Until that carrier-specific invariant-projection estimate is proved, this is
a reduction rather than a proof of a nonhyperlinear group.
