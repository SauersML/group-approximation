# The first exceptional raw/comb commutator has infinite order

Date: 2026-08-13

## Statement

Let

```text
X'_1=U* X_1 U,
h=[X'_1,raw]=X'_1 raw X'_1 raw,
```

where `X'_1` and `raw` are involutions in the exact binary Leavitt-prefix
model.  Then

```text
h has infinite order.                                      (MCI1)
```

This is the first explicit nonfinite direction found by the shortest
raw/comb packet audit.  The other four first transported-generator/raw
commutators have order two.

## The direction is exactly bilateral

Put `g=X'_1` and `r=raw`.  Since `g^2=r^2=1` and `h=(gr)^2`, direct group
algebra gives

```text
g h g^(-1)=h^(-1),        r h r^(-1)=h^(-1).          (MCI1b)
```

Thus both reflections reverse the infinite translation direction.  The
identity is formalized for arbitrary groups in
`GroupApproximation/Sofic/MixedCommutatorDihedral.lean` as
`involutions_conjugate_product_sq_to_inverse`.

## Grading proof

Work in the binary Leavitt algebra over `F_2`, with its standard integer
grading

```text
deg(s_alpha t_beta)=|alpha|-|beta|.
```

Exact prefix reduction expands `h` into 21 monomials.  Its least degree is
`-8`, and the homogeneous degree-`-8` component consists of the single term

```text
m=s_00 t_(00(10)^4).                                     (MCI2)
```

All other terms have degree strictly greater than `-8`.  Therefore the
degree-`-8n` component of `h^n` can only be obtained by selecting `m` from
every factor.  Prefix cancellation gives

```text
m^n=s_00 t_(00(10)^(4n)) != 0.                           (MCI3)
```

Hence `h^n` has a nonzero homogeneous component of degree `-8n` for every
`n>0`.  The identity is homogeneous of degree zero, so `h^n != 1`.  This
proves `(MCI1)`.

The exact certificate checks `(MCI2)` directly and checks the formula
`(MCI3)`, uniqueness of the minimum-degree term, and degree range
`[-8n,0]` through `n=16`.  The proof for arbitrary `n` is the grading
argument above, not extrapolation from those sixteen cases.

## Coefficient dynamics

Let `F=F_(--)` be the top raw coefficient cut from
`TRUE_TRANSPORTED_PAULI_ORBIT_FINGERPRINT.md`.  The same exact audit finds

```text
tau(F h^n F h^(-n))=1/64=tau(F)^2       for 1<=n<=16.   (MCI4)
```

No nonzero tested translate returns to `F`.  Thus the infinite-order escape
is not a wandering-projection shortcut: its translates have positive,
trace-independent overlap rather than being orthogonal.  Equivalently, the
tested centered vectors

```text
h^n F h^(-n)-1/8
```

are orthogonal to `F-1/8`.  This looks like a bilateral regular direction,
which finite cyclic matrices can approximate.  By itself `(MCI1)` therefore
does not contradict hyperlinearity.

Relation `(MCI1b)` closes the most direct one-sided interpretation: the two
packet involutions already provide both directions and exchange them.  Any
one-sided boundary would therefore have to arise only after an additional
coefficient or spectral compression that is not invariant under these
reflections.  The mixed word `h` alone cannot supply it.

## Reproducible certificate

`experiments/atlas_mixed_commutator_dynamics.py` performs the exact bounded
prefix and rational group-algebra audit.  Its checked result is
`experiments/atlas-mixed-commutator-dynamics.json`.  It runs on one MSI core;
no local code is run.
