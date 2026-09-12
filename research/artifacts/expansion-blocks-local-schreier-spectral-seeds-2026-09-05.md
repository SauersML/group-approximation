# Expansion blocks local Schreier trial maps

This gives a limitation of local word-halo and short polynomial-filter
attempts to construct the low-energy count required by MSC14. The
obstruction already holds for exact inputs and zero curvature. It is
not a stability counterexample and does not rule out a global algebraic
construction.

## 1. A quotient-support Rayleigh floor

Let G have symmetric finite Kazhdan generating set S, `h=|S|`, and
constant kappa in the convention

```text
dist(v,H^G)<=kappa^(-1)max_s ||pi(s)v-v||.
```

Let N be any finite-index subgroup, with index m and left-coset
transversal T. Let `pi:N->U(k)` be genuine and let Pi be its induced
representation on `direct_sum_(t in T) C^k`. Let `U_s` be arbitrary
unitaries on `C^d`. For a nonzero linear map A from `C^d` into this
induced space, write its coset rows as `A_t:C^d->C^k` and define

```text
D_s(A)=Pi(s)A-AU_s,
Delta=(1/h)sum_s D_s^*D_s,
Rayleigh(A)=<Delta A,A>/||A||_HS^2.
```

Suppose A is supported on a set Omega of cosets, with
`theta=|Omega|/m`. Then

```text
Rayleigh(A)>=kappa^2(1-theta)/h.                       (ES1)
```

To prove this, put `f(t)=||A_t||_HS`. If `s t=t' n(s,t)`, the
corresponding residual row is

```text
pi(n(s,t))A_t-A_(t')U_s.
```

Both left and right factors are unitary. The reverse triangle inequality
therefore gives

```text
|f(t)-f(t')|<=||pi(n(s,t))A_t-A_(t')U_s||_HS.
```

Summing over the cosets and S proves that the scalar permutation
Laplacian energy of f is at most `<Delta A,A>`. The permutation action
on the finite transitive coset space has constants as its invariant
vectors. Property (T) bounds its scalar energy below by

```text
(kappa^2/h)(||f||_2^2-m^(-1)|sum_t f(t)|^2).
```

As f is supported on Omega, Cauchy--Schwarz gives
`m^(-1)|sum_t f(t)|^2<=theta ||f||_2^2`. Finally
`||f||_2^2=||A||_HS^2`. These identities prove `(ES1)`.

In particular an epsilon-low-energy trial map must satisfy

```text
|supp A|/m>=1-h epsilon^2/kappa^2.                      (ES2)
```

There is no dependence on the fibre dimension, source dimension, or
choice of exact subgroup holonomy. Nontrivial holonomy does not evade
the scalar row-norm obstruction.

## 2. Short polynomial filters cannot produce these maps from local seeds

Consider the unitary connection transports

```text
mathcal A_s(A)=Pi(s)A U_s^*.
```

Each transport moves row support by one edge in the Schreier graph. A
polynomial of degree at most L in these transports and their inverses,
applied to a map supported on a coset set Omega_0, is supported on the
word-L neighborhood of Omega_0. Cancellations can only shrink this
support. The same conclusion holds for a degree-L polynomial in Delta,
since

```text
Delta=2I-(1/h)sum_s (mathcal A_s+mathcal A_s^*).
```

Let `v=|Omega_0|`. When `h>=2`, the crude word count gives the support
bound

```text
|supp A|<=v sum_(l=0)^L h^l<=v h^(L+1)/(h-1).
```

Combining this with `(ES2)`, whenever
`1-h epsilon^2/kappa^2>0`, gives the explicit degree requirement

```text
L>=log_h( (m/v)(h-1)(1-h epsilon^2/kappa^2) )-1.        (ES3)
```

In particular, for a single-coset seed and epsilon tending to zero,
one needs `L>=log_h m-O_h(1)`. More precisely, the word neighborhood
must cover a fraction tending to one of the coset space; the degree
bound is only its elementary consequence.

Positive mixtures or direct sums of trial maps all having Rayleigh
quotient at least a fixed positive number retain that floor, since
their energy and squared norm add. Thus Gaussian compression followed
only by its positive second-moment energy ledger does not turn such a
family into a low-energy certificate. Arbitrary coherent linear
combinations can change the energy and may spread over the entire
quotient; `(ES1)` then applies to their resulting support, not to the
supports of individual summands separately.

## 3. Relevance and limitations

The estimate holds even when the input is an exact representation of a
finite quotient and the induced ambient contains it. For example, take
the quotient regular input and the aligned trivial subgroup seed. There
are exact zero-energy coordinate-row frames, but they occupy every
coset. A construction confined to a small word neighborhood cannot
find low energy in that same exact example.

Consequently small curvature supports and correct local word fillings
do not, by themselves, produce low-energy trial vectors confined to
small parts of a growing quotient. Passing through a local polynomial
filter costs at least the global spreading scale in `(ES3)`. QRC5 alone
does not bound its defining defect against this growing scale.

The full low-energy spectral projection is not asserted to remain
localized: spectral projection is a global operation and can have rows
on every coset. The argument gives no lower or upper bound on its
dimension beyond excluding the indicated local trial construction. It
does not prevent globally coordinated frames, exact arithmetic
identities, or another construction of the missing spectral count.
