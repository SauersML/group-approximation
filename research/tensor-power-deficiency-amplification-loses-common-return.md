---
rg: 2
id: tensor-power-deficiency-amplification-loses-common-return
kind: claim
title: Tensor powers amplify a rectangular kernel but lose its one-word return
distinct_from:
  balanced-direct-sums-preserve-rectangular-excess: direct sums conserve both deficiency density and return error; tensor products amplify deficiency density but fail for the different reason that their union kernel is not fixed by the common tensor-power return.
  adaptive-tensor-amplification: that tensors a separated representation with itself to convert operator separation into normalized two-norm separation; here tensoring is applied to a rectangular pencil and the obstruction is the fixed space of the diagonal return word.
  fixed-rectangular-kernel-return-factorization-is-impossible: that forbids a fixed algebraic factorization in the regular representation; this is a finite-dimensional linear-algebra obstruction which already appears before group-algebra functoriality.
---

Let `E` be an `N`-dimensional Hilbert space, let

```text
A:E->F,             K=ker A,             dim K=beta N,
```

and let `V in U(E)` fix `K` pointwise.  The tensor power has the attractive
rank identity

```text
dim ker(A^(tensor k))/N^k=1-(1-beta)^k.                (TPR1)
```

Thus `k` of order `1/beta` turns a small kernel into a positive-density
kernel.  However, the group word in the tensor-power representation is
`V^(tensor k)`, and the hypothesis `V|_K=1` does **not** make this word fix
the amplified kernel.

This failure is sharp.  Put `L=K^perp` and choose a scalar `zeta in T` with

```text
zeta^j!=1                   (1<=j<=k).
```

For

```text
V_zeta=I_K direct_sum zeta I_L,                         (TPR2)
```

one has `V_zeta|_K=1`, but

```text
ker(A^(tensor k)) intersect Fix(V_zeta^(tensor k))
 =K^(tensor k).                                         (TPR3)
```

Consequently the part of the amplified kernel returned by the one common
word has density only

```text
beta^k,                                                 (TPR4)
```

which decreases rather than increases.  No consequence using only the base
kernel return can improve `(TPR4)`.

## Proof

The orthogonal decomposition `E=K direct_sum L` gives

```text
E^(tensor k)
 =direct_sum_(S subseteq {1,...,k})
   K^(tensor S) tensor L^(tensor S^c).                  (TPR5)
```

Since `A|_L` is injective, `A^(tensor k)` is injective on the `S=empty`
summand and kills every summand with `S` nonempty.  This proves `(TPR1)` and
identifies the kernel as the sum of all nonempty-`S` summands.

On the summand indexed by `S`, the unitary in `(TPR2)` acts by the scalar
`zeta^(k-|S|)`.  By the choice of `zeta`, this scalar is one only when
`|S|=k`.  That is the single summand `K^(tensor k)`, proving
`(TPR3)--(TPR4)`.

## Canonical-moment calibration

The obstruction is not an artifact of the scalar complement.  Given a
finite moment window and `beta_n->0`, choose diagonal unitaries `W_n` on
`L_n` whose empirical spectral measures tend to Haar measure and perturb
their eigenphases so that no product of at most `k_n` eigenvalues is one.
Then

```text
V_n=I_(K_n) direct_sum W_n
```

has

```text
tr(V_n^j)->0
```

for every fixed nonzero `j`, while the only fixed vectors of
`V_n^(tensor k_n)` inside `ker(A_n^(tensor k_n))` still lie in
`K_n^(tensor k_n)`.  Hence a late vanishing-density trigger can have the
correct finite windows of an infinite-order canonical character and still
defeat the tensor return after its rank deficiency has been amplified.

## Koszul and same-model dichotomy

The rank formula `(TPR1)` uses the ordinary tensor product of numerical
operators.  It therefore moves the microstate from `H` to `H^(tensor k)` and
moves the marked word from `V` to `V^(tensor k)`.  Keeping the return as one
copy of `V` requires choosing a factor on every summand in `(TPR5)` which
contains `K`; there is no common choice because different summands have their
first bad factor in different positions.

A tensor/Koszul complex can make such a choice only by adjoining factor
selectors (for example, a first-bad-factor partition) and proving that they
are coherent with the kernel decomposition.  That is an authenticated
matrix-only decoder.  If instead the construction keeps the original
`d`-dimensional microstate and merely multiplies group-algebra coefficient
entries, the ordinary tensor-rank identity `(TPR1)` is unavailable over the
noncommutative coefficient algebra.  Thus tensoring supplies no selector-free
positive-rate exit:

- numerical tensoring gives the rank gain but loses the common-word return;
- same-model multiplication retains the word but loses the tensor rank law.

The surviving nonlinear route must therefore construct the factor selector
with runtime-independent normalized-HS control.  Tensor or Koszul notation
does not itself provide that control.
