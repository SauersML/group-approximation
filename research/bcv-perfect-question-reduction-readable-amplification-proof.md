---
rg: 2
id: bcv-perfect-question-reduction-readable-amplification-proof
kind: route
title: Extract every controlled source corner from the exact BCV Pauli normal form
target: bcv-every-perfect-question-reduction-amplifies-readable-closure
requires: []
---

Use Bowen--Chapman--Vidick, arXiv:2501.00173. Their Pauli action and unique
negative irreducible representation are Definition 3.64, Definition 3.68,
equations `(44)--(46)`, and Remark 3.70. The honest controlled answer
formula is Definition 4.4, equations `(49)--(51)`. The exact converse used
below is Remark 4.22, equations `(91)--(94)`, especially item (6), together
with Theorem 4.24.

## 1. The exact Pauli factor has a monomial normal form

Let `PZ_i` and `PX_i` be the target Pauli observables. Perfectness gives
the hypotheses of Remark 4.22. Equation `(91)` gives the unique
`2^k`-dimensional negative Pauli representation with a multiplicity space,
and equation `(92)` identifies the SamZ atoms.

For ZPC typing one should not choose an arbitrary self-testing unitary.
Work in the original Z-aligned signed-set basis of `S`. Every `PZ_i` is
diagonal and every `PX_i` is a signed permutation. Let `Omega_z` be the
joint `PZ` eigenspace with sign string `z in F_2^k`. The exact Pauli
relations imply

```text
PX_i Omega_z = Omega_(z+e_i).                            (UQP1)
```

Thus all `Omega_z` have the same coordinate dimension `m`. Choose the
coordinate basis of `Omega_0` and identify

```text
(z,omega) |-> PX^z omega.                                (UQP2)
```

The `PX_i` commute and square to one, so `(UQP2)` is a monomial unitary
from `ell^2(F_2^k) tensor Omega_0` onto `H_S`. In this identification,

```text
PX^a=X^a tensor 1,    PZ^c=Z^c tensor 1,
e_z=|z><z| tensor 1.                                    (UQP3)
```

Equation `(92)` says precisely that the `e_z` are the joint atoms of the
readable SamZ measurement. Hence every `e_z` belongs to `D_0(S)`.

## 2. The controlled blocks form a perfect source strategy

Remark 4.22 item (6), using equation `(93)`, says that every answer
observable is block diagonal over the `e_z` and that its block depends only
on the sampled endpoint. In the notation of equation `(51)`, it has the
exact form

```text
C_(epsilon,j)
  = sum_(z in F_2^k) e_z tensor U_(s_epsilon(z),j),
epsilon in {A,B}.                                       (UQP4)
```

The operators `U_(x,j)` define the source strategy `T`. A block of a
signed permutation preserving a coordinate subspace is a signed
permutation, and a block of a readable diagonal observable is diagonal.
Thus `T` has the same readable/unreadable typing and is ZPC.

There is no missing-support assumption. BCV's question law is the
pushforward of the uniform seed law by the sampler, and Definition 2.48
defines the positive-weight edges as possible sampler outputs. Therefore
each supported source edge `xy` has a seed `z` with

```text
s_A(z)=x,    s_B(z)=y.                                   (UQP5)
```

Compress the perfect IntroA--IntroB test to the nonzero block `e_z`.
The target edge commutation restricts to source edge commutation, and
zero rejection restricts to zero rejection of the source predicate at
`xy`. This holds for every supported edge, so `T` is perfect. Vertices
outside the sampler support occur in no positive-weight test and may be
filled trivially.

## 3. Every readable source corner occurs in every Pauli block

Let `p` be a readable source spectral projection at a supported vertex
`x`. Choose a side `epsilon` and a seed `z_x` with
`s_epsilon(z_x)=x`. Functional calculus applied to `(UQP4)` gives a
target readable projection

```text
p_hat=sum_z e_z tensor p_(s_epsilon(z)).
```

Cutting by the readable SamZ atom gives

```text
e_(z_x) p_hat=e_(z_x) tensor p.                          (UQP6)
```

The Pauli-X observables are structural unreadables, and

```text
(X^a tensor 1)e_z(X^a tensor 1)^*=e_(z+a).               (UQP7)
```

Consequently `e_w tensor p` belongs to `D_infinity(S)` for every `w`.
Closing under the Boolean operations gives

```text
e_w tensor D_0(T) subseteq D_infinity(S)                 (UQP8)
```

for every `w in F_2^k`.

## 4. Controlled unreadables transport the whole closure

Define `D_(t+1)(T)` from `D_t(T)` by adjoining the conjugates by source
structural-unreadable generators and then taking the finite Boolean algebra
they generate. Assume inductively that

```text
e_w tensor d belongs to D_infinity(S)
```

for every `w` and every `d in D_t(T)`. Let `U_(x,j)` be a source
unreadable generator and choose `epsilon,z_x` as above. Use the full
controlled target unreadable `C_(epsilon,j)` from `(UQP4)`. One must not
claim that the isolated block `U_(x,j)` is itself a target word. Instead,

```text
C_(epsilon,j) (e_(z_x) tensor d) C_(epsilon,j)^*
 = e_(z_x) tensor U_(x,j) d U_(x,j)^*.                  (UQP9)
```

The right side belongs to `D_infinity(S)` by its definition. Conjugating
it by `X^(w+z_x) tensor 1` and using characteristic two copies it to the
`w` block. Boolean closure and induction give

```text
e_w tensor D_infinity(T) subseteq D_infinity(S)          (UQP10)
```

for every `w`. The orthogonal sum of the `2^k` corners in `(UQP10)` is

```text
ell^infinity(F_2^k) tensor D_infinity(T)
  subseteq D_infinity(S),                                (UQP11)
```

which is `(UQR1)` after restoring the monomial identification `W`.
A finite Boolean algebra with `b` atoms tensored with the `2^k` SamZ
atoms has `2^k b` atoms, proving `(UQR2)`.
