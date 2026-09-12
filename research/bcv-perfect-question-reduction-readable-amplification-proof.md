---
rg: 2
id: bcv-perfect-question-reduction-readable-amplification-proof
kind: route
title: Extract every side-controlled source corner from the exact BCV Pauli normal form
target: bcv-every-perfect-question-reduction-amplifies-readable-closure
requires: []
---

Use Bowen--Chapman--Vidick, arXiv:2501.00173. Their Pauli action and unique
negative irreducible representation are Definition 3.64, Definition 3.68,
equations `(44)--(46)`, and Remark 3.70. The honest controlled answer
formula is Definition 4.4, equations `(49)--(51)`. The exact converse used
below is Remark 4.22, equations `(91)--(94)`, especially item (6), together
with the perfect IntroA--IntroB check.

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

## 2. The side-controlled blocks form a perfect double-cover strategy

Remark 4.22 item (6), using equation `(93)`, says that every A-answer
observable is block diagonal over `e_z` and that its block depends only on
`s_A(z)`. Repeating the argument for B gives, in the notation of equation
`(51)`,

```text
C_(A,j)=sum_z e_z tensor U^A_(s_A(z),j),
C_(B,j)=sum_z e_z tensor U^B_(s_B(z),j).                 (UQP4)
```

These displayed equations do not by themselves identify `U^A_x` with
`U^B_x` when `x` occurs in both sampler images. Define `T_pm` on the
double cover by assigning `U^A_x` to the plus copy of `x` and `U^B_y`
to the minus copy of `y`.

A block of a signed permutation preserving a coordinate subspace is a signed
permutation, and a block of a readable diagonal observable is diagonal.
Thus `T_pm` has the same readable/unreadable typing and is ZPC.

There is no missing-support assumption. BCV's question law is the
pushforward of the uniform seed law by the sampler, and Definition 2.48
defines the positive-weight edges as possible sampler outputs. Therefore
each supported source edge `xy` has a seed `z` with

```text
s_A(z)=x,    s_B(z)=y.                                   (UQP5)
```

Compress the perfect IntroA--IntroB test to the nonzero block `e_z`.
The target edge commutation restricts to commutation between the plus
measurement at `x` and the minus measurement at `y`, and zero rejection
restricts to zero rejection of the source predicate. This holds for every
supported edge and gives a perfect ZPC strategy for `DoubleCover(G)`.
Vertices outside the sampler support occur in no positive-weight test and
may be filled trivially.

If every supported `x` has a positive synchronization loop, the corresponding
Intro block tests the two PVMs for equality. The zero-loss functional
relation gives `U^A_x=U^B_x`, so `T_pm` descends to `G`. If the supported
graph is bipartite, choose `U^A_x` on one side and `U^B_y` on the other.
A zero-answer anchor in both sides carries only the trivial PVM, so it causes
no ambiguity. This is the standard exact double-cover descent.

## 3. Every readable double-cover corner occurs in every Pauli block

Let `p` be a readable spectral projection of `T_pm` at a supported sheet
vertex. Choose `epsilon=A` for a plus vertex and `epsilon=B` for a minus
vertex, and choose a seed `z_x` with `s_epsilon(z_x)=x`. Functional
calculus applied to `(UQP4)` gives a target readable projection

```text
p_hat=sum_z e_z tensor p_(epsilon,s_epsilon(z)).
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
e_w tensor D_0(T_pm) subseteq D_infinity(S)              (UQP8)
```

for every `w in F_2^k`.

## 4. Controlled unreadables transport the whole closure

Define `D_(t+1)(T_pm)` from `D_t(T_pm)` by adjoining the conjugates by
double-cover structural-unreadable generators and taking the finite Boolean
algebra they generate. Assume inductively that `e_w tensor d` has been
obtained for every `w` and `d in D_t(T_pm)`. Let `U^epsilon_(x,j)` be a
source-sheet unreadable generator and choose `z_x` as above. Use the full
controlled target unreadable `C_(epsilon,j)` from `(UQP4)`. One must not
claim that the isolated block `U^epsilon_(x,j)` is itself a target word.
Instead,

```text
C_(epsilon,j) (e_(z_x) tensor d) C_(epsilon,j)^*
 = e_(z_x) tensor
     U^epsilon_(x,j) d (U^epsilon_(x,j))^*.              (UQP9)
```

The right side belongs to `D_infinity(S)` by its definition. Conjugating
it by `X^(w+z_x) tensor 1` copies it to the `w` block. Boolean closure and
induction give

```text
e_w tensor D_infinity(T_pm) subseteq D_infinity(S)       (UQP10)
```

for every `w`. The orthogonal sum of the `2^k` corners is

```text
ell^infinity(F_2^k) tensor D_infinity(T_pm)
  subseteq D_infinity(S),                                (UQP11)
```

which is `(UQR1)` after restoring the monomial identification `W`.
A finite Boolean algebra with `b` atoms tensored with the `2^k` SamZ
atoms has `2^k b` atoms, proving `(UQR2)`. Either exact double-cover
descent only selects sheet measurements, so the same inclusion holds with
`D_infinity(T)` whenever a source strategy `T` is recovered.
