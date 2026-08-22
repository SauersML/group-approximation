---
rg: 2
id: toeplitz-transitive-pauli-actor-repairs-relative-cell
kind: claim
title: A polynomial Toeplitz head exposes an exact four-orbit Pauli actor and avoids the multiplicity twist
distinct_from:
  toeplitz-head-jacobi-words-give-uniform-expanders: that uses a relative-Kazhdan adjoint channel whose normalizer words can carry a correlated multiplicity action; this exactifies an honest finite Pauli--linear semidirect product and uses four prototype Pauli commutators.
  normalizer-multiplicity-twist-breaks-prefix-expander-rounding: that refutes treating Clifford normalizers as `C_s tensor I`; here no such tensor form is used, because actor conjugation transports one actual Pauli word and its arbitrary multiplicity factor cancels.
  kazhdan-transitive-pauli-actor-localizes-one-mixed-word: that uses one prototype under a transitive actor; this uses four prototypes for the four natural linear-actor orbits and supplies the actor's polynomial word/derivation compiler in one Toeplitz--Steinberg presentation.
---

At Pauli rank `n`, write the Weyl quotient as

```text
W_n=V_n direct_sum V_n^*,             V_n=F_2^n.
```

Let `P_n` be the corresponding binary Heisenberg/phase-Pauli group and put

```text
K_n=SL(V_n),
J_n=P_n semidirect K_n,                                     (TPA1)
```

where

```text
g.(v,phi)=(gv,phi g^(-1)).                                 (TPA2)
```

This preserves the evaluation pairing and is an honest action on `P_n`; no
binary Clifford section is needed.  It also has an honest spin model on
`l^2(V_n)`: `P_n` acts by translations and modulations and `g` acts by the
permutation `f(x)|->f(g^(-1)x)`.

The action of `K_n` on `W_n\{0}` has exactly four orbits:

```text
(v!=0,phi=0), (v=0,phi!=0),
(v!=0,phi!=0,phi(v)=0), (v!=0,phi!=0,phi(v)=1).        (TPA3)
```

Choose one Weyl representative from each orbit.  The uniformly gapped
bounded sets `S_n` supplied by
`bounded-involutive-cayley-expanders-for-sl-n-two` therefore give a
four-prototype version of `(KPR9)`.  If `Tbar` is the actor average and
`a=||T-Tbar||_2`, the exact Weyl square function gives

```text
dist_2(T,P_n')
 <= (sum_(i=1)^4 ||[T,W_i]||_2^2)^(1/2)/sqrt(2)
    +(1+sqrt(2))a.                                         (TPA4)
```

Indeed actor invariance makes the commutator norm constant on each of the
four orbits, and their four weights in the full Weyl average sum to one.

The groups `J_n` have faithful characteristic-two representations of degree
`n+2`: use the upper-unitriangular matrices

```text
[[1,phi,z],[0,I_n,v],[0,0,1]]
```

for `P_n`, and `diag(1,g,1)` for `g in K_n`.  Therefore the Toeplitz-head
construction embeds each `J_n` in a head of size `poly(n)`.  Gaussian
elimination gives words for `S_n`, the four `W_i`, and every multiplication
and conjugacy identity used below with derivation area `poly(n)` in the fixed
Toeplitz--Steinberg presentation.

Given a presentation microstate of total energy `E`, evaluate normal-form
words for all elements of `J_n`.  The polynomial derivations make its average
all-pairs multiplication defect at most

```text
poly(n) sqrt(E).                                            (TPA5)
```

Gowers--Hatami flexible stability then replaces this finite table, after a
`poly(n)sqrt(E)` perturbation and the usual flexible dimension change, by an
exact representation of `J_n`.  In particular the restriction to `K_n` is
now an exact actor representation; no HS stability of the ambient infinite
Toeplitz group is assumed.

Let `T` be the proposed next-cell operator.  The deep Toeplitz tail commutes
with the finite head, so the fixed presentation gives, with polynomial
derived-word loss,

```text
avg_(s in S_n)||[T,U_s]||_2^2 <= poly(n) E,
sum_(i=1)^4||[T,W_i]||_2^2 <= poly(n) E.                  (TPA6)
```

On the exactified table, the Cayley gap of `K_n` is precisely `(KPR5)`.
Applying the four-orbit estimate `(TPA4)` gives

```text
dist_2(T,P_n') <= poly(n) sqrt(E),                         (TPA7)
```

with no dependence on the spin dimension.  If in an isotypic decomposition
`U_s=C_s tensor V_s`, the factors `V_s` cause no problem: in
`U_s W_i U_s^(-1)` they cancel, which is exactly why the prototype-orbit
argument survives the countermodel to bare normalizer averaging.

Thus the polynomial Toeplitz actor supplies the valid one-step uniform
relative-cell interface.  It replaces the invalid inference that the
normalizer words themselves are `C_s tensor I`; the only tensor statement
concluded is `(TPA7)`, after finite-table exactification and four mixed Pauli
prototype checks.
