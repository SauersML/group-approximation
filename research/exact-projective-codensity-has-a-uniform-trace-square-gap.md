---
rg: 2
id: exact-projective-codensity-has-a-uniform-trace-square-gap
kind: claim
title: Perfect Kazhdan co-density has a uniform projective trace-square transfer gap on exact representations
distinct_from:
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that starts from ordinary almost-commutation and an exactified ambient representation; this converts projective trace-square energy to ordinary almost-commutation uniformly before applying the same co-density mechanism.
  projective-trace-square-transfer-for-sl3-pair: that asks for the inequality on arbitrary approximate assignments of the ambient presentation; this proves it with zero error on every exact finite-dimensional ambient representation.
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that uses a nonperfect rank-one subgroup and congruence property tau; this uses perfectness and genuine property (T) of the rank-three subgroup to remove scalar phases.
---

Let `C<=A` be finitely generated groups.  Fix a finite generating set `S` of
`C` and an element `h in A`.  Assume:

1. `C` is perfect;
2. `C` has property (T), with Kazhdan constant `kappa>0` for `S`; and
3. the pair is finite-dimensionally co-dense:

```text
rho(C)'=rho(A)'                                         (EPT1)
```

for every finite-dimensional unitary representation `rho` of `A`.

Then there is `K<infinity`, depending only on `C,S,h` and `kappa`, such that
for every exact finite-dimensional unitary representation `rho:A->U(d)` and
every `U in U(d)`, with normalized trace,

```text
1-|tr([U,rho(h)])|^2
 <= K sum_(s in S) (1-|tr([U,rho(s)])|^2).             (EPT2)
```

In particular `(EPT2)` applies to

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),
h=diag(2,1,1/2).                                       (EPT3)
```

The constant is independent of `d`, of the congruence level through which
`rho` factors, and of its irreducible multiplicities.

## Proof

Put

```text
w_g=U rho(g) U^* rho(g)^*,
D_g=inf_(z in T)||w_g-zI||_2.                          (EPT4)
```

For a unitary `w`, choosing the phase of its normalized trace gives

```text
inf_(z in T)||w-zI||_2^2
 =2-2|tr(w)|
 <=2(1-|tr(w)|^2).                                    (EPT5)
```

The cocycle identity

```text
w_(gh)=w_g rho(g) w_h rho(g)^*                        (EPT6)
```

shows that projective errors telescope along words.  Here is the phase
bookkeeping explicitly.  Enlarge `S` to be symmetric.  For each `s in S`
choose `z_s in T` with

```text
||w_s-z_s I||_2=D_s,
```

choosing `z_(s^-1)=conj(z_s)`.  If `q=s_1...s_m` is a word, repeated use of
`(EPT6)` gives

```text
||w_q-(z_(s_1)...z_(s_m))I||_2 <= sum_j D_(s_j).       (EPT6a)
```

In particular the phase on a commutator word is exactly one.  Since `C` is
perfect and `S` is finite, choose once and for all, for every `s in S`, a
word equal to `s` which is a finite product of commutators of words in `S`.
Let `L` be the maximum total letter length of those fixed words.  Exactness
of `rho`, `(EPT5)`, and `(EPT6a)` give

```text
max_(s in S)||w_s-I||_2
 <= L sqrt(2 E),
E=sum_(s in S)(1-|tr(w_s)|^2).                         (EPT7)
```

Apply property (T) to the conjugation representation of `C` on the normalized
Hilbert--Schmidt space `M_d`, with vector `U`.  If `Q` is the orthogonal
projection onto `rho(C)'`, then

```text
||U-Q(U)||_2<=L sqrt(2E)/kappa.                        (EPT8)
```

By co-density `(EPT1)`, `Q(U)` commutes with `rho(h)`.  Therefore

```text
||[U,rho(h)]-I||_2
 =||U rho(h)-rho(h)U||_2
 <=2||U-Q(U)||_2.                                     (EPT9)
```

Finally, for every unitary `v`,

```text
1-|tr(v)|^2<=2-2 Re tr(v)=||v-I||_2^2.                (EPT10)
```

Combining `(EPT8)--(EPT10)` proves `(EPT2)`, for example with

```text
K=8L^2/kappa^2.                                       (EPT11)
```

For `(EPT3)`, elementary matrices generate `SL_3(Z)` and

```text
e_ij(1)=[e_ik(1),e_kj(1)]
```

for distinct `i,j,k`, so the subgroup is perfect.  It has property (T).
Finite-dimensional unitary superrigidity for this higher-rank
`S`-arithmetic group makes every such image finite.  Congruence subgroup
rigidity then makes it a congruence image away from `2`, and reduction of
`SL_3(Z)` is already onto that image.  Hence

```text
rho(SL_3(Z))=rho(SL_3(Z[1/2])),
```

which is stronger than `(EPT1)`.

## Consequence for the open projective transfer

The exact finite-quotient/projective-centralizer falsification gate in
`projective-trace-square-transfer-for-sl3-pair` is closed.  Any failure of
that claim must be a genuinely uniform-outlier sequence of approximate
representations of `SL_3(Z[1/2])`; it cannot persist after dimension-free
correction to exact representations.  Thus the remaining term
`eta(delta)` is precisely an adjoint/projective lifting problem for the
ambient presentation.
