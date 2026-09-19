# One group-like gauge does not scalarize the packet multiplicity

Date: 2026-08-14

## 1. Outcome

The two strongest current reductions do not combine automatically.

* `TRUE_COPRODUCT_DEFECT_PINS_COMMUTANT_GAUGE.md` says that one repaired
  compressor gauge with vanishing coproduct defect becomes a PVM-valued
  direct sum of right translations.
* `TRUE_FULL_PACKET_GAP_SPLITS_INTO_RIGHT_SHIFT_OR_MULTIPLICITY.md` says that
  the transported carrier is detected either by a recovered right shift or
  by a pure multiplicity unitary.

It is tempting to conclude that a group-like compressor gauge collapses the
multiplicity branch to the right-shift branch. That implication is false,
even with zero defect and with exactly the packet constants `1/4`, `3/16`,
and `3/8`.

The missing relation must couple the transported carrier to the coefficient
PVM of the actual gauge. Controlling the gauge alone does not control the
rest of its commutant.

## 2. Exact countermodel

Let `K` be any nontrivial finite group and put

```text
M = B(l2(K)) tensor M_4(C),
A = C[lambda_K(K)] tensor 1.                         (OCG1)
```

Write `rho_K` for the right regular representation, so

```text
A' = C[rho_K(K)]'' tensor M_4(C).                   (OCG2)
```

Choose any `g in K`, and let

```text
C = rho_K(g) tensor 1.                              (OCG3)
```

For the group coproduct on the right regular algebra,

```text
Delta(rho_K(h))=rho_K(h) tensor rho_K(h),            (OCG4)
```

the gauge `C` is exactly group-like:

```text
Delta(C)=C_13 C_23.                                 (OCG5)
```

Its coefficient PVM has one nonzero atom, equal to `1`. Thus this is already
the strongest possible output of the coproduct-classification theorem.

Now take a rank-one projection `p in M_4(C)` and set

```text
F = 1 tensor p.                                     (OCG6)
```

Then `F` commutes with every recovered right shift:

```text
[F,rho_K(h) tensor 1]=0              for all h in K. (OCG7)
```

It also commutes with the actual group-like gauge `C`. Nevertheless, the
trace-preserving expectation onto `A` is

```text
E_A(F)=(1/4)1,                                      (OCG8)
```

and therefore

```text
dist_2(F,A)^2
 =tau(F)-tau(F)^2
 =1/4-1/16
 =3/16.                                             (OCG9)
```

This is exactly the full raw-packet gap.

## 3. The multiplicity witness survives perfectly

Choose a unitary `W in U(4)` which moves the range of `p` to an orthogonal
rank-one subspace. Then

```text
V=1 tensor W in A',                                 (OCG10)
```

while

```text
||[V,F]||_2^2=1/2.                                  (OCG11)
```

Indeed, `VpV*` and `p` are orthogonal rank-one projections, so their squared
distance in normalized `M_4` trace is `1/2`; unitary invariance identifies
that distance with the squared commutator norm. The value is larger than the
general Haar floor `3/8`.

Thus all of the following hold simultaneously and exactly:

```text
right-shift synchronization,
zero coproduct defect for the actual gauge,
classical/PVM gauge classification,
the full 3/16 packet-algebra distance,
an order-one pure multiplicity witness.             (OCG12)
```

## 4. Why the tempting inference fails

The coproduct equation classifies one distinguished unitary

```text
C=sum_(h in K) rho_K(h) tensor P_h.                 (OCG13)
```

It says that `(P_h)` is a PVM. It does not say that this PVM generates the
whole multiplicity algebra, nor that an unrelated transported carrier is
measurable with respect to it. In `(OCG3)`, the coefficient PVM is trivial,
so it contains no multiplicity information at all.

Even if `F` commutes with `C` and all right shifts, coefficient comparison
only implies that `F` commutes with the particular projections `P_h`. It
does not imply commutation with every element of `M_4(C)`, and hence does not
put `F` in `A=A''`.

The amplification principle makes this obstruction unavoidable. Tensoring
any exact packet by an arbitrary finite multiplicity space preserves all
group relations and normalized traces, while introducing a fresh matrix
algebra in the packet commutant. No theorem about one group word can erase
that algebra unless another relation makes the transported carrier depend
on the word's coefficient projections.

## 5. Corrected live theorem

The compiled-word program now needs a **carrier-coupled** conclusion, not
only gauge classification. Any one of the following would suffice:

1. prove that `F_n` is asymptotically measurable with respect to the
   coefficient PVM `(P_(h,n))` of the actual repaired compressor gauge;
2. produce finitely many group-like repaired gauges whose coefficient PVMs
   generate the multiplicity algebra seen by `F_n`; or
3. use the intrinsic transition effects
   `P U*Q_j U P` to show directly that every centered multiplicity
   coefficient of `F_n` has vanishing Hilbert--Schmidt norm.

Option 3 is currently the most intrinsic. The transition effects are built
from the actual compressor and carrier, so unlike the abstract gauge in
`(OCG3)` they cannot be tensored with an unrelated rank-one projection
without changing the tested operator.

The revised endpoint is:

> **Carrier-coupled coproduct gate.** Bound both the coproduct defect of the
> repaired compressor gauge and the conditional variance of the transported
> carrier relative to its coefficient PVM by the mixed compiled-word relator
> energy, with constants independent of representation multiplicity.

The first bound alone is insufficient by `(OCG1)--(OCG12)`. The second is
the genuinely new content required to close the full-packet bicommutant
gate.
