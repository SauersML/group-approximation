---
rg: 2
id: pure-prefix-swap-invariants-are-selector-blind
kind: claim
title: Pure invariants of the prefix swap cannot authenticate its coarse-to-fine selector covariance
distinct_from:
  coarse-fine-selector-covariance-has-quarter-trace-floor: that proves the mixed selector-covariance trace floor directly; this classifies why every invariant of the prefix word alone, including its extensive rectangular index, fails to authenticate that mixed covariance.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that proves the rank floor after the off-diagonal source Gram has been authenticated; this proves that determinant, spectrum, index and pure cyclic traces cannot perform that authentication.
---

**ESTABLISHED NO-GO.**  Let `P` be the common identity of exact coarse
`M_2` and fine `M_4` matrix-unit packets in a finite matrix algebra, and put

```text
e=e_11,                 f=f_11,
X=fJe                                                   (PSI1)
```

for a unitary involution `J`.  No determinant, spectral multiplicity,
Fredholm index, or cyclic trace formed from `J` alone can authenticate the
source Gram `X^*X ~= e`.

## A canonical-trace countermodel with all pure invariants fixed

Take `P=I` on `C^(8m)` and fix

```text
J=diag(I_(4m),-I_(4m)).                                (PSI2)
```

Thus

```text
J^2=I,       tr(J)=0,       det(J)=1,
tr(J^k)=0 for k odd,        tr(J^k)=1 for k even.       (PSI3)
```

Its two spectral multiplicities are both `4m`; in particular `(PSI3)` is
exactly the canonical normalized-trace profile of a nonidentity involution.
Choose the coarse atom `e` to be the `+1` eigenspace of `J`, of rank `4m`,
and complete it to an exact `M_2` packet.  There are two exact `M_4` packets
with the same identity `P`:

1. choose the first fine atom `f_in` of rank `2m` inside `e`;
2. choose the first fine atom `f_out` of rank `2m` inside `1-e`.

The remaining three equal-rank atoms can be completed to matrix units in
both cases.  All pure data in `(PSI3)`, and all separate coarse/fine packet
types and ranks, are identical.  Nevertheless

```text
||e-(f_in J e)^*(f_in J e)||_2^2  =1/4,
||e-(f_out J e)^*(f_out J e)||_2^2=1/2.                (PSI4)
```

Hence even the value of the Gram defect is not determined by the complete
spectral distribution of `J` together with the two packet dimensions.
Because `J^2=1`, every pure cyclic moment of `J,J^*` reduces to one of the
two moments in `(PSI3)`, so adding finitely or infinitely many such moments
does not help.

## The apparent index certificate is tautological

Regard `T=fJe` as a rectangular map `eH -> fH`.  In finite dimensions,
rank--nullity gives, for every `J`,

```text
ind(T)=dim ker(T)-dim coker(T)
      =rank(e)-rank(f)=rank(P)/4.                       (PSI5)
```

Thus the index density is extensive and amplification-stable, but it is
already fixed before the word `J` is evaluated.  It detects the static
`2`-versus-`4` rank mismatch; it does not authenticate that `J` attempts a
source-full transport.  Likewise `T^*T` has nullity at least `rank(P)/4`,
so its determinant is zero for every `J`.  A pseudodeterminant merely reads
the selector-dependent singular values and has no stable phase shortcut.

Even the determinant of the natural selector commutator is blind.  For

```text
R_e=1-2e,       R_f=1-2f,       C=R_f J R_e J^*,       (PSI6)
```

one has

```text
det(C)=det(R_f)det(R_e),                                (PSI7)
```

independent of `J`; tensor amplification can also erase any residual parity.

## The unique scalar boundary is a mixed selector moment

There is a useful scalar, but it necessarily contains both selectors:

```text
D(J;e,f)=tr(e)-tr(fJeJ^*)
        =||(1-f)Je||_2^2
        >=tr(e)-tr(f)=tr(P)/4.                         (PSI8)
```

The equality is trace cyclicity and the inequality is `tr(fJeJ^*)<=tr(f)`.
Moreover, with `L=(1-f)Je`, one has

```text
e-X^*X=L^*L,       ||e-X^*X||_2^2<=D(J;e,f).           (PSI9)
```

Thus small `D` would authenticate the desired source Gram.  Formula `(PSI8)`
is not an alternative to the missing selector-covariance theorem: it is
exactly its scalar form.

Consequently a genuinely finite-matrix completion of the prefix-swap route
must make named relator defect control the mixed moment
`tr(fJeJ^*)` (or the equivalent reflection-word defect).  It cannot be a
determinant, a multiplicity count of `J`, a Fredholm index of the rectangular
compression, or any canonical trace involving only powers of the one word
`J`.  If the mixed covariance is imposed as a universal group-algebra
identity, the same rank floor holds in every finite tracial von Neumann
algebra and kills the positive regular carrier; the required control must
therefore remain matrix-only.
