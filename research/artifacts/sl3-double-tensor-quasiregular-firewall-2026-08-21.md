# Tensor/contragredient audit for the SL3 arithmetic double

## Result

For a hypothetical canonical microstate sequence of

```text
SL_3(Z[1/2]) *_(SL_3(Z)) SL_3(Z[1/2]),
```

the diagonal tensor/contragredient representation with its maximally
entangled vector converges, as a pointed representation, to exactly

```text
(lambda_(A/C),delta_C).
```

This identifies the both-outlier sector with the exact quasi-regular leak
already isolated in Cairn.  It also gives a rigorous firewall against a
property-(T) or tensor-amplification shortcut.

## Coefficient computation

Let `Omega_d=d^(-1/2)sum_i e_i tensor conjugate(e_i)`.  Then

```text
<(U tensor conjugate(V))Omega_d,Omega_d>=tr_d(UV^*).
```

For the two vertex assignments this is the trace of the fold word at `a`.
It tends to one on `C`, where the two copies are identified, and to zero off
`C`, where the alternating word is Bass--Serre reduced.  Hence its limit is
the subgroup indicator `1_C`, whose GNS representation is quasi-regular.

## Why property (T) is consistent with the enemy

The limit vector is exactly fixed by `C` and has displacement `sqrt(2)`
under every `h notin C`.  This is an exact representation of `A`, not an
almost representation after taking the Hilbert ultraproduct.  Property (T)
of `C` merely recovers the already fixed vector; property (T) of `A` does
nothing because the vector is not almost invariant under an `A`-Kazhdan
set.  The non-coamenability of `C` in `A` is likewise consistent: it says
the quasi-regular representation has an `A`-spectral gap.

## Amplification accounting

For a degree-`k` tensor power, presentation defects are bounded by `k` times
the original normalized-HS defect.  The pointed coefficient becomes the
`k`th power of the original coefficient.  On the limiting `0/1` profile,

```text
1_C^k=1_C.
```

Thus every fixed tensor power returns the same wall.  Growing powers can be
kept approximate only while the degree times the relevant error tends to
zero (or under the corresponding square-error condition read directly from
the trace formula).  In that regime the off-subgroup coefficient remains
near zero, not near one.  There is no defect-versus-coefficient squeeze.

Exterior powers do not improve this: fixed degree is merely another
continuous functor of the same finite-coordinate data, while growing degree
has a degree-dependent Lipschitz constant and loses vanishing defect unless
extra estimates unavailable from canonical regularity are assumed.

## Exact endpoint

Writing the construction instead as a block-diagonal approximate
representation and a block swap produces a `C`-central unitary with exact
ultraproduct coefficient profile `1_C`.  Therefore the desired tensor
upgrade is precisely the SL3 instance of
`no-exact-quasi-regular-leak`.  Proving that named finite-dimensional
exclusion would close the double; ordinary property (T), tensor powers, and
exterior powers do not prove it.  A positive sofic model of the 2-adic
vertex action would instead realize the obstruction and refute collapse.
