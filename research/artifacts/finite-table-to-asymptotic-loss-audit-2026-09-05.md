# Growing root tables: canonical trace accuracy does not authenticate regular multiplicity

This audit follows the new abelian atom-normalizer rounding theorem. It
isolates a second growing-window issue beyond propagation of relator
defect: canonical trace convergence on an expanding root table does not
imply the regular multiplicity hypothesis, even when the entire group table
is exact and the trace error tends to zero uniformly on that entire table.

The unconditional nonhyperlinear-group proof remains open. No computation
or numerical approximation is used below.

## An exact supercritical root table with uniformly canonical moments

Fix the native odd prime `p>=5`. For `t=p^k`, let `K=F_t` and let
`psi:K->C` be a nontrivial additive character. Take the additive root group

```text
H_t=K direct_sum K,                  |H_t|=t^2,
```

and the following exact representation on the `t`-dimensional space with
basis indexed by `x in K`:

```text
U_(a,b)e_x=psi(a x+b x^2)e_x.                          (GRA1)
```

Every multiplication relation of `H_t` holds exactly. Every nonidentity
matrix has order `p`. Its normalized character satisfies

```text
tr_t(U_(a,0))=0                         for a!=0,
|tr_t(U_(a,b))|=t^(-1/2)                for b!=0.      (GRA2)
```

The second formula follows without importing a Gauss-sum theorem. Put
`S=sum_x psi(a x+b x^2)`. Writing `u=x-y` in `|S|^2`,

```text
|S|^2=sum_u psi(a u+b u^2) sum_y psi(2b u y)=t.
```

For `u=0` the inner sum is `t`; for `u!=0` it is zero because `p` is odd
and `b!=0`. The first formula in `(GRA2)` is additive character
orthogonality.

In particular,

```text
max_(h!=0) |tr_t(U_h)|=t^(-1/2) -> 0,                  (GRA3)
||U_h-I||_2^2 >= 2-2t^(-1/2)              for h!=0.    (GRA4)
```

Thus all nonidentity root words are uniformly close to their canonical
trace and uniformly separated from the identity. There are `t^2` root
group elements, but the matrix dimension is only `t`.

## Their joint spectral multiplicity is maximally nonregular

The full dual group of `H_t` has `t^2` characters. Representation `(GRA1)`
uses only the `t` distinct characters

```text
(a,b) |-> psi(a x+b x^2),                  x in K,
```

each once. Hence its spectral distribution assigns mass `1/t` to those
`t` atoms and zero to all other atoms. Its total variation distance from
the uniform distribution on the full dual is

```text
1-1/t -> 1.                                              (GRA5)
```

A nonzero multiple of the regular representation has dimension at least
`t^2`; it cannot be obtained here by a flexible enlargement with dimension
ratio tending to one. This is not an issue of approximately commuting
matrices: the root table and joint PVM are exact from the outset.

The Fourier normalization explains the discrepancy. For an exact abelian
representation with spectral masses `mu_x`,

```text
sum_h |tr(U_h)-1_(h=0)|^2
 = |H| sum_x |mu_x-1/|H||^2.                            (GRA6)
```

In this example the left side is `t-1`: there are `t(t-1)` terms of
squared size `1/t`. The maximum trace error tends to zero, but the total
Fourier error needed to control the whole multiplicity distribution grows.

Consequently the following promotion is false:

> Exact growing finite abelian root tables, with maximum canonical trace
> error tending to zero on their entire tables, can be replaced at vanishing
> normalized cost by regular root packets of comparable matrix dimension.

The failure persists with a supercritical group size `|H_t|=d^2` and with
the strong uniform marked separation `(GRA4)`.

## Consequence for the new localization theorem

`abelian-root-average-placement-rounds-its-normalizer` assumes equal
multiplicities for all root characters. Its triple-expander refinement
retains this hypothesis. A fixed root table in canonical microstates meets
it asymptotically after finite-table corrections; a root table chosen from
the matrix dimension need not. Equations `(GRA1)`--`(GRA5)` disprove the
required uniform promotion even under stronger trace control than ordinary
fixed-window hyperlinearity supplies.

This identifies the next missing implication precisely. A growing-table
decoder must authenticate a positive-density, approximately uniform
character sector by additional actor relations or by a separately proved
aggregate multiplicity estimate. It cannot infer it from entrywise
canonical moments, even if every entry of the growing table is tested.

There is one concrete source of extra rigidity worth retaining: if exact
atom normalizers act transitively on a set of characters, then the ranks
of those character projections are equal. With approximate covariance, a
uniform classical gap can control the square-root rank profile. However,
the actual affine-Leavitt presentation must supply that covariance on the
same growing root algebra with a usable error ledger. The present example
does not supply those actors and is not a representation of the full
Steinberg presentation.

This audit therefore changes the proposed adaptive route in two places:
track the growing-table covariance loss and the growing-table multiplicity
loss separately. A successful estimate for just one does not justify the
other. The fixed-depth atom-matching theorem remains valid; it does not
provide the needed asymptotic density loss by itself.
