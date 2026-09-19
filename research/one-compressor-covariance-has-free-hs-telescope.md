---
rg: 2
id: one-compressor-covariance-has-free-hs-telescope
kind: claim
title: One ascending-HNN covariance relation has dimension-free normalized-HS models at rate 2/sqrt(L)
distinct_from:
  ascending-hnn-cannot-create-nonhyperlinearity: that concludes hyperlinearity of the whole HNN group from a hyperlinear base by extension permanence (kernel a union of conjugates, quotient Z, amenable), and supplies no model and no rate; this is an explicit finite-dimensional construction for the covariance relation alone, needs no hypothesis on the base, and does not conclude hyperlinearity of any group.
  kun-thom-single-compressor-sofic-joint-nonsofic: that localizes the Kun--Thom obstruction by proving every one-compressor coset action sofic via the monomial ascending-HNN theorem, so it is restricted to nonnegative monomial compressors and lives in the permutation category; this is a tracial construction valid for an arbitrary injective endomorphism and an arbitrary finite-dimensional representation.
  ascending-hnn-base-profinite-closure-telescope: that computes the profinite closure of the base and concludes exact finite quotients cannot witness strict compression; this exhibits the approximate models that do exist once exactness is dropped, and quantifies their error.
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
---

Let `Lambda` be a group, `alpha : Lambda -> Lambda` an injective
endomorphism, and `rho : Lambda -> U(d)` any finite-dimensional unitary
representation.  For `L >= 1` put

```text
H_L = direct sum over j=0..L-1 of C^d,      dim H_L = L d,
Pi_L(gamma)|_(H_j) = rho(alpha^j(gamma)),                        (OCT1)
```

and let `T_L in U(H_L)` be the cyclic block shift `H_j -> H_(j-1)`, indices
mod `L`.  Then `Pi_L` is an **exact** unitary representation of `Lambda`,
and for every `gamma in Lambda`

```text
|| T_L Pi_L(gamma) T_L^(-1) - Pi_L(alpha(gamma)) ||_2 <= 2 / sqrt(L)
```

in the normalized Hilbert--Schmidt norm on `M_(Ld)`.  The bound is uniform
in `gamma` and **independent of `d`**: only one of the `L` equal blocks is
wrong, and the shift is exact on the other `L-1`.

So the single covariance relation `t gamma t^(-1) = alpha(gamma)` of an
ascending HNN extension admits arbitrarily accurate normalized-HS models for
free, with no hypothesis on `Lambda`, `alpha` or `rho` beyond the existence
of `rho`.

## Scope, stated so it is not overread

This constructs models of the *relation*, not a separated model of the HNN
group: nothing here separates elements of `<Lambda, t>`, and the claim
therefore does not by itself prove any group hyperlinear.  The stronger
conclusion for a hyperlinear base is already available by permanence
(`ascending-hnn-cannot-create-nonhyperlinearity`); what is added here is the
explicit model and the rate, which permanence does not supply.

## Where this leaves the compression semigroup

The obstruction in the Kun--Thom geometry is therefore not carried by any
single compressor -- a conclusion the graph already reaches twice, by
permanence and by soficity of every one-compressor coset action
(`kun-thom-single-compressor-sofic-joint-nonsofic`).  This claim adds the
quantitative form of that statement: the one-compressor problem is not merely
solvable but solvable at a dimension-free rate, so no accounting of model
dimension can recover an obstruction from one covariance.  What must fail is
the *simultaneous* compatibility of the whole infranormal compression
semigroup with a wall that stays macroscopically visible.
