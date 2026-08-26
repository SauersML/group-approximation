# Audit of finite congruence extension for the positive Higman rope

The route `mf-safe-rope-via-profinite-synchronization` reduces the analytic
MF problem to the following algebraic datum.  For every finite quotient
`beta:Q->B`, find a finite quotient `alpha:Gamma->C` such that

```text
ker(alpha|S) <= ker(beta tau),                          (1)
```

and do this in cofinal computable families which also separate `Gamma`.

## 1. The condition is a finite congruence extension condition

Condition `(1)` says that `beta tau:S->B` factors through the finite image
`alpha(S)`.  Equivalently, the quotient `S/ker(beta tau)` embeds as a quotient
of `alpha(S)` in a finite quotient of `Gamma`.  If one can choose `alpha` with
equal kernel, this is precisely extension of the finite congruence
`ker(beta tau)` from `S` to `Gamma`; the inclusion in `(1)` is the slightly
more flexible form actually needed by the matrix argument.

Ordinary residual finiteness of `Gamma` and `Q` does not imply `(1)`.  It
separates individual elements independently, whereas `(1)` must kill the
entire, generally infinitely generated, kernel of `beta tau` in one quotient
while retaining the finite quotient `B`.

## 2. Why a retract cannot supply it

A retraction `r:Gamma->S` would extend every finite quotient of `S` by
composition.  A virtual retraction would do the same after passing to a
finite-index subgroup and then inducing to a finite wreath product.  Neither
architecture is available in this compiler.

On the positive branch, the finitely generated recursive presentation `Q`
is the endpoint of an indefinitely delayed monotone FIN/INF switch.  If `Q`
were finitely presented, its defining normal subgroup in the finite-rank free
group would be finitely normally generated.  All of those generators would
occur at one finite stage, so the stream would already have reached `Q` at
that stage.  A finite enumeration stopping after the same stage would then
give the same group, contradicting the required negative branch.  Therefore
`Q` is not finitely presented.

For `S=F *_N F`, quotient by the normal closure of the second copy of the
finite-rank free group.  The result is `F/N=Q`.  If `S` were finitely
presented, adding the finitely many relations killing that second free factor
would finitely present `Q`.  Hence `S` is not finitely presented either.

Retracts of finitely presented objects are finitely presented.  If `S` were a
virtual retract of finitely presented `Gamma`, it would be a retract of a
finite-index subgroup of `Gamma`; that subgroup is finitely presented, again
forcing `S` finitely presented.  Thus no retract or virtual-retract refinement
of the benign witness can prove `(1)`.

## 3. Wagner CEP does not by itself give finite quotients

Francis Wagner, *Malnormal Subgroups of Finitely Presented Groups*,
arXiv:2404.00841, proves that every finitely generated recursively presented
group admits a malnormal quasi-isometric CEP embedding in a finitely presented
group.  In the paper's definition, CEP says that an epimorphism

```text
S -> S/K
```

extends to an epimorphism `Gamma->H_K` for some group `H_K` containing `S/K`.
Equivalently, there is `M normal Gamma` with `M intersect S=K`.  Neither
formulation says that `H_K` is finite or residually finite when `S/K` is
finite.  The paper's additional positive conclusion is decidability of the
ambient word problem when the source word problem is decidable, which also
does not imply residual finiteness.

Therefore Wagner CEP embeds `S/K` in a finitely presented quotient, while
the profinite synchronization route needs it embedded in a finite quotient.
One extra theorem would suffice:

```text
for each relevant finite-index K normal S,
Gamma/normalClosure_Gamma(K) is residually finite.       (2)
```

Indeed `(2)` plus CEP lets finitely many finite quotients of that ambient
quotient jointly embed the finite subgroup `S/K`, yielding `(1)`.  No such
residual-finiteness statement is present in Wagner's theorem or in the
current benign-witness construction.

## 4. Exact remaining construction target

The next positive target is not generic subgroup separability and not
ordinary CEP.  It is an effective **finite CEP** for only the quotient family
`ker(beta tau)` arising from finite quotients of the positive scaffold `Q`,
plus a cofinal finite quotient family separating `Gamma`.  This is strictly
weaker than asking every finite quotient of `S` to extend, and should be kept
in this tailored form when redesigning the benign witness.
