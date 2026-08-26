---
rg: 2
id: positive-rope-profinite-edge-synchronization
kind: claim
title: The positive Higman rope admits cofinal finite quotients synchronizing its graph edge
artifacts:
  - research/artifacts/positive-rope-profinite-route-audit-2026-08-25.md
distinct_from:
  coordinate-swap-rope-does-not-compress-kernel: that symmetrizes the presentation before the recursive kernel is imposed and thereby loses compression; this asks for compatible quotients of the already correct rope group.
  higman-half-row-has-regular-mf-benign-witness: that supplies a regular-MF benign witness but no cofinal finite quotient family and no compatibility with the quotient-valued graph map.
  profinite-synchronized-hnn-is-regular-mf: that is the general permanence theorem consuming synchronization; this is the rope-specific construction of its hypotheses.
---

On the `W_e`-infinite branch of the MF-safe Higman compiler, arrange the
correct rope data

```text
S=F *_N F <= Gamma,             Q=F/N,
tau:S->Q,                       tau|F_0=q, tau|F_1=1,
theta_0(s)=(s,1),               theta_1(s)=(s,tau(s))
```

so that `A=Gamma times Q` has a computable cofinal sequence of finite
quotients `p_n:A->A_n` satisfying

```text
ker(p_n o theta_0)=ker(p_n o theta_1)                  (RPS1)
```

for every `n`.  Equivalently, for product quotients
`p_n=(alpha_n,beta_n)`, require

```text
ker(alpha_n|S) <= ker(beta_n o tau).                   (RPS2)
```

The sequences must eventually separate every nonidentity element of both
`Gamma` and `Q`, and the construction must be uniform in the presentation
index.  Together with `profinite-synchronized-hnn-is-regular-mf`, this makes
the final graph HNN MF without changing its Britton compression semantics.

## Attempts

The regular-MF half-row witness does not automatically provide finite
quotients, much less `(RPS2)`.  Residual finiteness of the two vertex groups
alone is also insufficient: the finite quotient of `Q` must be continuous
for the subspace profinite topology that `S` inherits from `Gamma`.

The coordinate-swap construction gives exact compatibility before passing to
finite quotients, but it violates the algebraic compression requirement and
therefore cannot establish this claim.  The next attack is to inspect whether
the benign-witness operations can be chosen with a congruence-extension
property for `S<=Gamma`; that property would extend each `beta o tau` to a
finite quotient of `Gamma` and imply `(RPS2)`.

There is now a sharper sufficient condition which does not ask for generic
finite CEP.  If the benign witness `(K,e,L)` carries a homomorphism
`sigma:K->Q` extending `q:F->Q` and killing `L`, then every finite quotient
`beta:Q->B` produces a finite quotient of `Gamma` into
`(B times B) semidirect C_2`: map `K` into the first coordinate and map the
first rope letter to the coordinate swap.  Projection onto the first
coordinate on `S` is exactly `beta tau`.  This proves `(RPS2)` once `Gamma`
and `Q` are effectively residually finite.  The remaining construction is
isolated as `positive-scaffold-has-quotient-compatible-rf-witness`.

There are two cautions on that attack.

- **Retracts and virtual retracts are impossible here.**  On the positive
  branch `Q` cannot be finitely presented: if a monotone relator stream on a
  finite alphabet reached a finitely presented limit, compactness of normal
  generation would make it reach that limit at a finite stage, contradicting
  the FIN/INF switch.  Moreover, killing the second free factor in
  `S=F *_N F` gives `Q`; hence finite presentability of `S` would imply finite
  presentability of `Q`.  Thus `S` is not finitely presented.  A retract, and
  also a virtual retract, of a finitely presented group is finitely
  presented, so neither can be the source of `(RPS2)`.
- **Ordinary CEP is too weak.**  Wagner's congruence-extension refinement of
  Higman embedding extends a finite quotient `S->S/K` to a quotient of the
  ambient finitely presented group in which `S/K` embeds, but the ambient
  quotient need not be finite or residually finite.  What `(RPS2)` needs is
  the finite congruence extension property: every relevant finite quotient of
  `S` must embed in an actual finite quotient of `Gamma`.  This stronger
  property is not supplied by the cited CEP theorem.
