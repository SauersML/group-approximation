---
rg: 2
id: positive-rope-profinite-edge-synchronization
kind: claim
title: The positive Higman rope admits cofinal finite quotients synchronizing its graph edge
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

