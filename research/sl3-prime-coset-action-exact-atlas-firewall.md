---
rg: 2
id: sl3-prime-coset-action-exact-atlas-firewall
kind: claim
title: Every one-prime SL3 coset atlas is either nonsofic or essentially noncorrectable
distinct_from:
  sl3-dyadic-building-action-soficity-forces-p-instability: that is the p=2 instance; this packages the exact obstruction uniformly for every prime, including the p at least eleven action fork left by the central-dual program.
  sl3-finite-building-quotients-forget-arithmetic-labels: that is the covering-space descent obstruction for unlabelled finite building quotients; this excludes every exact finite Gamma-action atlas quantitatively, whether congruence, noncongruence, or obtained by some other construction.
  coordinate-action-not-sofic: that proves nonsoficity for the Kun--Thom compression pair; this does not decide soficity and instead isolates the only sector in which a positive arithmetic model could live.
---

Fix a prime `p`, put `Gamma=SL_3(Z[1/p])`, `Lambda=SL_3(Z)`, and
`X=Gamma/Lambda`.  Choose a finite Kazhdan generating set of `Lambda`, with
Kazhdan constant `kappa>0`, and choose `h in Gamma\Lambda`.  Then every
orbit atlas for the two-site window

```text
{Lambda, h^(-1)Lambda} subset X
```

inside an exact finite action of `Gamma` has normalized error at least

```text
delta_kappa = kappa^2/(2 kappa^2+8).                             (PAF1)
```

Consequently, if `Gamma curvearrowright X` is sofic, every witnessing
sequence is uniformly outside the flexibly correctable closure of exact
finite `Gamma`-actions.  In particular, no proof through subgroup
separability, finite equivariant quotients, or congruence actions can
establish its soficity.

This leaves a precise positive sector: coherent approximate arithmetic
labels whose multiplication and orbit charts improve on each finite word
window but which remain a fixed Hamming distance from every exact action.
Unlabelled finite quotients of the Bruhat--Tits building do not supply these
labels by `sl3-finite-building-quotients-forget-arithmetic-labels`; a
building construction must round its deck cocycles coherently without ever
rounding the resulting almost-action to a genuine action.

The standard general criteria do not settle this sector:

- the GKP locally-finite-stabilizer theorem does not apply because
  `Lambda` is infinite (indeed finitely generated and Kazhdan);
- the later Gao--Patchell--Kunnawalkam Elayavalli graph-action theorem does
  prove soficity for sofic actors with amenable stabilizers, but it does not
  apply because `Lambda` is nonamenable;
- LERF/subgroup-separability methods fail maximally:
  `sl3-prime-permutation-codensity` says the profinite closure of `Lambda`
  is all of `Gamma`, so the only finite equivariant quotient of `X` is a
  point; because `Lambda` is finitely generated, it is not even a Chabauty
  limit of finite-index subgroups, so the rooted-Schreier/co-sofic subgroup
  criterion also fails;
- Kun--Thom's infranormal-compression criterion is unavailable by
  `arithmetic-integral-subgroup-is-incompressible`.

None of these failures proves nonsoficity.  Equation `(PAF1)` says exactly
what remains to be overcome: the action-soficity fork is an outlier-atlas
problem, not a search for better exact arithmetic quotients.

There is, however, a strictly weaker closure target than flexible
P-stability: `sl3-prime-stable-finite-actions-excludes-coset-soficity` shows
that stability in finite actions of the actor already rules out the outlier
atlases.  That named modulus is not currently known for this residually
finite S-arithmetic group.

DERIVATION
sl3-prime-coset-action-exact-atlas-firewall-proof
