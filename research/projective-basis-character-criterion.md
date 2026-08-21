---
rg: 2
id: projective-basis-character-criterion
kind: claim
title: A group character gives a projective orthonormal basis exactly when it vanishes off its scalar kernel
distinct_from:
  thom-central-corner-criterion: that compiles a known finite-valued twisted group factor into a central corner of an ordinary group factor; this characterizes when a GNS factor natively is a twisted group factor.
---

Let `chi` be a character of a countable group `G`, with faithful GNS trace and
representation `pi_chi`, and put

```text
N_chi={g:|chi(g)|=1}={g:pi_chi(g) is scalar}.
```

The images of `G`, modulo scalar multiples, form a projective orthonormal basis
of `L^2(M_chi)` if and only if

```text
chi(g)=0  for every g notin N_chi.
```

In that case `N_chi` is normal and

```text
M_chi isomorphic_to L_omega(G/N_chi)
```

for the multiplier obtained from a section of `G/N_chi`. The basis can be
rephased so that `omega` takes values in `mu_m` if and only if its cohomology
class is `m`-torsion.

Consequently any named non-Connes-embeddable character with one word satisfying
`0<|chi(w)|<1` fails this native twisted-group-factor test immediately.
