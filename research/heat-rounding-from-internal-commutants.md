---
rg: 2
id: heat-rounding-from-internal-commutants
kind: route
title: Identify admissible heat with the full commutant expectation and use internality on every bad subsequence
target: kazhdan-heat-maps-round-to-finite-algebras
requires:
  - kazhdan-commutants-are-internal
  - property-t-laplacian-sos-certificate
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
  - research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md
---

Use the target's fixed certificate and inverse-paired generating list.
Poisson expansion makes P_n(t) unital completely positive, trace preserving,
and contractive in operator norm and normalized L2. The expanded SOS error
satisfies

```
||(A_n^2-kappa A_n-sum_j X_(n,j)^*X_(n,j))x||_2
 <= C epsilon_n ||x||_op.
```

This follows by telescoping the fixed equality rows and the bound
`||(Ad W-Ad Z)x||_2 <= 2||W-Z||_2 ||x||_op`. With
`E_n(x)=<A_n x,x>`, differentiate heat energy and integrate to obtain

```
E_n(P_n(t)x) <= exp(-2 kappa t) E_n(x)
                   + C epsilon_n ||x||_op^2/kappa,
||P_n(t)x-x||_2^2 <= E_n(x)/kappa
                   + 2 C epsilon_n t ||x||_op^2/kappa.
```

For any free ultrafilter, the full asymptotic relations give a homomorphism
pi:G->U(M). Admissibility and the first inequality put every bounded heat
output in D=pi(G)' cap M. The second fixes every bounded representative of
an element of D, without any extra rate of commutator decay. Thus the
induced heat map is E_D, the full commutant expectation.

Internality supplies D=[B_n]_omega in the original dimensions. The maps
E_(B_n) induce E_D too: outputs lie in D, and the differences from the
inputs are L2-orthogonal to every bounded B_n sequence. Hence

```
||P_n-E_(B_n)||_(infinity->2) ->_omega 0.
```

Otherwise contractions witnessing the coordinate norms on an omega-large
set would contradict equality of the induced maps. This argument concerns
all bounded sequences, not merely fixed group words.

Finally put `r_n=inf_B ||P_n-E_B||_(infinity->2)`. If r_n did not tend to
zero, reindex a subsequence with r_n>=c>0 and apply the preceding argument
to any free ultrafilter on it. All full-relation and admissibility
conditions survive restriction, so this is a contradiction. Choose B_n
within 1/n of the infimum to get ordinary sequential rounding.

The proof rederives the applicable expectation-lift criterion directly;
it does not identify Liu's chosen averaging lengths with these heat times.
The universal internality prerequisite remains open.

**Attribution.** Commutant internality is the proposed theorem of Jihao Liu,
[*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7. The uniform expectation criterion is also recorded in his
Proposition 3.1. This route gives Cairn's conditional sequential heat
application, combining that analytic input with the earlier September 8
Cairn SOS heat proof. The bounded-sequence argument is written out to check
the interface, not to claim Liu's analytic contribution as new Cairn work.
