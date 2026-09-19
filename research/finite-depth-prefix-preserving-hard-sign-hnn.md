---
rg: 2
id: finite-depth-prefix-preserving-hard-sign-hnn
kind: claim
title: Fixed-depth HNN rows transport hard signs without leaking from earlier pulse prefixes
distinct_from:
  packet-hard-transport-preserves-pulse-prefix: That asks for one uniform clocked presentation with polynomial control at every level; this uses the finite depth actually sufficient for one existence witness and permits a separate HNN row at each level.
  product-clock-synchronizes-fanizza-and-e5: That generates all level words from one product clock; this directly lists the finitely many marked abelian subgroup isomorphisms needed up to the chosen terminal depth.
---

**ESTABLISHED.**  Fix `N`.  Let `B_0,...,B_(N-1)` be independent commuting
involutions.  For every `n<N`, let `A_n` be an involution commuting with all
`B_k`, and assume

```text
<A_n,B_0,...,B_(n-1)> ~= C_2^(n+1).                    (FDP1)
```

Form the iterated HNN extension with stable letters `V_n` and relations

```text
V_n A_n V_n^(-1)=B_n,
V_n B_k V_n^(-1)=B_k                 (k<n).             (FDP2)
```

Each row is an HNN extension along an isomorphism between two marked copies
of `C_2^(n+1)`, so all preceding base groups embed.

Put

```text
C_n=product_(k<n)(1+B_k)/2.                            (FDP3)
```

Then `V_n C_n=C_n V_n`.  Consequently, for every projection `P_n<=C_n`,

```text
(1-C_n)V_nP_n=0.                                       (FDP4)
```

If additionally `A_nP_n=-P_n`, the transported projection lies in the
negative `B_n` sector:

```text
(1+B_n)V_nP_n=0.                                       (FDP5)
```

Thus it lies in the genuine first-hit projection

```text
X_n=C_n(1-B_n)/2,
```

and the `X_n` are pairwise orthogonal.  For approximate normalized-HS
representations, fixed-group exactification and telescoping the `n+1`
relations in `(FDP2)` give prefix leakage bounded by `C N sqrt(E)`; no
ambient-dimension constant occurs.

This finite-depth form is sufficient for an existence proof: after the
marked density and exit fraction are fixed, choose one finite
`N>1/(eta q_*)` and include only these finitely many rows.  A uniform
all-depth clock is needed for a machine-indexed family, not for one witness
group.

The destination signs need not be listed as `N` unrelated generators.
`baumslag-torsion-host-is-a-quadratic-hs-address-register` realizes them as
the first `N` lamps in one three-generator finitely presented metabelian
group, with quadratic normalized-HS authentication cost.  This compresses
the address register only; the source signs and the `N` payload-carrying HNN
rows remain part of the fixed-depth witness.
