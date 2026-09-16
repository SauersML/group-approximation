---
rg: 2
id: homogeneous-quotient-ce-frees-sl3-lamp-seed
kind: claim
title: Connes embeddability of the SL3 homogeneous quotient keeps the two-point lamp seed and its central D8 mark out of the hyperlinear radical
distinct_from:
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that consumes the same Connes-embeddable crossed product to refute relative-commutant collapse for group microstates of the arithmetic pair; this consumes it to keep the two-point lamp seed, and the central D8 mark over it, outside the hyperlinear radical of the permutational lamp groups, which excludes every uniform finite-window estimate for the marked host.
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open embeddability hypothesis itself; this is an established implication from that hypothesis, plus its unconditional contrapositive, and decides neither side.
  sl3-codense-coset-lamp-recursive-host: that proves exact finite-dimensional invisibility of the arithmetic lamp mark; this concerns visibility of the same mark in tracial matrix ultraproducts, which is what the analytic interface would have to kill.
  infinite-character-interface-is-marked-radical-certificate: that shows any uniform interface already certifies the mark in the hyperlinear radical; this shows that for the SL3 host, under the embeddability hypothesis, the mark is not in the radical, so no such certificate exists.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that uses the weakly mixing coset Bernoulli shift over SL3(Z[1/3]); this uses the compact homogeneous quotient of SL3(Q_2), where the moved invariant set is a compact-open orbit indicator.
  sl3-two-point-lamp-mark-is-single-rcc-scalar: that reduces collapsing the mark to one projective relative-commutant scalar estimate; this shows, under the embeddability hypothesis, that the mark survives in some tracial ultraproduct, so every collapse mechanism fails, not only the scalar transfer.
artifacts:
  - research/artifacts/seed-radical-transfer-2026-09-16.md
---

**ESTABLISHED as an implication** by route `homogeneous-quotient-ce-frees-sl3-lamp-seed-proof`. The hypothesis
`(SH1)` is open and is not decided here.

**Setting.**

```text
A = SL_3(Z[1/2]),  C = SL_3(Z),  K = SL_3(Z_2),  h = diag(2,1,1/2),
X = A/C,  L = directSum_X F_2,  L_0 = augmentation submodule,
m_0 = delta_C + delta_(hC),
P_host = P(L rtimes A, m_0),   P_host^0 = P(L_0 rtimes A, m_0),
```

where `P(G,b) = <G, z, J | z^2 = J^2 = 1, J central, [b,z] = J>` is the central D8 seed construction. This is the
host of `sl3-codense-coset-lamp-recursive-host` with the choice `a = h`, and its augmentation variant.

**Hypothesis `(SH1)` for `Lambda'`.** `Lambda' < SL_3(Q_2)` is a torsion-free cocompact lattice with `r >= 2` orbits
of `K` on `Y = SL_3(Q_2)/Lambda'`, and `L^infinity(Y) rtimes A` is Connes embeddable.

**Theorem.** Assume `(SH1)` for some such `Lambda'`.

- **(D1)** `m_0 notin Rad_hyp(L rtimes A)` and `m_0 notin Rad_hyp(L_0 rtimes A)`.
- **(D2)** `J notin Rad_hyp(P_host)` and `J notin Rad_hyp(P_host^0)`. Some homomorphism into a tracial matrix
  ultraproduct sends `J` to `-1`.
- **(D3)** For every finite presentation window of `P_host` or `P_host^0`, every word `w_J` representing `J`, and
  every `delta > 0`, there are finite-dimensional unitary tuples with all windowed relator defects below `delta` and
  `||w_J(U) - I||_2 > 2 - delta`. So the terminal estimate `(ICR2)` of
  `infinite-character-interface-is-marked-radical-certificate` fails for this host. Any uniform actor word-energy
  interface for this packet would imply `(ICR2)`, so no such interface exists.

**Unconditional contrapositive.** `A = <C,h>`. Any proof that `J in Rad_hyp(P_host)`, and in particular any proof of
the uniform interface for this host, proves that every p.m.p. action of `A` with Connes-embeddable crossed product has
`L^infinity(Z)^C = L^infinity(Z)^A`. So it would prove `(SH1)` false for every such `Lambda'`. Finite-quotient
codensity makes this rigidity automatic for profinite actions, so it has no finite-level content.

**Consequence for the frontier.** Under `(SH1)`, the mechanism of `sl3-codense-lamp-higman-route` is excluded for
this host: its interface requirement fails. This is in addition to the projective-transfer routes that `(SH1)`
already invalidates. Hyperlinearity of `P_host` itself is not decided: it could be nonhyperlinear for reasons
unrelated to the seed.

**Scope of the obstruction (referee addition).** `(D3)` concerns the recursively presented host `P_host` (and
`P_host^0`) itself, which is the host to which `sl3-codense-lamp-higman-route` applies the interface. It does not
exclude an interface for a different packet, and in particular not for a finitely presented overgroup
`Gamma >= P_host` (for example a Higman embedding): restriction only gives
`Rad_hyp(P_host) <= Rad_hyp(Gamma) cap P_host`, and this inclusion can be strict. The hole
`infinite-character-actor-word-energy-interface` stays open as stated.

**Scope.** The statement is for the seed `m_h`. For another `a in A - C`, the same argument needs the stabilizer of a
`K`-orbit containing `<C,a>` to be all of `SL_3(Q_2)`. That would follow from maximality results for open subgroups,
which are not verified here.
