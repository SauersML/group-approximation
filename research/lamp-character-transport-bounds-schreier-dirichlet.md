---
rg: 2
id: lamp-character-transport-bounds-schreier-dirichlet
kind: claim
title: Character transport leakage is the PVM covariance defect and bounds the amplitude Dirichlet form
artifacts:
  - research/artifacts/atomic-schreier-lamp-collapse-audit-2026-08-26.md
distinct_from:
  infinite-schreier-pvm-transport-kills-finite-mark: that is the mass collapse itself, drawn from a bottom spectral gap of the orbit graph and stated in the covariance-defect vocabulary; this is the dictionary between that vocabulary and character-transport leakage, plus the amplitude form of the same energy, and it collapses nothing on its own.
  stabilizer-orbit-commutators-have-a-kesten-chart-carrier: that produces a free carrier whose Kesten spectral measure is atomless so a chart can be cut at a quantile; this is an identity and an inequality inside one trace and uses no free subgroup.
  single-lamps-recover-set-action: that transfers soficity of a lamp-group action back to the underlying set action; this is a quantitative estimate inside one finite-dimensional trace and transfers nothing.
---

Let `M` be an elementary abelian `2`-group with dual `M^`, let a group `A` act
on `M` by automorphisms with dual action `(s.chi)(m) = chi(s^(-1).m)`, and let
`(N,tau)` be tracial.  Let

```text
rho : M -> U(N),   rho(m) = sum over chi of chi(m) P_chi
```

be an **exact** representation with joint spectral resolution `(P_chi)`, put
`q_chi = tau(P_chi)`, and let `U_s in U(N)` be any unitary attached to `s in A`.
Define the character-transport leakage and its overlap

```text
a_s(chi) = tau(P_(s chi) U_s P_chi U_s^*),
L_s      = sum over chi of tau((1 - P_(s chi)) U_s P_chi U_s^*).   (CTL1)
```

**Dictionary.**  `L_s` is exactly half the PVM covariance defect of `(ISP2)`:

```text
sum over chi of || U_s P_chi U_s^* - P_(s chi) ||_2^2 = 2 L_s.     (CTL3)
```

So a hypothesis stated as "actor leakage" and a hypothesis stated as
"covariance defect" are the same hypothesis, and
`infinite-schreier-pvm-transport-kills-finite-mark` consumes either.

**Amplitude form.**  Set `h(chi) = sqrt(q_chi)` and `(s.h)(chi) = h(s^(-1) chi)`.
Then

```text
|| h - s.h ||_2^2 <= 2 L_s   for every s in A.                     (CTL2)
```

The content of `(CTL2)` is that the **square roots of the spectral
multiplicities are a classical probability amplitude**: the operator-level
transport defect of the actor is an ordinary Dirichlet increment of that
amplitude on the character set, with no hypothesis on `U_s` beyond unitarity,
no finiteness of `dim N`, and no finite generation of `M` or `A`.  It is
weaker than `(CTL3)` -- Cauchy--Schwarz is used once -- and is the form in
which a classical Schreier-graph gap can be applied directly.
