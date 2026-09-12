---
rg: 2
id: extensive-index-defect-from-spectral-syndrome-transducer
kind: route
title: Spectral density plus bounded-overlap local payment gives extensive index energy
target: extensive-cosystolic-index-defect
requires:
  - marked-hs-separation-forces-spectral-density
  - bounded-overlap-syndrome-energy-accounting
  - spectral-carrier-to-local-syndrome-transducer
---

Use the presentation, marked nontrivial word and constants from
`spectral-carrier-to-local-syndrome-transducer`.  Put

```text
beta = alpha^2(1-theta^2)/(4-theta^2 alpha^2) > 0.
```

For every marked tuple, `marked-hs-separation-forces-spectral-density` gives

```text
tau_d(Q) >= beta.
```

The transducer therefore produces carriers with

```text
sum_j rank(P_j)/d >= gamma beta.
```

Since every nonzero carrier has rank at most `B`, their number is at least

```text
#J >= (gamma beta/B) d.
```

Thus the extensive-syndrome constant may be taken as
`c=gamma beta/B`.

For the opposite inequality, every nonzero carrier has rank at least one, so

```text
#J/d <= sum_j rank(P_j)/d.
```

Apply `bounded-overlap-syndrome-energy-accounting` to the local-payment
inequalities with

```text
q_j=rank(P_j)/d,
e_r=||r(U)-1||_2^2.
```

This yields

```text
#J/d
 <= sum_j q_j
 <= L D sum_(r in R) ||r(U)-1||_2^2.
```

Hence `(EID)` holds with `C=LD`.  The positive carrier density and the energy
payment required by `extensive-cosystolic-index-defect` are therefore reduced
to the single local transducer claim; no additional expansion or asymptotic
counting step remains.
