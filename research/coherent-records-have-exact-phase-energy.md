---
rg: 2
id: coherent-records-have-exact-phase-energy
kind: claim
title: Coherently recording basis information has an exact hypercube phase-energy formula
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
distinct_from:
  shared-records-obey-complementary-check-uncertainty: That bounds two data-record correlation checks; this computes an unchanged data-only phase check after a specified isometry.
---

For normalized auxiliary vectors phi_x and n>=1 let
Psi=2^(-n/2)sum_x |x>|phi_x> and H_X=(1/n)sum_i (I-X_i)/2.
Then <Psi|H_X tensor I|Psi> =
sum_(x,i)||phi_x-phi_(x xor e_i)||^2/(4n 2^n).
For classical records |f(x)>, this is half the fraction of oriented
edges on which f changes. Parity, AND and constant records have
energies 1/2, 2^(-n) and zero respectively.

For a single data bit recorded as |0>|u>,|1>|v>, the encoded |+>
has data-only phase energy (1-Re<u,v>)/2. If s is the trace distance
between the pure records, this is at least (1-sqrt(1-s^2))/2;
energy <=eta<=1/2 forces s<=2sqrt(eta(1-eta)).

These statements fix the data-only phase observable. They do not
exclude encoded replacement checks, nor impose a constant penalty
on every nonconstant record.

