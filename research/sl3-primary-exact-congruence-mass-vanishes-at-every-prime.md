---
rg: 2
id: sl3-primary-exact-congruence-mass-vanishes-at-every-prime
kind: claim
title: At every prime a small arithmetic overlap defect forces the exact denominator-primary congruence mass to vanish
distinct_from:
  p-divisible-lambda-exact-mass-vanishes-at-large-primes: That gives an explicit depth-free Clifford bound at primes at least eleven; this covers every prime including two through positive orbit measures and works in arbitrary finite tracial coordinate algebras, without an explicit numerical modulus.
  lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible: That leaves arbitrary ultra-deep primary towers; this excludes them for genuine finite congruence lattice representations at every prime.
artifacts:
  - research/artifacts/sl3-primary-exact-sector-kirillov-tightness-2026-09-08.md
  - research/artifacts/independent-kirillov-primary-sector-audit-2026-09-08.md
---

Fix any prime p, C=SL_3(Z), K=SL_3(Z_p),
h=diag(p,1,p^-1), and D=C intersect h^-1 C h.
Let (M_n,tau_n) be finite tracial von Neumann algebras,
sigma_n:C -> U(M_n) genuine homomorphisms factoring through
SL_3(Z/(p^(a_n)m_n)), with (p,m_n)=1, and H_n unitary.
Assume on a fixed finite Kazhdan set S_D that

    max_(d in S_D)
      ||H_n sigma_n(d)-sigma_n(h d h^-1)H_n||_2 -> 0.

Let rho_n:K -> U(M_n) be the CRT primary factor, and let P_n
be the finite group average of rho_n, the projection onto its
trivial part. Then

    1-tau_n(P_n) -> 0,
    sup_(k in K)||rho_n(k)-1||_2 -> 0.

In particular the coprime CRT factor beta_n gives a genuine
representation of C with

    sup_(c in C)||sigma_n(c)-beta_n(c)||_2 -> 0.

The conclusions hold along free ultrafilters as well. Conductors,
multiplicities, coprime factors, trace weights and dimensions are
unrestricted. No regular limiting character is assumed. Only the
fixed overlap relation is needed for this primary reduction.

The proof uses the exact positive orbit formula on fixed principal
uniform pro-p groups. At p=2 the positive formula is applied only
on their square subgroups, as required by Boyarchenko--Sabitova
Theorem 2.8. Almost intertwining gives common positive Fourier
mass. Escaping frequency mass would create an invariant probability
on projective coadjoint space, which cannot exist. Tightness and
root contraction force the primary factor to be trivial.

The hypothesis of genuine finite congruence representations is
essential to the proof. The theorem supplies no correction of
arbitrary approximate representations.

