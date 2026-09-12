---
rg: 2
id: bernoulli-rokhlin-deficit-has-a-finitary-witness
kind: claim
title: A Rokhlin entropy deficit of Bernoulli shifts is witnessed by one finite configuration of translates
distinct_from:
  bernoulli-rokhlin-maximality-passes-to-subgroups: that transfers maximality along subgroup inclusions and finite index; this computes the per-copy Rokhlin entropy as an infimum over finite configurations and gets closure under directed colimits.
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Let `G` be a countable group and `|A| = q >= 2`. Take `k >= 1`, finite sets `E`
and `F` in `G`, and a function `psi` from `(A^k)^E` to a finite set. With `x` iid
uniform on `A^k` over `G`, put

    Phi(k,E,F,psi) = (1/k) [ H(psi(x|_E)) + H( x(1) | (psi((x(fe))_(e in E)))_(f in F) ) ].

Then

    rho_q(G) = lim_k h^Rok_G((A^k)^G)/k = inf over configurations of Phi.

`Phi` depends only on the incidence pattern of the products `f e`, including which
of them equal `1`.

Consequences:

* `G` is Rokhlin-maximal at `q` exactly when
  `H(psi) + H(x(1) | F-translates of psi) >= k log q` for every configuration.
* Rokhlin-maximality is closed under directed colimits with arbitrary structure
  maps, because a witness uses finitely many coincidences.
* The route `rokhlin-maximality-on-tester-covers-every-group` combines this with
  subgroup closure and the fixed tester theorem.

**ESTABLISHED 2026-09-12** by
[[bernoulli-rokhlin-deficit-has-a-finitary-witness-proof]].
