---
rg: 2
id: free-shift-shell-relations-are-finitely-certified
kind: claim
title: At a free near-shift action every true shell relation has a finite enumeration certificate
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Let P be infinite and finitely generated, and suppose its enumeration
nu gives R_nu=P*<s> under the canonical map. Use a fixed finite
generating set of V together with the shell copies of generators of P.

For every word w that is identity in E_nu, there is a finite
restriction sigma of nu such that w is identity in E_mu for EVERY
bijection mu extending sigma, with the same generator marking.
The other enumeration need not have a free near-shift action.

If the word problem of P and nu with its inverse are computable,
the word problem of E_nu is decidable. In the identity case the
algorithm outputs such a finite certificate. The certificate uses
finite enumeration values, finite prefix tables, and finitely many
true equalities in P; it is not a finite presentation of E_nu.
