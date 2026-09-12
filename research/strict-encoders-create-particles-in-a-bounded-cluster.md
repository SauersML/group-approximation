---
rg: 2
id: strict-encoders-create-particles-in-a-bounded-cluster
kind: claim
title: A strict binary encoder must create particles in an explicitly bounded connected cluster
distinct_from:
  finite-injective-charge-noncreation-forces-surjectivity: that assumes noncreation on every finite configuration; this gives a finite family of necessary creation witnesses for a supplied binary encoder-decoder pair.
  local-decoders-bound-connected-missing-particle-witnesses: that bounds a missing output; this bounds an input on which particle count increases, using the charge induction truncated at the decoder bound.
artifacts:
  - research/artifacts/bounded-particle-creation-synthesis-audit-2026-09-08.md
---

Let G be any group and let tau,sigma:{0,1}^G->{0,1}^G be cellular
automata with tau(0)=0 and sigma tau=id. Choose finite memories M,S
containing 1_G, using the convention that output at g reads gM or gS.
Put K=|MS| and E=M^(-1)M.

If tau is not surjective, there is a finite configuration x such that

    1 <= |supp(x)| <= K,
    |supp(tau(x))| > |supp(x)|,

and supp(x) is E-connected. After translating x, its support contains
1_G and is contained in E^(K-1).

Consequently a supplied encoder-decoder pair is surjective if particle
count does not increase on the finite family of nonempty E-connected
subsets T of E^(K-1) containing 1_G with |T|<=K. It is unnecessary to
assume or verify noncreation on larger finite configurations.

This is an exact finite synthesis obstruction, conditional on the
literal identity sigma tau=id. It does not give a counterexample,
prove unrestricted surjunctivity, or assert that group equality is
algorithmically decidable. A reversible rule may satisfy the creation
condition, so finding such a cluster does not establish a defect.
