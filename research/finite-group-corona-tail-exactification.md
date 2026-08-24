---
rg: 2
id: finite-group-corona-tail-exactification
kind: claim
title: Finite-group corona representations exactify on a cofinite tail
distinct_from:
  finite-group-opnorm-support-profile: That claim is the same-dimension operator-norm stability input for one approximate finite-group table; this is its corona-level consequence, including recovery of the original corona class on one cofinite coordinate tail.
  gowers-hatami-finite-group-hs-stability: That theorem allows flexible enlargement and controls normalized Hilbert--Schmidt error; this claim keeps every late matrix dimension fixed and corrects in operator norm.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
---

Let `F` be finite and let `rho:F -> U(prod M_(d_n)/oplus M_(d_n))` be a
homomorphism.  After deleting finitely many coordinates there are genuine
unitary representations `rho_n:F -> U(d_n)` whose classes recover `rho`.
Equivalently, the induced star-homomorphism from the finite-dimensional
algebra `C*(F)` lifts to the tail product.  This is the finite-dimensional
semiprojectivity/matrix-unit correction lemma used in the finite-packet
self-copy collapse.

This corona-level corollary is established at paper level through the
existing operator-norm finite-group stability node; it has no dedicated Lean
declaration yet.
