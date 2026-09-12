---
rg: 2
id: two-site-rigidity-of-lamp-witnesses
kind: claim
title: A lamp-to-lamp weak-soficity witness separating the mark must be exactly covariant
distinct_from:
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks whether a Hilbert embeddable witness exists; this proves necessary conditions on the shape of any witness, embeddable or not, and so constrains that search rather than answering it.
  invariant-graph-clifford-phase: that classifies invariant graphs on the infinite coset space; this shows a related structure is forced on the finite site sets of any witness.
  marked-double-coset-infinite-degree: that computes an index in the infinite Kun--Thom pair; this is about the finite approximating groups.
artifacts:
  - notes/FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md
---

Let `W = (directSum_(G/Gamma) Z/2Z) semidirect G`, let `w=a_o a_(h Gamma)` be
the marked involution, and consider a weak-soficity witness `sigma:W->K_n`
with bi-invariant length `ell_n`, defect tending to zero and
`ell_n(sigma(w)) >= c > 0`.  Call the witness **lamp-to-lamp** if `K_n` has a
normal subgroup `directSum_(Y_n) Z/2Z` with `sigma(a_u)=a_(j_n(u))` and the
`sigma(g)` normalizing it by permuting sites.

1. **Two-site rigidity.**  If the conjugation image of `K_n` on the site set
   `Y_n` is 2-transitive, then all elements `a_p a_q` with `p != q` are
   conjugate, so a bi-invariant length gives them **one common value**.  The
   mark and every covariance error are among them, so they cannot be
   separated from each other.
2. **Forced exact covariance.**  Consequently, under the hypotheses of 1, the
   witness must satisfy

   ```text
   pi_n(g) j_n(u) = j_n(g u)
   ```

   exactly for every `g,u` in the window — no covariance error is affordable
   at all.  The entire multiplicative defect must be carried off the lamp
   coordinates, by the acting part alone.
3. **Corrected no-dilution bound.**  `sqrt(ell_n)` is a conjugation-invariant
   pseudometric, because conditional negative definiteness writes
   `ell_n(a^(-1)b)=||f(a)-f(b)||^2`.  Since `w = a_o * g a_o g^(-1)`, the
   triangle inequality for `sqrt(ell_n)` gives `ell_n(a_o) >= c/4`: every
   single lamp is expensive.

So a witness of this shape must break 2-transitivity — the site sets must
carry a nontrivial invariant relation distinguishing the marked pair from the
error pairs.  That is the finite shadow of `invariant-graph-clifford-phase`:
the invariant graph structure classified there on `G/Gamma` is not optional
decoration, it is forced on the finite approximations too.
