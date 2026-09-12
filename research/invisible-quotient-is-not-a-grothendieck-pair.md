---
rg: 2
id: invisible-quotient-is-not-a-grothendieck-pair
kind: claim
title: The invisible quotient is a quotient analogue and its profinite half is automatic
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
distinct_from:
  grothendieck-profinite-representation-equivalence: that imports the classical theorem and the existence of Grothendieck pairs; this compares them with the compression-wreath quotient and isolates which half of the comparison carries content.
  compression-wreath-five-radicals-coincide: that computes the five coinciding radicals; this is a positioning statement about how much of that computation the profinite formulation already exhausts.
---

The split epimorphism `q: W_K -> P_K` is **not** a Grothendieck pair, and the
difference cuts in the direction that matters for how the result is stated.

1. *Direction and hypotheses.*  A Grothendieck pair is a proper **inclusion**
   `P < Gamma` of finitely presented **residually finite** groups inducing an
   isomorphism of profinite completions.  Here the map is a **surjection** with
   nontrivial kernel, and the source is not residually finite -- its finite
   residual is exactly `R_K`.  So both groups of a classical pair embed in
   their own completions and the paradox is that the completion cannot separate
   them; here the completion genuinely forgets a piece of `W_K`.

2. *The profinite half carries no content beyond the radical computation.*
   Once `R_K = Res_fin(W_K)` is known, `W_K^ = P_K^` and
   `Hom(P_K, F) = Hom(W_K, F)` for finite `F` are immediate: finite quotients
   of `W_K` are by definition those factoring through `W_K/Res_fin`.  Nothing
   about compression, property (T), or coronas is used.  A statement of the
   form "invisible to every finite quotient" is therefore the free end of the
   theorem, and a reader who meets it first will underrate what follows.

3. *Where the content is.*  The inclusions

   ```text
   Rad_MF  subset  Rad_fd = Rad_Bohr  subset  Res_fin
   ```

   hold for every group: finite groups sit inside `U(d)` and inside the MF
   class, and Peter--Weyl collapses compact targets onto finite-dimensional
   unitary ones.  The theorem is that for `W_K` this chain **collapses**, the
   smallest radical equalling the largest.  That is the surprise, and it is
   entirely carried by the matricial end -- the statement that the operator-norm
   corona sees no more than a finite quotient does.

So the honest headline is the collapse of the chain, with the Grothendieck
material as historical orientation for what "invisible" means rather than as
the closest comparison.
