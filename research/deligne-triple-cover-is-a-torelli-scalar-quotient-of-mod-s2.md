---
rg: 2
id: deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2
kind: claim
title: Deligne's triple cover of Sp4(Z) is the quotient of Mod(S_2) x Z/3 that makes the Torelli group act by an invariant cube-root character
distinct_from:
  deligne-central-mark-hs-collapse: that is the one-word normalized-HS collapse for a presentation of E_3 itself; this relocates the same mark to the Torelli group of the genus-two mapping class group through a split pullback, where the mark becomes a scalar condition on Torelli words.
  deligne-triple-cover-finite-residual-is-center: that computes the finite residual of E_3; this uses it to show that the Torelli character is nonzero on every finite-index part of the Torelli group.
  deligne-triple-cover-fd-central-invisibility: that kills the mark in every finite-dimensional representation of E_3; this transfers the statement to finite-dimensional representations of Mod(S_2) that are scalar on Torelli.
---

**ESTABLISHED** through `deligne-triple-cover-torelli-scalar-quotient-proof`. Unreviewed; no novelty
claimed.

**Setting.**
- `M = Mod(S_2)`, the mapping class group of the closed oriented genus-two surface.
- `pi : M -> Gamma = Sp_4(Z)` is the action on `H_1(S_2; Z)`, which is surjective.
- `K = ker(pi)` is the Torelli group.
- `1 -> <z> = Z/3 -> E_3 -> Gamma -> 1` is Deligne's triple cover, `z` its covering generator.
- `omega = exp(2 pi i/3)`.

**Statement.**

1. **(TS1) Splitting.** The pulled-back central extension `M x_Gamma E_3` of `M` by `Z/3` splits. So
   there is a homomorphism `c : K -> Z/3`, constant on `M`-conjugacy classes, together with an
   isomorphism
   ```text
   E_3  ~=  (M x Z/3) / L_c,     L_c = { (k, -c(k)) : k in K },     z = class of (1, 1).
   ```
2. **(TS2) The character is nowhere profinite.** For every finite-index normal subgroup `N` of `M`,
   `c(K cap N) = Z/3`. In particular `c != 0`.
3. **(TS3) Presentation.** If `k_1, ..., k_m` normally generate `K` in `M` (finite lists exist), then
   ```text
   E_3  ~=  < M, z | z^3,  [z, M],  k_i z^(-c(k_i))  (1 <= i <= m) >.
   ```
4. **(TS4) Invisibility on Mod(S_2).** No finite-dimensional unitary representation `rho` of `M`
   satisfies `rho(k) = omega^(c(k)) I` for all `k in K`, or equivalently for all the `k_i`. The same
   holds with `omega^2` in place of `omega`.
5. **(TS5) Hyperlinearity dictionary.** Fix a finite presentation `<S | R>` of `M` and words for
   `k_1, ..., k_m`. Then `E_3` is hyperlinear iff there are a primitive cube root `zeta` and unitary
   tuples `rho_n : S -> U(d_n)` with
   ```text
   max_(r in R) ||rho_n(r) - I||_(2,d_n) -> 0   and   max_i ||rho_n(k_i) - zeta^(c(k_i)) I||_(2,d_n) -> 0.
   ```
   The condition does not depend on the chosen finite presentation or normal generators.

**Reading.** By `deligne-sector-gap-is-exactly-nonhyperlinearity`, (TS5) turns the terminal Deligne
problem, the genus-two instance of `deligne-stable-triple-cover-is-not-hyperlinear`, into a question
about almost representations of the mapping class group `Mod(S_2)`:
- the relators of `M` must be almost satisfied;
- the Torelli normal generators must be almost scalar, with the prescribed invariant cube-root phases.

By (TS4), exact finite-dimensional representations can never do this. By (TS2), the phase character `c`
can't be seen through any finite quotient of `M`. So a vanishing-defect countermodel has to put the
Torelli group almost at scalars while staying profinitely far from every finite quotient. A
non-hyperlinearity proof must show that the defect of the Torelli-scalar condition stays bounded below
on almost representations of `Mod(S_2)`.

**What is not claimed.**
- No identification of `c` with a named invariant (e.g. a reduction of Meyer's function) is made.
- No single separating Dehn twist is asserted to normally generate `K`. That standard fact is not pinned
  here, so the statement uses an arbitrary finite normal generating list.
