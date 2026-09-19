---
rg: 2
id: kazhdan-relations-have-no-poly-haagerup-host
kind: claim
title: A pmp relation whose factor has property (T) has no free host, finite or infinite, whose actor has a normal series with Haagerup quotients
distinct_from:
  nonce-relation-hosts-force-root-or-q1-failure: item 5 there excludes amenable-by-(f.g. virtually free) and free actors for every non-CE relation, and infinite hosts only for amenable or free actors; this excludes every actor with a normal series with Haagerup quotients (Haagerup, Z^2 ⋊ SL_2(Z), Haagerup-by-Haagerup, poly-free, ...), finite and infinite hosts alike, but only for relations whose factor has property (T).
  haagerup-actors-cannot-host-property-t-algebraic-envelope: that forbids a (T) factor inside A ⋊ Lambda for finite A and one Haagerup actor, through Popa's relative property H; this is a relation-level statement that iterates along a normal series (reaching non-Haagerup actors such as Z^2 ⋊ SL_2(Z)) and covers sigma-finite infinite hosts, where no finite crossed product exists.
  haagerup-hosts-blind-full-group-kazhdan-certificate: that concerns Kazhdan groups acting through the full group of a Haagerup free action; this concerns a Kazhdan relation placed class-bijectively in any free action, with no group generating it.
  non-ce-relation-is-not-treeable: a treeing is a host with a free actor; this excludes all hosts with poly-Haagerup actors for the (T) relation.
artifacts:
  - research/kazhdan-relations-have-no-poly-haagerup-host-proof.md
---

**Definitions.**
* A countable group `Lambda` is *normally poly-Haagerup* if it has a chain
  `1 = N_0 ≤ N_1 ≤ ... ≤ N_k = Lambda` of subgroups, each normal in `Lambda`, with every `N_i / N_(i-1)` Haagerup.
  The class is closed under subgroups. It contains every Haagerup group, every extension of a Haagerup group by a
  Haagerup group (so `Z^n ⋊ SL_2(Z)`, amenable-by-virtually-free groups, free-by-cyclic groups). It also contains
  every group with a normal series with free quotients: for the pure braid groups `P_n`, take the kernels of the
  Fadell–Neuwirth maps `P_n -> P_(n-i)`. It contains no infinite group
  with property (T).
* *Free host* is as in `nonce-relation-hosts-force-root-or-q1-failure`. The measure `zeta` may be infinite, and only
  `0 < zeta(A) < infinity` is required.
* For a pmp relation `S` on `(A, zeta_A)` and a Borel cocycle `c : S -> Lambda`, the *skew relation* on
  `A × Lambda` is `(a, lambda) ~ (a', c(a', a) lambda)`. It preserves `zeta_A × counting`. Call `c` *dissipative* if
  the skew relation is smooth, meaning it has a Borel transversal on a conull invariant set.

**Theorem.** Let `R` be an ergodic pmp countable Borel equivalence relation on a standard probability space
`(X, mu)`. Assume `L(R)` is a II_1 factor with property (T) in the sense of Connes–Jones. Let `Lambda` be
normally poly-Haagerup.
1. **(Cocycle form.)** Let `S` be a pmp class-bijective extension of `R`. That is, `S` is on `(A, zeta_A)`, and
   `r : A -> X` pushes `zeta_A` to `mu` and maps a.e. `S`-class bijectively onto an `R`-class. Then `S` has no
   dissipative Borel cocycle into `Lambda`.
2. **(Haagerup step.)** Let `Q` be a Haagerup group and `b : S -> Q` any Borel cocycle. Then there are:
   * an `S`-invariant Borel set `A_0` of positive measure;
   * a finite subgroup `K ≤ Q`;
   * a Borel `h : A_0 -> Q` with `h(a')^(-1) b(a', a) h(a) ∈ K` for `(a', a) ∈ S|A_0`.
3. **(Hosts.)** `R` has no free host with actor `Lambda`, whether `zeta` is finite or infinite. Consequently `R` has
   no splitting cocycle into any pmp action of `Lambda` (these are finite hosts, by item 2 of the hosting claim).
4. **(The fixed (T) relation.)** Item 3 applies to the property-(T) non-CE relation `R_T` of
   `non-ce-property-t-equivalence-relation-exists`. So for the `R_T` branch of `nonce-relation-admits-free-host`,
   every host's actor must fail to be normally poly-Haagerup. By closure under subgroups, it must fail on every
   subgroup that carries the host.

**Class-kill.**
* *Named invariant:* the finite-set-valued equivariant section `Phi(a) = argmax_g |<F(a), pi(g) v>|`. It is built
  from the `[R]`-fixed vector `F` of the `C_0`-representation `pi`, which is induced along the host cocycle.
* *Death step:* property (T) of `L(R)` makes the Schur multipliers of the induced positive-definite functions
  uniformly close to the identity. This yields `F`, and hence `Phi`. `Phi` cohomologizes the cocycle into
  (finite)-by-`N_(k-1)`. Repeating down the series lands the cocycle in a finite group. A dissipative cocycle into a
  finite group forces finite classes.
* *Consequence:* every host strategy for `R_T` that uses an actor built from Haagerup pieces by normal extensions is
  dead. This includes all hosts with infinite `zeta`, where item 5 of the hosting claim covered only amenable and free
  actors.

**What is not claimed.**
* Nothing is claimed about the Manzoor relation `R_mu`, which is not known to have (T).
* Nothing is claimed about actors with an infinite Kazhdan subgroup, or about other non-poly-Haagerup actors.
* Nothing is claimed about generation of `R_T` by non-free actions with finite stabilizers (item 3 of the hosting
  claim). Those give corners, not class-bijective hosts.
