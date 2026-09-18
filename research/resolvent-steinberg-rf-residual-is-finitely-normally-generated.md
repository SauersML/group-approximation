---
rg: 2
id: resolvent-steinberg-rf-residual-is-finitely-normally-generated
kind: claim
title: For some l and N >= 5, the finite residual of St_N(R_l) is the normal closure of finitely many elements
distinct_from:
  resolvent-steinberg-group-is-residually-finite: that asks for a trivial finite residual; this allows any finitely normally generated one, which already gives a finitely presented residually finite quotient.
  resolvent-elementary-group-is-fp: that asks for the whole kernel K_2(N,R_l) of St_N(R_l) -> E_N(R_l) to be finitely normally generated; the finite residual is contained in that kernel, and neither statement is known to imply the other.
---

**OPEN.** There are a prime `l` and `N >= 5` such that the finite residual
`K_rf = ∩ {finite-index normal subgroups}` of `St_N(R_l)` is the normal closure of a finite
set.

**Use.** Then `Λ = St_N(R_l)/K_rf` is finitely presented and residually finite, and it
contains `Z_(l)`. So it witnesses `z-localized-embeds-in-fp-rf-group`, by route
`z-localized-fp-rf-via-resolvent-steinberg-rf-quotient`. Finite presentation of
`St_N(R_l)` for `N >= 5` uses `steinberg-groups-of-fp-rings-are-fp-in-rank-five`, with no
literature input.

**Where it stands (2026-09-18, lane gq-infinite-primes).**
- *The ring side is done.* `R_l` is residually finite
  (`resolvent-presentation-ring-is-residually-finite`), so `E_N(R_l)` is residually finite
  and `K_rf ⊆ K_2(N, R_l) = ker(St_N(R_l) -> E_N(R_l))`.
- *Detection.* By `steinberg-rf-forces-ring-rf`, an element of `K_2(N, R_l)` survives
  exactly when it is nontrivial in `St_N(F)` for some finite quotient ring `F`.
- *The crux.* Is the part of `K_2(N, R_l)` that is invisible in every finite `St_N(F)`
  finitely normally generated?

## Attempts

1. **Two families of candidate invisible elements (heuristic; the K-theory imports
   below were not checked at source).**
   - *Symbols from `Z`.* The class `{-1,-1}` comes from `K_2(Z) = Z/2`. It maps nontrivially
     to `K_2(Q(u)[x^(±1); σ])`: `R_l -> D ⊆ Q(u)[x^(±1); σ]`, and the twisted Laurent
     fundamental theorem gives a cokernel of `1 - σ` on `K_2(Q(u))` that contains
     `K_2(Q)`. So `{-1,-1}` is plausibly nontrivial in `St_N(R_l)`.
     - For `l` odd, finite quotients `F` of characteristic `p^r` with `p` odd factor it
       through `K_2(Z/p^r) = 0`.
     - The 2-primary parts of finite quotients have every faithful free
       `Z/2^r`-module of rank divisible by `2^r`: taking traces in `x u x^(-1) = u + l`
       gives `rank · l ≡ 0`. So `{-1,-1}` may be invisible.
     - Even so, it is a single element, so it does not obstruct this claim.
   - *Corner tame symbols.* `K_2(Z_(l))` contains `⊕_(q != l) F_q^×` (tame symbols at
     every prime `q != l`), which is infinitely generated. Through the corner
     `θ : Z_(l) -> e R_l e` these give Steinberg-symbol elements of `St_N(R_l)` in the
     block of `e`.
     - In a finite quotient `F` where `e` survives, `e F e` has `l`-power characteristic,
       because `q` is invertible there for every prime `q != l`.
     - There the tame symbols at `q` plausibly die, as they do in `K_2(Z/l^r)`.
     - *The danger.* Suppose infinitely many of them are nontrivial and independent in
       `St_N(R_l)`, and `K_2(N, R_l)` is central in `St_N(R_l)`. Then `K_rf` is central, so
       its normal closures are just the subgroups it generates. It contains an infinitely
       generated subgroup, so this claim fails for `R_l`, and
       `resolvent-elementary-group-is-fp` fails too. (Centrality of `K_2(N, R)` for
       noncommutative `R` is itself not known here.)
     - *The test that decides it.* Compute `K_2(R_l)` through the split extension
       `0 -> (e) -> R_l -> D -> 0`, with `K_2(D)` from the twisted Laurent theorem
       (plausibly finite). The question is whether `K_2` of the path ideal
       `V ⊗ T ⊗ W` of `resolvent-ring-has-path-normal-form` sees `K_2(Z_(l))`.
2. **If the corner symbols survive: change the ring.** Add finitely many relators to `R_l` that make the
   corner symbols trivial, then re-check residual finiteness with the path normal form. Or replace the corner
   ring `Z_(l)` by a ring with finitely generated `K_2` that still has roots at every prime but one. Not
   attempted.
