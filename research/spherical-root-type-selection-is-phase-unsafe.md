---
rg: 2
id: spherical-root-type-selection-is-phase-unsafe
kind: claim
title: A transitive spherical root selects the desired answer type but its moving character kills the toric phase
distinct_from:
  finite-group-selector-induction-barrier: that records all selector characters visible somewhere in finite representations; this proves the sharper normal-closure obstruction for a state-selected spherical character
  finite-morita-toricization-cannot-encode-nonaffine-support: that rules out a representation-functorial central/Morita compiler; this allows a noncentral selected type and shows why its root clauses are phase-unsafe
  toric-gap-is-a-relative-fd-central-word-face: that gives the general normal toric quotient; this gives the exact graph-character criterion and applies it to the strongest finite transitive answer packet
---

ESTABLISHED.  A finite transitive spherical packet can isolate one prescribed
answer representation on a cyclic vector.  The direct attempt to impose that
root by toric scalar-word clauses is nevertheless incompatible with phase-safe
normal closure whenever the inducing character moves under the packet group.

## Exact graph-character normal-closure criterion

Let `B` be an abelian group, central in `B x H`.  Let `K <= H` and let
`chi:K -> B` be a homomorphism.  Put

```text
C_chi={(chi(k)^(-1),k):k in K},
N=normalClosure_(B x H)(C_chi),
L=normalClosure_H(K).
```

> **Theorem 1.**  `N intersect B={1}` if and only if `chi` extends to a
> homomorphism `chi_tilde:L -> B` invariant under conjugation by `H`:
>
> ```text
> chi_tilde(h l h^(-1))=chi_tilde(l).                  (SRT1)
> ```

Projection `B x H -> H` maps `N` onto `L`.  If `N intersect B={1}`, this
projection is injective on `N`, so `N` is the graph of a unique map
`l |-> chi_tilde(l)^(-1)`.  The subgroup law makes `chi_tilde` a homomorphism,
the generators make it extend `chi`, and normality gives `(SRT1)`.
Conversely, the inverse graph of an invariant extension is normal, contains
`C_chi`, and contains every conjugate of its generators.  It is therefore
exactly `N` and meets `B` trivially.

In particular, if `D normal H`, `D <= K`, and `chi|D` is not `H`-invariant,
then `N intersect B` is nontrivial.

## The strongest finite answer packet really does select one type

Let `R` be a nonempty finite answer set, fix `r_0 in R`, and put

```text
D=(C_2)^R,
H_R=D semidirect Sym(R),
K_R=D semidirect Stab(r_0).
```

Write `l_r` for the coordinate lamp in `D`, and define

```text
chi_R(d,sigma)=d(r_0) in {+1,-1}.                     (SRT2)
```

Then `Ind_(K_R)^(H_R)(chi_R)` is the tautological signed-permutation
representation `T_R` on `C^R`, and is irreducible.  Indeed `D` acts on the
coordinate lines by distinct coordinate characters and `Sym(R)` acts
transitively on those lines, proving irreducibility.  The line `C e_(r_0)`
transforms under `K_R` by `chi_R`; Frobenius reciprocity gives a nonzero map
from the induced module to `T_R`, and both have dimension `|R|`.

Thus a `chi_R`-spherical root vector generates exactly the desired answer
type.  The diagonal lamps realize every coordinate function on `R`, and a
free router can conjugate this answer PVM to a source context PVM.  Finite
spherical induction genuinely solves the local selected-type problem.

## The root clauses kill the phase

Take `B={+1,-1}` and impose the scalar-word root clauses

```text
(chi_R(k)^(-1),k),  k in K_R.                         (SRT3)
```

Choose `s != r_0`.  Since `D <= K_R`, these clauses contain

```text
(1,l_s)  and  (-1,l_(r_0)).                           (SRT4)
```

A permutation in `H_R` sends `s` to `r_0`.  The normal closure of `(1,l_s)`
therefore contains `(1,l_(r_0))`.  Multiplication with the second element of
`(SRT4)` gives

```text
(-1,1) in N.                                          (SRT5)
```

The phase dies exactly.  This is the firewall missed by a vector-state-only
completeness check: the packet has a perfect spherical vector in the intended
type, but the full quotient by the normal closure of its root clauses has
trivial phase.

The obstruction is not weakness of finite induction; it is that type
isolation uses a moving nonnormal character.  Avoiding `(SRT5)` requires the
inducing character to extend invariantly over the normal closure, removing
the transitive character-orbit mechanism which selected one coordinate.

## Attempts

The hyperoctahedral packet above is the canonical finite transitive packet for
an arbitrary answer support, and its induced module is exactly the desired
irreducible type.  It fails at `(SRT5)`, before Hilbert--Schmidt soundness is
relevant.  Matrix amplification and Hecke projections do not alter the graph-
character normal closure.  Conjugating the whole root by a private router
only conjugates the same contradiction.

