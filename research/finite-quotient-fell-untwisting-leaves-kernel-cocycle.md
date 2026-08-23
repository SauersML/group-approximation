---
rg: 2
id: finite-quotient-fell-untwisting-leaves-kernel-cocycle
kind: claim
title: Finite-quotient Fell untwisting leaves the whole kernel representation as a cocycle
distinct_from:
  simple-lamp-gauge-rigidity-reduces-to-actor-classicalization: that identifies an arbitrary actor approximation in the lamp multiplicity fiber and notes absorption by a genuinely regular actor packet; this computes why a residually finite actor's finite quotient packets do not supply that absorption.
  diagonal-tensor-powers-do-not-amplify-regular-lamp-center: that concerns tensor powers of one finite lamp representation; this concerns tensoring an arbitrary actor representation with a finite quotient regular representation.
---

**ESTABLISHED.** Let `q:G -> Q` be a finite quotient, choose a section
`s:Q -> G`, and let `pi:G -> U(H)` be a unitary representation.  On
`ell^2(Q) tensor H` put

```text
R_g = lambda_Q(q(g)) tensor pi(g).                        (FQF1)
```

The finite-quotient analogue of the Fell basis change does not erase `pi`.
Define

```text
T(delta_a tensor xi)=delta_a tensor pi(s(a)^(-1))xi.
```

A direct calculation gives

```text
T R_g T^*(delta_a tensor xi)
 = delta_(q(g)a) tensor pi(c(g,a))xi,                     (FQF2)

c(g,a)=s(q(g)a)^(-1) g s(a) in ker(q).                   (FQF3)
```

The maps `c(g,a)` form the usual section cocycle.  Hence the actor becomes a
permutation of the quotient coordinate only at the price of a blockwise
unitary cocycle carrying the restriction `pi|ker(q)`.  It is pure
permutation precisely when that cocycle is killed (for example, when `pi`
factors through `Q`).

The same identity is stable for a fixed finite test window in normalized
Hilbert--Schmidt norm: replacing `pi` by a sufficiently accurate approximate
representation changes `(FQF2)` only by the finitely many multiplication
defects used in the displayed words.  It does not make the kernel cocycle
amenable or permutation-valued.

## Application to simple-lamp recovery

The Kun--Thom actor `G` is residually finite, so a tempting strategy is to
tensor a hypothetical microstate of

```text
K^(G/Gamma) semidirect G
```

with a regular action on a finite quotient of `G`.  One then hopes to use
regular absorption to make the actor permutation-valued and apply
amenable-base classicalization to the lamps.  Equations `(FQF2)--(FQF3)`
show the exact failure: the residual blocks are a representation of a
finite-index, generally nonamenable kernel of `G`, not of the amenable lamp
base.  The Burton--Chaudkhari--Juschenko--Muliarchyk theorem therefore has no
input with which to classicalize them.

Using a genuine regular `G`-packet would kill the cocycle by Fell absorption,
but finite sofic models provide only local Cayley balls.  Choosing coherent
group labels on almost every point would amount to a Følner tiling of the
nonamenable actor; the boundary is exactly the actor-classicalization gate.

Thus residual finiteness of the actor does not close
`simple-lamp-hyperlinear-recovery-forces-action-sofic`.  It moves the
arbitrary multiplicity gauge into the finite-index kernel cocycle without
reducing its complexity.
