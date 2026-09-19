# Kun--Thom fixed edge-window escape audit

**Date:** 2026-08-26

## Goal

After the Walsh--Hadamard no-go, test a packet which includes the actual
strict compressor and full Kun--Thom actor rather than isolated matrix
correspondence data.

## Exact full-actor calibration

Let

```text
h=t^(-1)gamma t notin Gamma
```

be the fixed return.  Given finite windows `F subset Gamma` and
`S subset G\{1}`, residual finiteness supplies a finite quotient `pi:G->Q`
which separates every element of `S` from the identity and separates `h`
from every `f in F`.  In the left regular representation of `Q`, all actor
relations and the literal mixed word hold exactly, and

```text
<lambda(pi(h)),lambda(pi(f))>=0,       f in F.
```

But the exact finite-dimensional absorption theorem says

```text
lambda(pi(h)) in C*(lambda(pi(Gamma))).
```

Equivalently, some quotient-dependent `gamma_(F,S) in Gamma\F` satisfies
`pi(gamma_(F,S))=pi(h)`.  The return is globally absorbed but every fixed
candidate witness misses it.

Taking exhausting windows makes the full-actor characters canonical while
the absorption witness moves outward without bound.

## What this refutes

No finite packet of coefficients

```text
<phi(h),phi(f)>,       f in F subset Gamma,
```

can authenticate the complete edge algebra, even if:

- the actor is an exact finite-dimensional representation;
- the strict compressor and return equation are literal;
- the actor character is canonical on an arbitrarily large prescribed
  window;
- exact finite-dimensional algebraic absorption holds.

This is stronger than the Walsh calibration with respect to actor
compatibility.  The countermodel is an honest representation of the full
Kun--Thom actor.

## Remaining viable datum

The full conditional expectation `E_(C*(phi(Gamma)))`, a commutant
projection, or a canonical positive-density lamp correlation is not a fixed
word-span test.  Those data can see the quotient-dependent witness and are
not refuted here.  The next positive step must preserve one of them under
actor correction; expanding the finite edge-word list cannot close the gap.

## Cairn duplication check

Nearby nodes prove global exact absorption and moving Gram degeneration.
Neither combines them into this exact full-actor escape: orthogonality to an
arbitrary prescribed edge window together with membership in the complete
edge algebra at the same coordinate.
