---
rg: 2
id: unrestricted-zero-compression-feedback-is-surjunctive
kind: claim
title: Zero compression forces injective scalar order-three feedback to preserve parity blocks and be surjective
artifacts:
  - research/artifacts/gottschalk-unrestricted-order-three-odd-parity-obstructions-2026-09-08.md
---

Let t have order three in any group G, put E=I+R_t+R_t^2, and
let A be an arbitrary scalar linear cellular automaton. If

    F(x)=x+A(xR_t x)

is injective and EAE=0, then AE=0 and F is surjective. This
requires no direct-finiteness assumption and permits nonzero
feedback A(I-E) from the even-parity subspace.

More generally, write K=(I-E)AE and W=im E. Two inputs of odd
parity on every t-block collide exactly when some nonzero q in W
satisfies EAq=0 and (Kq)_i is nonzero on every active block of q.
This criterion implies that on A_4, with t a three-cycle, every
injective scalar rule of the displayed form has K=0, even when
EAE is nonzero. Finiteness already makes injectivity imply
surjectivity on A_4; the additional result is the restriction K=0.

The unrestricted scalar family on general groups remains
unresolved. These statements do not prove Gottschalk's conjecture.
