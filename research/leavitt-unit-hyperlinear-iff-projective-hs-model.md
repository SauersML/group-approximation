---
rg: 2
id: leavitt-unit-hyperlinear-iff-projective-hs-model
kind: claim
title: The binary Leavitt unit group is hyperlinear exactly when it has a nontrivial projective HS model
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that is the open yes/no question; this is an equivalent witness problem in which relators need only approach scalars, the phase correction being supplied by the vanishing of the first two homology groups.
  binary-leavitt-hyperlinear-iff-singular-near: that removes the normal sector of a state witness; this removes the phase constraint of a matrix witness, and the two relaxations are independent.
  projective-unitary-classes-vanish-on-schur-kernel: that kills projective multipliers on the Schur kernel of a nonsingular adjunction over an arbitrary countable group; this uses vanishing of the whole Schur multiplier of one simple group to lift every projective model.
---

**ESTABLISHED.** Put `H = L_(F_2)(1,2)^x`. For maps `phi_n : H -> U(d_n)` and
the normalized trace write

```text
pdef_n(g,h) = min_(lambda in T) ||phi_n(g) phi_n(h) - lambda phi_n(gh)||_2,
pdist_n(g)  = min_(lambda in T) ||phi_n(g) - lambda 1||_2.
```

The following are equivalent.

1. `H` is hyperlinear.
2. There are `phi_n` with `pdef_n(g,h) -> 0` for all `g,h in H` and
   `limsup_n pdist_n(g_0) > 0` for some `g_0 in H`.                (PHS)

So a witness for the unstable Steinberg branch may be built modulo scalars:
relators need only tend to scalar unitaries, and generators may be
implemented by projective representations of any phase cocycle. The phase
correction exists in the limit because `H_1(H;Z) = H_2(H;Z) = 0`
(perfectness, and Khanh's Theorem 4.4 at rank one), and it is unique because
`H` has no nontrivial characters.

## What the relaxation does and does not buy

- **Balanced relators carry no phase.** If a relator `w` has exponent sum
  zero in every generator, then `w(phi_n)` does not change when the
  generators are rescaled by scalars. Along the ultrafilter it therefore tends
  to `1` itself, not merely to a scalar. Scalar slack can live only on
  relators with a nonzero exponent-sum vector, such as power relators.
- **Commuting pairs commute on the nose.** If `[a,b] = 1` in `H` then
  `lim_omega ||[phi_n(a),phi_n(b)] - 1||_2 = 0`. The same holds for every
  `phi_n`-value of a word lying in the commutator subgroup of the free group.
  In particular anticommuting (Pauli-type) implementations of the frozen
  `C_2^3` of `binary-leavitt-hyperlinear-iff-24k-feasible` cannot survive, and
  neither can spin implementations of the `A_8` charts of the atlas criterion.
  Every finite subgroup has trivial limiting projective class.
- **It does not enlarge the chart sector.** By the previous item, the
  projective freedom is already absorbed by rescaling. What it removes is the
  bookkeeping of phases, since the correction exists and is unique in the
  ultraproduct. It proves nothing about which branch holds.

DERIVATION
leavitt-unit-projective-hs-lift-proof
