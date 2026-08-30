---
rg: 2
id: stw63-every-z-pair-has-joint-central-bridge
kind: claim
title: Every pair of unital Jiang--Su embeddings has a joint central-sequence Jiang--Su bridge
refuted_by:
  - stw63-full-tracial-shadow-forbids-joint-z-bridge
---

**Refuted.**  The canonical pair in `Z*_(C)Z` has a reduced free-product
factor shadow with trivial central-sequence algebra.  Any proposed joint
bridge would map injectively into that scalar relative commutant; see
`stw63-full-tracial-shadow-forbids-joint-z-bridge`.

For every unital C-star algebra `B` and unital embeddings `phi,psi:Z->B`,
there is a unital homomorphism

```text
rho:Z -> B_infinity intersect phi(Z)' intersect psi(Z)'.
```

This was a sufficient pairwise absorption hinge, not a reformulation of
approximate unitary equivalence.  Its failure does not decide STW LXIII.

## Attempts

- If `B` is `Z`-stable, central-sequence absorption supplies a copy commuting
  with all of `B`, hence the required bridge.  The open point is to centralize
  only two given nuclear ranges without global absorption.
- A one-sided bridge commuting with `phi(Z)` does not suffice to compare it
  to `psi`; the same copy must commute with both ranges so that the two
  half-flips have a common endpoint.
- The canonical embeddings into the full free product are the decisive
  counterexample.  Their reduced free-product von Neumann closure does not
  obstruct approximate conjugacy, but its trivial central-sequence algebra
  forbids the stronger joint bridge.
- The claim is stronger than needed.  A weaker viable replacement would be a
  finite zigzag of central-sequence copies, consecutive members commuting,
  because the half-flip argument can be concatenated along such a zigzag.
