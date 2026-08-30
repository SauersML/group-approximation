---
rg: 2
id: stw63-every-z-pair-has-joint-central-bridge
kind: claim
title: Every pair of unital Jiang--Su embeddings has a joint central-sequence Jiang--Su bridge
---

For every unital C-star algebra `B` and unital embeddings `phi,psi:Z->B`,
there is a unital homomorphism

```text
rho:Z -> B_infinity intersect phi(Z)' intersect psi(Z)'.
```

This is a sufficient pairwise absorption hinge, not a reformulation of
approximate unitary equivalence.  It may fail even if STW LXIII is true.

## Attempts

- If `B` is `Z`-stable, central-sequence absorption supplies a copy commuting
  with all of `B`, hence the required bridge.  The open point is to centralize
  only two given nuclear ranges without global absorption.
- A one-sided bridge commuting with `phi(Z)` does not suffice to compare it
  to `psi`; the same copy must commute with both ranges so that the two
  half-flips have a common endpoint.
- The canonical embeddings into free-product hosts are a decisive stress
  test.  Their von Neumann closures do not obstruct approximate conjugacy,
  but a joint bridge must live in the C-star sequence algebra itself.
- The claim is stronger than needed.  A weaker viable replacement would be a
  finite zigzag of central-sequence copies, consecutive members commuting,
  because the half-flip argument can be concatenated along such a zigzag.
