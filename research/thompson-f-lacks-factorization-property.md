---
rg: 2
id: thompson-f-lacks-factorization-property
kind: claim
title: Thompson's group F does not have Kirchberg's factorization property
distinct_from:
  thompson-f-is-not-hyperlinear: that is the Connes-embedding statement, which implies this one; this is only the failure of amenability of the canonical trace on C*(F), and it gives nonhyperlinearity only together with a lifting input such as thompson-f-full-c-star-algebra-has-llp.
  rank-twelve-leavitt-group-lacks-factorization-property: that is a Kazhdan group, where Kirchberg reduces the factorization property to residual finiteness; F has the Haagerup property, so no rigidity reduction exists, and the finitary content is the ucp collapse statement below.
---

**OPEN.** Thompson's group `F` does not have Kirchberg's factorization property.

**Finitary form** (`thompson-f-factorization-iff-ucp-models-separate`). For every
`epsilon > 0` there is `delta > 0` such that the following holds for every unitary representation `pi` of
`F` and every finite-rank projection `P`:

```text
||[pi(a),P]||_HS, ||[pi(b),P]||_HS < delta ||P||_HS
    ==>  ||[P pi(a) P, P pi(b) P]||_HS < epsilon ||P||_HS.
```

In words, compressions of honest representations of `F` to almost-invariant finite-dimensional
subspaces almost commute, uniformly.

**Position.**
- It is implied by `thompson-f-is-not-hyperlinear`, since the factorization property implies
  hyperlinearity.
- It implies nonamenability of `F`: amenable groups have the factorization property, because the full
  and reduced algebras agree and are nuclear.
- If it is false and `F` is nonamenable, `C*(F)` is nonexact
  (`nonamenable-factorization-groups-have-nonexact-full-cstar`).
- `thompson-f-following-models-separate-iff-mean-charges-commutator` is the permutation analogue for
  models that follow a genuine `F`-set. The displayed statement is the ucp analogue over arbitrary
  unitary representations, which include the Koopman, Jones, Pythagorean and `O_2` representations. So
  a collapse theorem for any single one of these families proves only a special case.

## Attempts

- **Invariant-mean transplant from following models** (lane swarm-0917-w5-pull2-non-1, 2026-09-17).
  - **Where it works.** For a Koopman representation `pi = kappa_Omega` of an `F`-set, with `P` diagonal
    in `ell^2(Omega)`, a separating compression gives an invariant mean charging `Moved(c)`. Then clause 4
    and the confined-moved-set corollary of
    `thompson-f-following-models-separate-iff-mean-charges-commutator` apply.
  - **Where it dies.** At the diagonalization step. A general `pi`, or a general almost-invariant `P` even
    for Koopman `pi`, has no almost-invariant masa that `pi(F)` normalizes and `P` almost commutes with.
    This is the frame problem `thompson-f-hyperlinear-models-normalize-a-full-masa` in the compression
    setting. The honest relators upstairs do not supply the masa.
  - **Structural cost.** Any proof proves nonamenability of `F`. So it must escape
    `thompson-f-cohomology-certificates-cannot-prove-nonamenability`.
