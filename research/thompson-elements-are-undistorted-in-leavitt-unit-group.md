---
rg: 2
id: thompson-elements-are-undistorted-in-leavitt-unit-group
kind: claim
title: Every infinite-order element of Thompson's V, and every conjugate of one, generates an undistorted cyclic subgroup of the binary Leavitt unit group
distinct_from:
  thompson-v-cyclic-subgroups-are-undistorted: that is undistortion inside V itself; this is undistortion inside the much larger Kazhdan group Q, whose extra generators could a priori shorten powers of Thompson elements.
  leavitt-north-south-thompson-unit-has-cyclic-centralizer: that computes centralizers of one explicit north--south unit and gives a masa; this is a metric statement for all infinite-order Thompson elements and their conjugates.
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that asks for undistortion-type control of all units; this proves it for units conjugate into V.
---

**ESTABLISHED** by `thompson-elements-are-undistorted-in-leavitt-unit-group-proof`.

Let `Q = L_(F_2)(1,2)^x` with a finite generating set `S`, and let `V <= Q` be the
embedded Thompson group. For every `g` in `V` of infinite order and every `h` in `Q`,
there are `kappa > 0` and `C` with

```text
|h g^z h^-1|_S >= kappa |z| - C      for all integers z.
```

**Corollary.** In `Q`:
- no integer Heisenberg subgroup has a central commutator conjugate into `V`;
- no subgroup `BS(1,k) = <x,t | t x t^-1 = x^k>` with `|k| >= 2` has `x` conjugate into `V`.

In both groups the element in question is distorted, quadratically in the Heisenberg
group and exponentially in `BS(1,k)`. See `thompson-v-has-no-heisenberg-subgroup-proof`.

**The mechanism.**
- The depth `ell(x) = min{ N : x in span{ s_alpha t_beta : |alpha|, |beta| <= N } }` is
  subadditive on `R = L_(F_2)(1,2)`, so word length in `Q` dominates `ell / max_S ell`.
- A unit of depth `N` rewrites at most `N` leading letters of any sequence into at most
  `N` letters.
- For a Thompson element, the germ of `g^z` at a periodic point changes prefix length by
  an amount growing linearly in `z` (`thompson-v-powers-have-linearly-growing-slope`).

**What it leaves open.** A Heisenberg center or a Baumslag--Solitar base in `Q` has to
be a unit that is not conjugate into `V`. Such genuinely linear units have no germs, and
their depth growth is controlled only by the numerical screen on
`leavitt-unit-group-has-no-integer-heisenberg-subgroup`.
