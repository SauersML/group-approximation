---
rg: 2
id: thompson-f-one-minus-x1-is-ore-with-every-element
kind: claim
title: In the group ring of Thompson's group F, 1 - x_1 has a nonzero common right multiple with every nonzero element (Guba's Question 3.20)
distinct_from:
  thompson-f-one-minus-x0-is-ore-with-every-element: that is the same statement for 1 - x_0, proved by a shift argument; this is the case x_1, which fixes [0, 1/2] and where the shift argument fails, obtained from the x_0 case by induction along nested supports.
  thompson-f-binomial-pairs-have-common-multiples: that settles 1 - h against binomials for every h; this settles 1 - h against every element, for h conjugate to x_0^{+-1} or x_1^{+-1}.
---

**ESTABLISHED.** Let `K` be a field and `R = K[F]`. Let `C_+` be the union of the
`F`-conjugacy classes of `x_0^{+-1}` and `x_1^{+-1}`. It contains every `x_n^{+-1}`.

1. **Common multiples along nested supports.** For any finitely many `g_1, ..., g_m` in
   `C_+`, `(1 - g_1) R ∩ ... ∩ (1 - g_m) R ≠ 0`.
2. **Answer to Question 3.20.** For every `h` in `C_+` and every nonzero `b` in `R`,
   `(1 - h) R ∩ b R ≠ 0`. In particular `(1 - x_1) u = b v` has a nonzero solution for
   every `b`.

This answers positively Question 3.20 of V. Guba, *Amenability problem for Thompson's
group F: state of the art*, arXiv:2305.07113v4 (2023), verbatim:

> Let R = K[F] be a group ring of F over a field K. Is it true that for any element b∈R,
> the equation (1−x1)u = bv has a non-zero solution in R?

**Mirror form.** The survey's automorphism `x_0 -> x_0^-1`, `x_1 -> x_1 x_0^-1` maps `C_+`
onto the union of the conjugacy classes of `x_0^{+-1}` and `(x_1 x_0^-1)^{+-1}`. So both
items hold for that union as well. That includes `x_0 - x_1`, since
`(x_0 - x_1) R = (1 - x_1 x_0^-1) R`.

**Consequence for the roots.** A non-Ore witness for `thompson-f-is-not-amenable` (via
`thompson-f-amenable-iff-group-ring-is-ore`) cannot have `1 - h` on one side when `h` is
conjugate to a power `+-1` of `x_0`, `x_1` or `x_1 x_0^-1`. By item 1, a system
`(1 - g_1) u_1 = ... = (1 - g_m) u_m` with all `g_i` in `C_+` always has a nonzero
solution. This extends survey Corollary 3.21, which is the case `g_i = x_(i-1)`.

**Scope.**
- The proof uses survey Theorem 3.18 (`thompson-f-one-minus-x0-is-ore-with-every-element`,
  which also has an independent counting proof on this graph), plus elementary PL facts.
- Novelty search, 2026-09-12:
  - Guba's full arXiv listing: the latest entries are arXiv:2305.07113 and
    arXiv:2304.04322 (2023).
  - The abstract of arXiv:2201.02308 (Guba 2022) says the `1 - x_1` case "remains open",
    and that paper states it as Question 1.
  - arXiv title/abstract searches for Thompson + Ore found no later answer.
  - Journals and other authors' post-2023 work were not searched beyond that.
- Not covered: `h` whose support has several components or does not reach an endpoint
  (for example `x_1 x_2^-1`), and mixed families from `C_+` and its mirror, whose supports
  `(p, 1)` and `(0, q)` are not nested.

Proof route: `thompson-f-one-minus-x1-is-ore-with-every-element-proof`. Artifact:
`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md`.
