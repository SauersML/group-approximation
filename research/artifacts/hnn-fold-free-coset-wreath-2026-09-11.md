# HNN extensions fold into free coset wreath products

Date: 2026-09-11. Written proof, not a Lean certificate.

## 1. Statement

Let `B` be a group, `phi: C -> C'` an isomorphism between subgroups of `B`, and

    G = < B, t | t^(-1) c t = phi(c)  (c in C) >.

Let `rho: G -> H` be any homomorphism. Put `X = H/rho(C)`, `o = rho(C)`, let
`F_X` be free on `{z_x : x in X}`, and form

    W = F_X rtimes H,       h z_x h^(-1) = z_(h x).

**Theorem A.** The formulas `Phi(b) = rho(b)` and `Phi(t) = z_o rho(t)` define a
homomorphism `Phi: G -> W` with `pi o Phi = rho`, where `pi: W -> H` is the
quotient map. If `rho` is injective on `B`, then `Phi` is injective.

**Theorem B (local form).** Let `E` be a finite subset of `G`. Fix reduced forms
(Britton) of the elements of `E^(-1)E \ {1}`. Suppose that for every inner
syllable `b` of these forms:
* `rho(b)` is not in `rho(C')` when `b` sits between `t` and `t^(-1)`;
* `rho(b)` is not in `rho(C)` when `b` sits between `t^(-1)` and `t`.

Suppose also that `rho(b) != 1` whenever one of these elements is a single
syllable `b` of `B`. Then `Phi` is injective on `E`.

**Corollary C.** `G` is sofic if for every finite `E` some `rho: G -> H`
satisfies Theorem B, `H` is sofic, and `H action H/rho(C)` is a sofic action.
Indeed `W` is then sofic by Gao--Kunnawalkam Elayavalli--Patchell,
arXiv:2401.04945, Theorem 3.7 (free case). A group admitting, for every finite
set, a homomorphism to a sofic group injective on that set is sofic.
