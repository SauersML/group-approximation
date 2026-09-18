---
rg: 2
id: shell-mobius-extensions-see-finitely-many-primes
kind: claim
title: Adjoining to a finitely generated Mobius group finitely many tree automorphisms that are Mobius off 0 and shell-wise Mobius near 0, with their sections at vertex 0 in the group, gives a group that meets PGL_2(Q) inside some PGL_2(Z[1/N])
distinct_from:
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that assumes finitely many pieces per element; this allows infinitely many Mobius pieces accumulating at a singular point, the prime-shift design, and uses the section condition at that point.
  iwahori-overgroups-not-automaton-linear-or-metabelian: that rules out automaton, linear, metabelian and ring-affine overgroups of Gamma_p; this rules out the natural non-linear candidates obtained from Gamma_p(1) by adjoining finitely many spinal prime-shift elements.
  rational-iwahori-group-lies-in-fp-self-similar-group: that is the open input; this kills its prime-shift construction family.
---

**ESTABLISHED** through `shell-mobius-extensions-see-finitely-many-primes-proof`.
Lane proof, not independently reviewed. No priority is claimed.

## Setting

- `T_p` is the `p`-ary tree, `∂T_p = Z_p`, and `S_j = p^jZ_p^×` is the shell of
  radius `p^{-j}` around 0.
- Say `h ∈ PGL_2(Q)` **agrees with** a map `f` on a set `U` if `h` is defined on
  `U` and `h|_U = f|_U`. For `ρ(z) = pz`, the section at vertex 0 of `f` is
  `f|_0 = ρ^{-1} f ρ`.
- Let `Γ_0 <= PGL_2(Q)` be finitely generated and act on `Z_p` by tree
  automorphisms, for example `Γ_p(1)` of
  `rational-iwahori-group-is-union-of-fp-self-similar-groups`.
- Let `g_1, ..., g_r ∈ Aut(T_p)` satisfy:
  1. `g_i(0) = 0`;
  2. **Möbius off 0**: every `x ≠ 0` has a neighborhood on which `g_i` agrees
     with some element of `PGL_2(Q)`;
  3. **shell-wise Möbius**: there are `J` and `M^{(i)}_j ∈ PGL_2(Q)` such that
     `g_i` agrees with `M^{(i)}_j` on `S_j` for every `j >= J`.
- Put `Λ = ⟨Γ_0, g_1, ..., g_r⟩`.

The **prime-shift design** is the case `g(z) = u_{v(z)} z`, where `(u_j)`
enumerates generators of `Z_(p)^×`. Then `M_j = d_{u_j}`, and the sections of
`g` produce every dilation `d_{u_j}` (up to translations in `Γ_p(1)`).

## Statement

If every section `g_i|_0` lies in `Λ`, there is an integer `N >= 1` such that
every element of `PGL_2(Q)` that agrees with some element of `Λ` on a nonempty
open subset of `Z_p` lies in `PGL_2(Z[1/N])`. In particular:
- `Λ` contains the dilation `d_q` for only finitely many primes `q`;
- `Λ` does not contain the rational Iwahori group `Γ_p`;
- no self-similar group of this form witnesses
  `rational-iwahori-group-lies-in-fp-self-similar-group`, whether or not it is
  finitely presented.

## Reading

- Adjoining spinal elements to `Γ_p(1)` cannot absorb infinitely many primes
  when the spine is Möbius shell by shell. The section condition at the
  singular point turns into a recursion `M_{j+1} = ρ F(M_j) ρ^{-1}`, where `F` is
  a fixed word map with Möbius coefficients. That recursion keeps every shell
  map inside one finitely generated subgroup of `PGL_2(Q)`.
- A witness `Λ` therefore needs generators that are **not** Möbius on infinitely
  many shells around a singular point, or that have infinite singular sets.
  This is consistent with the non-linearity required by
  `iwahori-overgroups-not-automaton-linear-or-metabelian`.
- By conjugating with `Γ_p(1)`, which is transitive on `Q ∩ Z_p`, the same
  holds with the singular point 0 replaced by any rational point of `Z_p`, as
  long as the section condition is transported with it.
