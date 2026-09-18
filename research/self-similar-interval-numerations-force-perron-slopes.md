---
rg: 2
id: self-similar-interval-numerations-force-perron-slopes
kind: claim
title: A finite self-similar subdivision of intervals whose ratios are powers of λ ∈ (0,1) exists only if 1/λ is a weak Perron number, i.e. an algebraic integer at least as large in modulus as each of its conjugates; so no coding of this kind, and none of the finiteness proofs built on one, reaches Tanner's V_λ for λ = 2/3, for transcendental λ, or when 1/λ has a conjugate of larger modulus
distinct_from:
  pisot-unit-slope-stein-groups-are-finitely-presented: that is a sufficient condition (an (F) unit slope) proved through such a subdivision; this is the necessary condition on the slope for any such subdivision to exist.
  pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp: that widens the sufficient side inside the Pisot units; this bounds from outside every method of that shape.
  stein-derived-groups-need-computable-modules: that is a necessary condition for finite presentation of D(V) itself (computable ratios); this is a necessary condition for the coding method, not for finite presentation.
  hard-slope-thompson-groups-have-no-piecewise-projective-hosts: that proves non-finite presentation for hard Liouville slopes; this only excludes numeration codings, for every transcendental slope.
---

**ESTABLISHED** by `self-similar-interval-numerations-force-perron-slopes-proof` (lane `bh-partials`; elementary
Perron–Frobenius argument, not reviewed; no priority claimed, since it is close to Lind's theorem that Perron numbers are
exactly spectral radii of integral matrices).

## Definition

A **λ-numeration** of `[0,ℓ)`, for `λ ∈ (0,1)`, consists of:
- finitely many types `s` with lengths `L_s > 0`, the type `s_0` of `[0,ℓ)` having `L_{s_0} = ℓ`;
- for each type `s`, a cut of `[0, L_s)` into finitely many consecutive intervals, the `i`-th of type `t_i` and of
  length `λ^{k_i} L_{t_i}` with `k_i ≥ 1`.

Iterating the cuts gives cones (intervals) and a finite type graph. Every BBMZ-style coding of a Stein group on main is a
λ-numeration read as an edge shift: the β-shift of an (F) unit, its block recodings, and the squared negative-base coding.
So is the subdivision into `n` equal parts behind Thompson--Higman groups, with `λ = 1/n`.

## Statement

If a λ-numeration exists, then `β := 1/λ` is a **weak Perron number**:
- `β` is an algebraic integer;
- `|σ(β)| ≤ β` for every conjugate `σ(β)`.

In particular:
1. **Rational slopes.** A rational `λ` needs `1/λ ∈ Z`. So `λ = 2/3` has no λ-numeration; directly, every piece of
   every cut has strictly larger 2-adic valuation than the interval cut, since `|2/3|_2 < 1`.
2. **Transcendental slopes** have none.
3. **Slopes whose inverse has a conjugate of larger modulus** have none, even when they are units.

## Consequences for Tanner's question (arXiv:2312.07375, TeX l. 915)

- **Where the method has to stop.** Every positive answer on main codes `V(Γ,⟨λ⟩,ℓ)` by a λ-numeration whose boundary set
  is `Γ ∩ [0,ℓ)`, then applies BBMZ Theorem A. So the method stops at weak Perron `1/λ`. Within that range, the
  proven cases are Pisot, which is where the nucleus is finite.
- **Weak Perron but not Pisot.** A numeration with boundary set `Γ ∩ [0,ℓ)` would make `V` a full RSG. Its finite
  presentation would then be BBMZ's open non-contracting case, the same finiteness gap as BBMZ-hyperbolic Question 1.4
  (`fp-rsgs-have-fp-full-closures`). It is expected, not proved here, that the nucleus is infinite off Pisot. The
  classical fact behind this is that finite-automaton normalization forces a Pisot base (Berend–Frougny; not read at
  source).
- **The test case λ = 2/3.** Here `Γ = Z[2/3, 3/2] = Z[1/6]`.
  - **V is perfect.** `H_0 = Z[1/6]/(1/3)Z[1/6] = 0`. `H_1 = H_2(Z[1/6] ⋊_{2/3} Z) = 0`, because
    `H_2(Z[1/6]) = 0` and `2/3 − 1` acts injectively. So `V_{2/3}^{ab} = 0`, and `V_{2/3} = D(V_{2/3})` is simple
    (Tanner), and 2-generated (Tanner, Theorem `fg when fg by alg`, since `Z[1/6] ⋊ Z` is finitely generated).
  - **Boone–Higman already holds for it.** `V_{2/3} ≤ V(Z[1/6],⟨2,3⟩,1)`. It is perfect, so it lies in
    `D(V(Z[1/6],⟨2,3⟩,1))`, which is simple (Tanner), and of type `F_∞` by Stein, as quoted by Tanner (TeX l. 912–914; Stein's paper not
    read at source). So
    `V_{2/3}` embeds in a finitely presented simple group.
  - **Its own finite presentation is OPEN.** No numeration exists (item 1). The metabelian group
    `Z[1/6] ⋊_{2/3} Z` and the line group `G(R; Z[1/6], gp(3/2))` are infinitely presented (Bieri–Strebel,
    arXiv:1411.2868, Preface Proposition 4, read at source). But no compact-interval analogue of that obstruction is
    known (same page).

## Lesson for general BH

- **What the barrier is.** Self-similar codings exist only for weak Perron inverse slopes; that is a Perron–Frobenius
  barrier, with the finite places (algebraic integer) and the infinite places (dominant conjugate) as its two halves.
- **Which gate is left where.**
  - Inside the barrier, finite presentation needs a finite nucleus (Pisot), and the gate is BBMZ's contracting theorem.
  - Just inside, for Perron but not Pisot slopes, the gate is the non-contracting RSG question (BBMZ Q1.4).
  - Outside, as for `2/3`, any finite presentation needs a genuinely non-self-similar method. For Boone–Higman these
    groups are already harmless: they sit inside Stein's `F_∞` groups.
