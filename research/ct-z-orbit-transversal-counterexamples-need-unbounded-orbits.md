---
rg: 2
id: ct-z-orbit-transversal-counterexamples-need-unbounded-orbits
kind: claim
title: "Kourovka 20.44, constraint on counterexamples: if a finitely generated subgroup of CT(Z) has infinitely many orbits of size at most s for some s, then it has an orbit transversal of positive lower density; so a counterexample must have, for every s, only finitely many orbits of size at most s"
---

**ESTABLISHED** (lane proof, not reviewed). Elementary, no priority claimed. Kourovka 20.44
itself stays **OPEN**. This node records the constraint found while looking for a provable
counterexample.

## Statement

Let `G = ⟨S⟩ ≤ CT(Z)` with `S` finite and symmetric. Suppose that for some `s` infinitely
many `G`-orbits on Z have at most `s` points. Then:
- some residue class `C` has all but finitely many of its points in orbits of size at most
  `s`;
- the orbits meeting `[1, N]` number at least `N/(s·M) − O(1)`, where `M` is the modulus of `C`;
- the set of orbit minima in `N_0` has positive lower density.

So in a counterexample to 20.44, every orbit-size bound is violated by all but finitely many
orbits. The orbits of such a counterexample are infinite, or finite and of unbounded size.

## Proof

1. **Fixed sets are almost clopen.**
   - Let `h ∈ CT(Z)`. On each class of its modulus, `h` is `n ↦ (an + b)/c` with `a, c > 0`.
     On such a class `h` is either the identity or has at most one fixed point.
   - So `Fix(h) = U_h ⊔ F_h`, where `U_h` is a finite union of residue classes and `F_h` is
     finite.
2. **Small orbits are almost clopen.**
   - Let `W` be the finite set of elements given by words in `S` of length at most `2s + 2`.
   - The orbit of `x` has at most `s` points iff the ball of radius `s` around `x` in the
     Schreier graph has at most `s` points and is closed under `S`. That ball then equals the
     whole orbit.
   - Whether this holds is decided by the pattern of equalities `w(x) = w'(x)` for
     `w, w' ∈ W`, i.e. by which of the fixed sets `Fix(w'^(-1) w)` contain `x`.
   - By step 1, let `M` be a common modulus of all the `U_h` and let `F` be the union of all
     the `F_h`. Then the pattern depends only on `x mod M` when `x ∉ F`.
   - So `Z_{≤s} = {x : |G·x| ≤ s}` differs from a union of classes mod `M` by a finite set.
3. **Counting.**
   - The finite set of step 2 meets only finitely many orbits. So if `Z_{≤s}` meets infinitely
     many orbits, it contains some class `C = r(M)` up to finitely many points.
   - Each orbit meets `C ∩ [1, N]` in at most `s` points. So at least `(N/M − O(1))/s` orbits
     meet `[1, N]`.
   - Their minima in `N_0` are at most `N` and pairwise distinct. The minima lie in `N_0`
     because `CT(Z)` preserves `N_0`: a class transposition `r_1 + t m_1 ↔ r_2 + t m_2`, with
     `0 ≤ r_i < m_i`, preserves the sign of `t`. So an orbit through a point of `[1, N]` has its
     minimum in `[0, N]` (referee repair, bh-ref-d, e64cfcbeeb). ∎

## How this sharpens the search for a counterexample

Taken with `ct-z-orbit-transversal-dichotomy-is-collatz-hard`, any counterexample to 20.44
must meet three conditions.
- **(i) Big orbits.** It has infinitely many orbits, and orbits of every bounded size are
  finitely many (this node).
- **(ii) No local invariant at a rational point.** Suppose infinitely many invariant pieces
  accumulate at a point `ξ ∈ Ẑ` where all generators fix `ξ`.
  - If `ξ ∉ Q`, every generator's germ at `ξ` is the identity, since `(1 − λ)ξ` must be
    rational. So a whole box around `ξ` is fixed pointwise, which is again (i).
  - If `ξ ∈ Q`, every germ is multiplicative about `ξ`. Near `ξ` this preserves the cofactor
    of `q(n − ξ)` prime to the slopes. That points to transversals of positive density (sketch;
    this is the valuation-strata case of the bh-free-58 board).
- **(iii) Mixing (heuristic; referee bh-ref-d).** Orbits must be glued by translations, as in
  3x+1 dynamics. The Terras–Everett count then makes many orbits sparse automatically, so the
  whole difficulty is to prove that there are infinitely many.
  - `G_T` meets (i)–(iii) exactly when the 3x+1 map has infinitely many components on Z.
  - No finitely generated example with a *provable* infinite family of glued orbits is known
    to this lane. The obvious symmetries that would copy one orbit infinitely often, such as
    dilation equivariance `g(3n) = 3g(n)`, force zero translation parts, and therefore
    multiplicative dynamics, which falls under (ii).

## Lesson for general BH

**Orbit statistics of subgroups in arithmetic hosts split into two layers.**
- **The clopen layer.** Bounded orbits, and invariants that are local at a point, are forced
  onto whole residue classes by affine rigidity. There they are visible and have positive
  density.
- **The dynamical layer.** Unbounded glued orbits are the Collatz regime. There
  sparse-versus-finite is a stopping-time question.

**For host design.** Any construction that needs control of orbits of an embedded subgroup
can control the clopen layer by finite computation, but it cannot control the dynamical
layer. As with type (A), orbit finiteness should be imposed on the host's own action rather
than read off a subgroup.
