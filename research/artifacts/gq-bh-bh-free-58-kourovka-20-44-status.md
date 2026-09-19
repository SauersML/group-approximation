# Kourovka 20.44 (Kohl): best-known form of the dichotomy

> **Superseded (2026-09-19).** The full, current picture is the node
> `kourovka-20-44-holds-for-rank-one-slope-groups`. The V-case conjecture below is now proved
> (`ct-empty-z-subgroups-satisfy-the-orbit-transversal-dichotomy`, refereed PASS), as are the
> integer-ray and the frozen mixed-ray cases. This page is kept as the record of the search.

Lane bh-free-58, 2026-09-18. Status: **OPEN**. This page collects what is proved and what the
search for a provable counterexample found.

**Problem** (21st issue, 2026, verbatim): "Is it true that a finitely generated subgroup of
CT(Z) either has only finitely many orbits on Z or there is a set of representatives for its
orbits on Z which has positive density?"

For a finitely generated `G ≤ CT(Z)`, write `ν_G(N)` for the number of orbits meeting `[−N, N]`.
A set of representatives of positive (upper) density exists iff `ν_G(N) ≥ cN` for some `c > 0`
along a sequence `N → ∞`.

## What is proved (lane proofs, not reviewed)

1. **Clopen layer** (`ct-z-orbit-transversal-counterexamples-need-unbounded-orbits`,
   1c4a8a43c). If infinitely many orbits have size at most `s`, then `ν_G(N) ≥ N/(sM) − O(1)`.
   The reason is affine rigidity: the points in orbits of size at most `s` form a union of
   residue classes up to a finite set.
2. **Collatz layer** (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`, 7b84a747f).
   - For Kohl's `G_T = ⟨τ_{0(2),1(2)}, τ_{1(2),2(4)}, τ_{1(4),2(6)}⟩ ≤ CT_{{3}}(Z)`, the
     Terras–Everett count gives `ν_{G_T}(N) = o(N)`.
   - `G_T` has finitely many orbits iff the 3x+1 map has finitely many components on Z.
   - Credit: Kohl for `G_T`, `r` and `s`; Terras and Everett for the stopping-time lemma.

## Best-known form

    20.44 holds for G_T  ⟺  the 3x+1 map has finitely many components on Z.

- **An affirmative answer** would prove that the 3x+1 map has only finitely many cycles and
  finitely many divergent classes on Z. That is open (Lagarias).
- **A negative answer** follows from any infinite family of 3x+1 components, for example
  infinitely many cycles on Z.
- **Where a counterexample must live.** By item 1 its infinitely many orbits must be unbounded
  or infinite, glued by translations, and must carry no local invariant at a rational point of
  `Ẑ`. This is exactly the mixing (carry) regime of at least two primes.

## Why no provable counterexample was found

- **Conway-type maps.** Conway's amusical permutation, and the prefix-code maps `α_{P,Q}` of
  `conway-amusical-permutation-is-the-full-three-shift`, are conjugate on `Ẑ` to full shifts.
  - The integers, however, sit in the shift at points whose itineraries are governed by
    Lagarias's periodicity conjecture. Conway's orbit-of-8 question is still open.
  - So no integer orbit structure is known for them.
- **Two primes always mix digits.** Every canonical map between a box whose modulus is a power
  of 2 and a box whose modulus is a power of `p` multiplies the 2-adic coordinate by a unit
  `p^a`, which mixes the 2-adic digits by carries. So in two primes no map is simultaneously
  mixing and exactly solvable on the integers.
- **One prime (`CT_∅(Z) ≅ V`).** A counterexample there seems impossible.
  - Canonical maps rewrite only the low 2-adic digits. So orbit invariants are either local
    at rational points, which item 1 and the multiplicative-germ argument exclude, or
    high-digit tails, which occur with positive density.
  - This is not proved. A proof would go through Büchi–Caucal regularity of prefix-rewriting
    classes. **Conjecture:** 20.44 holds for every finitely generated subgroup of
    `CT_∅(Z)`.
- **Machines and passengers.** Valuation-coded constructions (counter machines, lamp and
  passenger codes) always keep a cofactor invariant, which gives positive density. Scaling
  symmetries such as `g(3n) = 3g(n)`, which would copy one orbit infinitely often, force
  multiplicative germs.

## Lesson for general BH

The subgroup-orbit statistics of the arithmetic hosts `CT_P(Z)` follow the same
one-base/two-base split as their torsion and automorphism theory:
- **One prime.** Tame, finite-type dynamics (V).
- **Two primes.** The carry makes integer dynamics Collatz-hard already for three class
  transpositions.

For Boone–Higman host design, finiteness conditions such as type (A) must be imposed on the
host's own clopen action. They can never be certified from an embedded subgroup's orbits on
the integers.
