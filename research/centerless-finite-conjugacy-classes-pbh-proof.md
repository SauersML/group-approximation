---
rg: 2
id: centerless-finite-conjugacy-classes-pbh-proof
kind: route
title: Two-sided translation on G has the diagonal as stabilizer and one pair-orbit per nontrivial conjugacy class
target: centerless-fp-finitely-many-conjugacy-classes-gives-pbh
requires:
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - simple-envelope-forces-solvable-word-problem
---

Let `G` be finitely presented, `Z(G) = 1`, with finitely many conjugacy classes.
Let `G x G` act on `G` by `(a,b)·x = a x b^-1`. It is an action:
`(a,b)·((c,d)·x) = a c x d^-1 b^-1 = (ac, bd)·x`.

1. **Faithful.** If `a x b^-1 = x` for all `x`, then `x = 1` gives `a = b`. Then
   `a x a^-1 = x` for all `x`, so `a ∈ Z(G) = 1`.
2. **Finitely presented.** `G x G` has the presentation with the generators and
   relators of two copies of a finite presentation of `G`, plus the commutators
   of each generator of the first copy with each generator of the second.
3. **Finitely generated stabilizers.** The action is transitive
   (`(x,1)·1 = x`), so all stabilizers are conjugate. `Stab(1) = {(a,b) : a b^-1 = 1}`
   is the diagonal `Δ ≅ G`, which is finitely generated.
4. **Finitely many orbits of two-element subsets.**
   - An ordered pair `(x,y)` with `x ≠ y` is moved by `(x^-1, 1)` to `(1, x^-1 y)`.
   - `(1,u)` and `(1,v)` lie in one orbit iff some `(a,b)` fixes `1`, i.e. `a = b`,
     and `a u a^-1 = v`.
   - So orbits of ordered pairs of distinct points correspond to conjugacy classes
     of nontrivial elements, of which there are finitely many.
   - Each orbit of two-element subsets is the image of at most two ordered-pair
     orbits, so these are finite too.

So the action is of type (A), and `G x 1 ≤ G x G` gives clause (i) of BFFHZ
Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`).

If `G` is simple, it is finitely presented simple. It has solvable word problem
by `simple-envelope-forces-solvable-word-problem`, and Theorem C (i) ⟹ (iv) embeds
it in a finitely presented simple MIF group. A nontrivial simple group with
trivial center is nonabelian, so the center hypothesis holds automatically once
`G` is infinite, or finite and nonabelian. `∎`
