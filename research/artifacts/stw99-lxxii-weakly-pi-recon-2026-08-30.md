---
title: STW Problem LXXII --- the weakly purely infinite problem, Cuntz-semigroup recon (2026-08-30)
---

Problem LXXII (Kirchberg--Rørdam 2002, Question 9.5): weakly purely
infinite = purely infinite (= strongly purely infinite)?

## Frame

`A` wpi iff `∃n ∀x ∈ Cu(A): n x = ∞ x`; `A` pi iff this holds with
`n = 1`, i.e. `Cu(A)` is the ideal lattice `{0, ∞}`-valued.  KR Prop 4.15
(survey Prop 3.9): pi ⟺ wpi + Global Glimm Property.  Thiel--Vilalta
Theorem 7.1: GGP ⟺ nowhere scattered + `Cu` ideal-filtered + property
(V); wpi algebras are nowhere scattered.  So LXXII(weak ⟹ plain) ⟺
"`Cu` of every wpi algebra is ideal-filtered and has (V)".

## No functional obstructions

Any dimension function `d` on a wpi algebra has `n d(x) = ∞ d(x)`, so
`d ∈ {0, ∞}`-valued: there are no quasitraces and no comparison
functionals.  All residual order structure in `Cu(A)` between `x` and
`∞x = nx` is ideal-positional.  The conjecture (pi) says it collapses.

## Property (V): the exact residual

Given `d'_j ≪ d_j` (j = 1,2), `d_1, d_2 ≪ c`, `c + d_1, c + d_2 ≪ x`,
one needs `y + z ≤ x` with `d'_1 + d'_2 ≤ ∞y, ∞z`.  Since
`d_j ≪ c ≤ ∞c = sup_{c' ≪ c, k} k c'`, there is a common `c' ≪ c` with
`d_1, d_2 ≤ k c'`.  Then `y := c'` satisfies `d'_1 + d'_2 ≤ ∞y`, and
`z := d''_1` (with `d'_1 ≪ d''_1 ≪ d_1`) satisfies
`y + z ≤ c + d_1 ≤ x`.  The ONLY failing requirement is
`d'_2 ≤ ∞ d''_1`: the ideal of `d_1` need not contain `d_2`.  Property
(V) for wpi is thus exactly: some `z` fitting beside `c'` in `x` whose
ideal contains both `d'_1` and `d'_2` — the join `d_1 ∨ d_2` if `Cu`
were a semilattice.  A wpi counterexample to LXXII must therefore have
two elements `d_1, d_2` under a common `c` such that no single element
inside `x` beside `c'` generates both ideals: a genuinely
two-dimensional ideal-position obstruction.

## Ideal-filteredness: the position problem

For `v' ≪ v ≪ ∞x, ∞y` with `x = ⟨a_1⟩, y = ⟨a_2⟩` and `v = ⟨b⟩`,
`b ∈ I_1 ∩ I_2`: KR absorption in wpi gives `b ≾ n c_0 = ∞⟨c_0⟩` for any
`c_0` with `(b−ε)_+ ∈ Ideal(c_0)`.  So ideal-filteredness needs one
`c_0 ≾ a_1, a_2` with `(b − ε)_+ ∈ Ideal(c_0)`.  The two subequivalences
are free for `c_0 := a_2^{1/2} X a_2^{1/2}`, `X ∈ her(a_1)_+`:
`c_0 ≤ ‖X‖ a_2 ≾ a_2`, and by `yy^* ~ y^*y` with `y = X^{1/2} a_2^{1/2}`,
`c_0 ~ X^{1/2} a_2 X^{1/2} ≤ ‖a_2‖ X ≾ a_1`.  What can fail is only the
ideal: in `M_2(C_0(U))` with `a_1 = f e_{11}`, `a_2 = g e_{22}` the
product vanishes though `I_1 ∩ I_2 ≠ 0`; there the repair is a rotation
(`c_0 := min(f,g) e_{22} ≾ a_1` via a partial isometry).  So
ideal-filteredness for wpi is a position/rotation problem: move
`her(a_1)` against `a_2` inside the wpi algebra so a single product
element generates enough of `I_1 ∩ I_2`.  Weak pure infiniteness
provides `n`-fold room (`b ≾ a_1^{⊕ n}` exactly), and the missing step
is compressing `n`-fold witnesses to single ones — the same
`n`-to-`1` collapse the problem asserts, but now needed only for the
IDEAL of a witness, not its class.

## Assessment

The reformulation is faithful (no shortcut), but it localises LXXII into
two finitary statements about wpi Cuntz semigroups where every
functional obstruction is dead and only ideal position survives.  A
counterexample hunt should target: a wpi `Cu` where two ideals under a
common element admit no joint single-element witness beside it — no such
semigroup is currently known even abstractly with (O5)-(O8)
(Thiel--Vilalta record no C*-algebra whose `Cu` lacks property (V),
their Question 5.4).

## Closed positive class from the existing Global Glimm graph

If the closed ideal lattice of a weakly purely infinite algebra is linearly
ordered, then weak and plain pure infiniteness coincide.  Indeed, weak pure
infiniteness passes to quotients and is impossible for a nonzero
finite-dimensional algebra, so the algebra has no nonzero finite-dimensional
representations.  The established Cairn theorem
`chain-ideal-lattice-solves-lxxiii` then gives the Global Glimm Property.
Kirchberg--Rordam's characterization finishes the implication.  This uses
the stronger square-zero packet theorem already present in the graph and
avoids reproving ideal-filteredness and property (V) separately.

Sources: Kirchberg--Rørdam, Infinite non-simple C*-algebras (AIM 2002),
Prop 4.15, Question 9.5; Thiel--Vilalta arXiv:2204.13059 Thm 7.1, Q5.4;
Vilalta arXiv:2512.13334 Prop 3.9, Cor 3.10.
