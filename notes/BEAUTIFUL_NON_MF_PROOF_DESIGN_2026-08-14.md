# The reader-facing non-MF proof

## The sentence to optimize

The construction should be remembered as

```text
Kazhdan transport forces u -> 1, while a Clifford model forces u^2 = -1.
```

Everything in the paper should either make this sentence rigorous, explain
where `u` comes from, or record a consequence.  Certificate arithmetic and
finite-stage estimates belong below that narrative boundary.

## The one-sign theorem

Let `Gamma` have property (T), let `iota : Gamma -> H`, and suppose

```text
t iota(Gamma) t^-1 <= iota(Gamma),        [c, iota(Gamma)] = 1.
```

Set

```text
d = t c t^-1,        u = [d, iota(a)].
```

If `epsilon = u^2` is a nontrivial central involution, then every
homomorphism from `H` to a norm matrix corona kills `epsilon`; in particular,
`H` is not operator-MF.

This is the ideal public obstruction.  Its proof is five lines.  If a corona
representation detects `epsilon`, cut by the nonzero central projection

```text
q = (1 - epsilon) / 2.
```

On that corner, `epsilon = -1`.  Kazhdan transport carries the asymptotic
commutation of `c` with `iota(Gamma)` to that of `d`, so `u -> 1` in normalized
Hilbert--Schmidt norm.  Hence `epsilon = u^2 -> 1`, contradicting the fixed
distance `||1 - (-1)||_2 = 2`.

The general finite-normal-subgroup theorem is stronger, but it should appear
after this proof.  It explains the scope of the method; it does not explain
the construction as quickly as the sign does.

## The conceptual presentation

Given a finitely presented property-(T) group `Gamma`, a proper injective
endomorphism `alpha`, and `a` outside `alpha(Gamma)`, adjoin `t` and an
involution `c` with

```text
t gamma t^-1 = alpha(gamma),        [c, Gamma] = 1.
```

Put `d = t c t^-1` and `u = [d,a]`.  The human presentation should retain a
redundant central sign `epsilon` and impose

```text
epsilon^2 = 1,        epsilon central,        u^2 = epsilon.
```

Now the analytic half says `epsilon -> 1`.  For the algebraic half, act on
the HNN cosets by Clifford generators.  The cosets `t Gamma` and
`a t Gamma` are distinct precisely because `a` is outside `alpha(Gamma)`.
Thus `u` becomes the product of two distinct Clifford generators and
`epsilon = u^2` becomes `-1`.

After the reader understands this, Tietze-eliminate `epsilon`.  Since `d` is
an involution,

```text
u^2 = [d, a d a^-1].
```

This gives the optimized presentation.  In the concrete example the letter
`z` is already a rotation generator, so the redundant sign should be called
`epsilon`, not `z`.

## The natural family

For every `n >= 3` and `m >= 2`, use

```text
Gamma_n = Z^n semidirect SL_n(Z),
alpha_m(v,A) = (m v,A),
a = (e_1,I).
```

The base is finitely presented and has property (T), `alpha_m` is injective,
and `a` is not in its image.  The construction therefore yields a family of
finitely presented non-MF groups.  The eight-generator `n = 3, m = 2` member
is the optimized explicit artifact, not the conceptual starting point.

## Four levels of exposition

1. **Main idea.** State the one-sign theorem and prove it by the negative
   corner in five lines.
2. **General construction.** Produce the sign with an HNN shift and a
   Clifford lamp.  State the affine family.
3. **Optimized example.** Display the eight-generator presentation and
   explain that it is obtained by eliminating the redundant sign.
4. **Formal verification.** Record that Lean independently proves the exact
   presentation facts, the Clifford witness, Kazhdan transport, and the
   rational Hodge lower bound `Delta_1 >= 1/500 I`.

The full Gram factor, residual table, spectral cutoffs, polar correction, and
row/column numerators remain available for audit but should not interrupt the
proof's semantic spine.

## Editorial tests

- A numerical constant belongs in the main text only if changing it changes
  the phenomenon.
- A reader should encounter `u` before the expanded word representing `u^2`.
- The concrete presentation should be visibly an optimization of the
  conceptual presentation, not the source of the idea.
- The first proof of non-MF should use the two-point sign corner.  Reynolds
  averaging over arbitrary finite normal subgroups comes later.
- Property (T) in ordinary prose is the classical theorem for
  `Z^3 semidirect SL_3(Z)`.  The exact `1/500` certificate is an independent
  formal check, not the mathematical explanation.
- Do not claim a hyperlinear obstruction: the finite-rank projection argument
  uses operator norm, and one-sided equivalence need not collapse in a
  tracial ultraproduct.

## Formal API

The Lean facade for this presentation is

```text
GroupApproximation/Sofic/KazhdanSignCriterion.lean
```

Its public declarations say both that the sign is killed by every genuine
norm-matrix-corona representation and that a surviving central sign obstructs
operator MF.  The implementation reuses the stronger verified finite-normal
theorem, while exposing only the two-element statement consumed by the
reader-facing proof.
