# The truncation obstruction for harmonic hosts (lane gq-steinberg-q, 2026-09-18)

Theorem: `bounded-harmonic-rings-are-not-finitely-presented`. This note records what it kills, why it works, and
what escapes it.

## Mechanism

A finite set of relations involves finitely many translates of the harmonic function `f = 1/(1+ℓ)`. Near a
translate of the base orbit, a relation reads as a polynomial `Q(t)` in the single value `t = f(g_0 x)`, with
everything else frozen. Two cases:
- Some local pattern is seen at infinitely many levels. Then `Q` vanishes at infinitely many values `1/(j+1)`, so
  `Q = 0`.
- Some pattern is seen at only finitely many levels. Then it disappears beyond those levels.

In both cases the truncation `f_k` satisfies the relations. But `f_k` takes values in `Z[1/(k+1)!]`, so every
large prime stops being invertible. The denominators of `Q` are produced "at infinity", and no finite set of
relations reaches infinity.

## What it kills

- `R_T`, the `SL_3(Z)` Toeplitz harmonic ring, with any base point.
  - The ring is not finitely presented.
  - No finitely presented ring with a unital map to `R_T` contains `Q`.
  - For every `N >= 3`, neither `E_N(R_T)` nor `PE_N(R_T)` is finitely presented.
  - So `sl3-toeplitz-harmonic-elementary-groups-are-fp` is refuted, and the route
    `q-algebra-host-via-sl3-toeplitz-harmonic-ring` is disabled.
- The pure odometer ring `R_K = ⟨u_s^(±1), f⟩`, over any residually finite `Γ` and any chain.
- Any variant with more finite-range coefficient functions: letters, block indicators, finitely many cylinders.

## What escapes, and why

- **`R_L` (Leavitt resolvent ring) is finitely presented.** Its denominators come from an unbounded operator `N`
  and one self-similarity relation, `N s_1 = s_1(N+1)` and `N s_2 = 0`. That single relation propagates to every
  level. A truncation of `N` breaks it, so the argument does not apply.
- **But `R_L` fails the scalar budget.** Any `Q`-algebra with a Leavitt `(1,d)`-tuple has `(Q^x)^(d-1)·I_m ⊆ E_m`
  (`leavitt-tuples-make-rational-scalar-powers-elementary`). So `Λ_N` is not finitely generated, and condition 3 of
  `q-algebra-with-fp-simple-projective-elementary-group` fails.

## The squeeze for the projective-elementary route to G

A host `R` for `q-algebra-with-fp-simple-projective-elementary-group` needs all of the following.
1. `R` finitely presented, or at least `E_N(R)` finitely presented.
   - This excludes bounded harmonic denominators in a crossed product over a compact space (this theorem).
   - The known finitely presented mechanism is self-similar, with an unbounded number operator.
2. Scalar budget: `Λ_N(R)` finitely generated. This excludes every ring with a Leavitt `(1,d)`-tuple, i.e. every
   ring with `R ≅ R^d` through such a tuple.
3. K-budget clauses R1 and R2, from `infinitely-generated-symbols-block-fp-elementary-groups` and
   `full-corners-must-kill-rational-k2-symbols`.

**Open design question.** Is there a finitely presented simple ring containing `Q` whose denominators come from a
self-similar unbounded relation, but which has no Leavitt tuple? One would look at finite-type (stably finite)
groupoids with a number operator, for example Toeplitz-type rings whose simple quotient keeps `Q`. For the
Toeplitz ring `q-embeds-in-a-corner-of-a-fp-toeplitz-ring`, `Q` sits in a corner built from the vacuum, and the
ring is not simple. Whether some simple quotient or variant keeps `Q` has not been checked here.
