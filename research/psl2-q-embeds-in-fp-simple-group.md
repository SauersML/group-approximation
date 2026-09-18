---
rg: 2
id: psl2-q-embeds-in-fp-simple-group
kind: claim
title: The countable simple group PSL_2(Q) embeds in a finitely presented simple group
distinct_from:
  sl2-q-embeds-in-fp-simple-group: that is the central extension SL_2(Q); this is its simple quotient, and neither statement is known to imply the other.
  gl-n-q-embeds-in-fp-simple-group: that is GL_n(Q) for every n >= 2, which implies this through PGL_2(Q) <= GL_4(Q) (route psl2-q-bh-via-root); this is one countable simple group.
  boone-higman-iff-infinite-simple-inputs: that concerns finitely generated simple inputs; PSL_2(Q) is simple but not finitely generated.
---

**OPEN.** There is a finitely presented simple group containing
`PSL_2(Q) = SL_2(Q)/{±I}`.

`PSL_2(Q)` is itself simple (Jordan--Dickson: `PSL_2(K)` is simple for every
field with `|K| > 3`). It is countable and not finitely generated, and it has
solvable word problem for its standard enumeration. So this asks for a
finitely presented simple overgroup of one specific infinitely generated
countable simple group. It follows from `gl-n-q-embeds-in-fp-simple-group`
by `psl2-q-bh-via-root`.

## Structure

- **Embeddings in larger linear groups.**
  - `PSL_2(Q) <= PGL_2(Q)`.
  - The conjugation action on `M_2(Q)` embeds `PGL_2(Q)` in `GL_4(Q)`
    (`gl-n-q-targets-are-cofinal-in-n`).
  - The adjoint action on the trace-zero matrices embeds `PGL_2(Q)` in
    `SL_3(Q)`. The kernel of `Ad` on `GL_2(Q)` is the scalars, and
    `det Ad(g) = 1`, since `det ∘ Ad` is a character that is trivial on
    diagonal and unipotent matrices, which generate `GL_2(Q)`.
- **Its action on the projective line.** `PSL_2(Q)` acts 2-transitively on
  `P^1(Q)`, and `PGL_2(Q)` acts sharply 3-transitively. The point stabilizers
  are Borel images. They contain `(Q,+)`, so they are not finitely generated,
  and this action is not itself a type (A) action.
- **Subgroups that constrain hosts.** The images of the unipotent `(Q,+)` and
  of `BS(1,4)` from `sl2-q-embeds-in-fp-simple-group` are still embedded. So
  O1 (no residually finite host), O4 (no `VA` host) and the natural
  piecewise-projective exclusion all apply. Every FA subgroup is finite
  (`gl2-q-fa-subgroups-are-finite`).

## Attempts

See `sl2-q-embeds-in-fp-simple-group`, Attempts 1--3. They apply verbatim.

**Rover--Nekrashevych route (2026-09-17, lane gq-rn-varying-degree).**
- `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori` puts all of
  `PGL_2(Q)` in the Röver–Nekrashevych group `V_p(Γ_p)`, where `Γ_p` is the
  self-similar rational Iwahori group acting on `Z_p`. That group is not
  finitely generated.
- The conditional route `psl2-q-fp-simple-via-rational-iwahori-rn-host` then
  needs only `rational-iwahori-group-lies-in-fp-self-similar-group`: a finitely
  presented self-similar overgroup of `Γ_p` in `Aut(T_p)` whose
  Röver–Nekrashevych group has finite abelianization.
- Such an overgroup must be neither contracting nor Möbius. The device does not
  reach `SL_2(Q)`: every homomorphism `SL_2(Q) -> PGL_2(K)` kills `-I`.
- Varying-degree and all-primes trees are dead
  (`aperiodic-tree-almost-automorphism-fg-subgroups-are-rf`).
