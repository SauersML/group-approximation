# Other countable fields, and what transfers to GL_n(Q)

Lane `gq-countable-fields`, 2026-09-17. Stepping stones only; none of these is a printed question.
Root: `gl-n-q-embeds-in-fp-simple-group`.

## 1. Results landed

| Node | Status | Content |
|---|---|---|
| `sl-n-of-infinite-fields-lie-in-no-residually-finite-group` | ESTABLISHED (classical, lane-proved) | `SL_n(K)` has no finite quotients for infinite `K`, so `GL_n(K)` has no residually finite overgroup, in every characteristic |
| `gl-n-over-algebraic-extensions-of-f-p-embed-in-v` | ESTABLISHED (Higman) | `GL_n(K) <= V` for `K` algebraic over `F_p`: the calibration case |
| `char-p-linear-groups-have-no-distorted-cyclic-subgroups` | ESTABLISHED (elementary, lane-proved) | the distortion obstruction O4 never applies in characteristic `p` |
| `char-p-transcendental-gl-n-avoids-v-and-va-for-n-ge-3` | ESTABLISHED (classical inputs) | `SL_3(F_p[t])` has (T), so `V` and `VA` are excluded for `n >= 3` |
| `gl-n-f2t-embeds-in-fp-simple-group` | OPEN | function-field analogue of the root |
| `rational-function-field-embeds-in-binary-leavitt-algebra` | OPEN | `F_2(t)` inside `L_(F_2)(1,2)`; route `gl-n-f2t-bh-via-leavitt-field` |

Q-bar and universal char-0 forms are lane `gq-transfer`'s: `gl-n-qbar-embeds-in-fp-simple-group`,
`countable-char-zero-linear-groups-embed-in-fp-simple-groups`.

## 2. What transfers back to Q

1. **O1 is not about divisibility.** Simplicity of `PSL_n(K)` already forbids residually finite overgroups
   over every infinite field. Consequences:
   - Removing `(Q,+)` does not remove the obstruction. Passing to `SL_n(Q)`, to `PSL_n(Q)`, or to
     characteristic `p` still leaves it.
   - Every route needs a non-residually-finite intermediate group before the final envelope.
2. **O1-type arguments never exclude a finitely presented simple host.** `GL_n(F_p-bar)` has no residually
   finite overgroup yet lies in `V`. Any claimed obstruction to the root must use more than the absence of
   finite quotients. Something infinite-order-specific is needed: distortion, property (T), or divisibility
   of unipotents.
3. **The characteristic-zero-specific difficulty is the unipotents.** `GL_2(Q)` meets O4 (distorted
   unipotents in `BS(1,2)`). `GL_2(F_q(t))` meets no known host obstruction, so `V` and `VA` are still alive
   for it. Everything else is shared by `Q` and `F_q(t)`:
   - infinitely many primes;
   - `GL_n(Z)` versus `GL_n(F_q[t])`;
   - the ascending union over S-integers;
   - simplicity of `PSL_n`;
   - property (T) for `n >= 3`.

   So `GL_2(F_q(t))` is the cleanest test of "all primes at once" constructions (adelic,
   union and germ lanes) with the unipotent issue removed. A construction there tells whether the
   remaining obstacle for `Q` is only the divisibility and distortion of unipotents.
4. **Host shape for Q, in contrast.** For `n >= 2` a `Q`-host must contain exponentially distorted cyclic
   groups (O4). For `n >= 3` it must contain an infinite Kazhdan group. Characteristic `p` keeps the second
   and drops the first.
5. **The Leavitt model.** In characteristic 2 the host `L_(F_2)(1,2)^x` is already finitely presented and
   simple (import), so only the field embedding `F_2(t) -> L_(F_2)(1,2)` is missing. For `Q` both halves are
   missing: a finitely presented ring containing `Q`, and finite presentation and simplicity of its unit
   group. The degree-sign lemma and the point-module test apply verbatim to Leavitt algebras over any
   coefficient field. They are the first checks for lane `gq-ring-leavitt` on any candidate element.

## 3. Minor correction to the root

`GL_1(Q) = Q^x ≅ Z/2 × ⊕_ω Z` already lies in `V`, not only in `VA`. `V` contains `⊕_ω V`, and hence
`Z/2 ⊕ ⊕_ω Z` (survey Theorem 4.3(1)–(2)).

## 4. Sparks (not pursued)

- Does `GL_2(F_q(t))` contain `Z^2 * Z`? If so it is excluded from `V` by Bleak--Salazar-Díaz (survey
  Theorem 4.6(1)). The scalar torus cannot be used, since scalars are central. Try a scalar-free rank-two
  torus and ping-pong on a Bruhat--Tits tree at a place where it acts with elliptic elements.
- Higman's structure theorem for finite-rank abelian subgroups of `V` (survey proof of Theorem 4.4),
  tested on the tori of `GL_2(F_q(t))`.
