# Rank-four associativity: decisive plans for the two-root gate

Lane `w3-strategist-gate`, 2026-09-12. Synthesis of the R-family state into decisive plans for
the rank gate `rank-models-of-el3-satisfy-the-two-root-identities`, i.e. `N_23 N_12 = 0` for every
characteristic-`p` rank model of `EL_3(R)`, `R = L_K(1,2)`, `K` finite. Closing it in either
direction settles `leavitt-el3-rank-models-over-finite-fields-are-trivial` and hence
`non-linear-sofic-group`.

## The opening the finished lanes leave

Two verified facts point the same way.

* `leavitt-isometry-commutators-constrain-el3-rank-models` shows the gate is exactly the assembly
  of an order-two Leavitt (Cuntz) family in a corner `eMe`, that assembling it in a **single Peirce
  corner is circular** (telescoping the four partial isometries there needs the block form, which
  *is* the gate), and that a **non-circular assembly** from data a model with `N_23 N_12 != 0`
  genuinely supplies is "the whole gate."
* `compressors-conjugate-leak-free-root-pairs` and `scalar-two-root-rank-data-cannot-force-the-identity`
  show rank *values* never suffice; **operator identities** are required.

The missing room is a fourth index. And it is free:

> **Khanh--Thanh.** `R^x = GL_n(R) = EL_n(R)` for every `n >= 2`
> (`leavitt-gl-equals-el-and-perfect-unit-group`).

So a rank model `sigma : R^x -> M^x` **is simultaneously a homomorphism `EL_4(R) -> M^x`**, with no
choice or extension involved. `EL_4(R)` has four indices, hence the associativity frame
`[x_12(a), x_23(b)] = x_13(ab)`, `[x_13(ab), x_34(c)] = x_14(abc)`, `x_24(bc) = [x_23(b), x_34(c)]`,
`[x_12(a), x_24(bc)] = x_14(abc)`. The two readings of `x_14(abc)` are an operator associativity
identity that the rank-3 analysis cannot see. This is the non-circular room the isometry lane asked
for: the four partial isometries can be placed on **four distinct root pairs**, so no single Peirce
corner of the EL_3 model has to carry all of them.

## Plan 1 (decisive): the four-index Cuntz assembly

Node `rank-four-isometry-relations-give-corner-cuntz-family` (OPEN), route
`leavitt-el3-triviality-via-rank-four-cuntz-family`.

**Claim to prove.** Let `sigma` be a char-`p` rank model of `R^x`, read as a model of `EL_4(R)`, and
suppose the EL_3 defect `D = N_23 N_12` is nonzero. Then there are an idempotent `e in M` of
positive rank and `S_0, S_1, T_0, T_1 in eMe` with `T_i S_j = delta_ij e` and
`S_0 T_0 + S_1 T_1 = e` -- an order-two Leavitt family in the corner `eMe`.

**Why it closes the gate.** `eMe` is again a rank ultraproduct (Fitting / idempotent lifting, [TR]
Thm D), so a Leavitt family there is a unital homomorphism `R -> eMe`, impossible by
`leavitt-algebra-has-no-unital-rank-model`. Hence `D = 0`; then
`el3-unit-root-matrix-units-iff-two-root-identities` and
`matrix-unit-rank-models-extract-ring-rank-models` give triviality. So every model is trivial:
`leavitt-el3-rank-models-over-finite-fields-are-trivial`.

**Why the verified obstructions miss it.**
* Not rank-values-only: the assembly is an operator construction; the isometry/associativity
  relations, not `rk` alone, produce the `S_i, T_j`. This is the operator input
  `scalar-two-root-rank-data-cannot-force-the-identity` demands.
* Not the circular single-corner extraction: the four isometries sit on four distinct indices, so
  no single Peirce corner carries them; the exact objection of
  `leavitt-isometry-commutators-constrain-el3-rank-models` Section 2 is bypassed.
* Not finite-dimensional/sofic/rank-modelled coefficients: it uses the Leavitt relations
  `t_i s_j = delta_ij`, `s_0 t_0 + s_1 t_1 = 1` directly (a unital Leavitt family has no f.d.
  representation), the input `fd-represented-coefficients-violate-two-root-identities` requires.
* Property (T) and rounding are never invoked, so
  `kazhdan-group-rank-models-admit-no-expander-decomposition` does not bite.

**First lemma (the four-index frame is honest).** In `EL_4(R)`, from `t_i s_j = delta_ij`:
`[x_12(t_i), x_23(s_j)] = x_13(delta_ij)` and `[x_23(t_i), x_34(s_j)] = x_24(delta_ij)`. Set
`A_i = n_12(t_i)`, `B_j = n_23(s_j)`, `A'_i = n_23(t_i)`, `B'_j = n_34(s_j)`. The isometry lane's
relations (off)/(diag) hold on both root pairs. The new content is the **cross frame**: the
associativity readings of `x_14(abc)` give, with `a = t_i`, `c = s_j`, `b` free, a relation tying
the `(1,2)-(2,3)` data to the `(2,3)-(3,4)` data through the common middle index. The first lemma is
to show these force the composite `T_i S_j` (built as the middle-index-`3` corner of the assembled
operator) to equal `delta_ij e`, with `e` the range projection of the `x_14` data and
`rk(e) = rk(D) > 0`. Because the middle index is genuinely shared (not a single Peirce corner of one
root pair), the telescoping that was circular in rank 3 is now a Steinberg identity.

**Where it must be checked hardest.** That `Sum S_i T_i = e` (unitality of the corner) follows from
`s_0 t_0 + s_1 t_1 = 1` through the additive decomposition `1 + N_12 = (1+n_12(e_0))(1+n_12(e_1))`
promoted to the four-index frame; and that `rk(e) = rk(D)`, not merely `>= 0`, so that `D != 0`
gives `e != 0`.

## Plan 2 (independent mechanism): the Heisenberg centre pairing

Node `heisenberg-centre-pairing-constrains-two-root-defect` (OPEN).

In `EL_3` the unipotent radical `U = <x_12, x_23, x_13>` is 2-step nilpotent with centre
`Z = x_13(R)`. For a rank model, `sigma(U)` is nilpotent in `M^x`, `sigma(Z)` central in it, and the
commutator pairing `U/Z x U/Z -> Z`, `(x_12(a), x_23(b)) |-> x_13(ab)`, becomes an `F_p`-bilinear
pairing `beta : R x R -> n_13(R)` with `beta(a,b) = n_13(ab)` and `rk(n_13(R)) <= rk(N_13) <= 1/...`
bounded. The defect `D` is the failure of `beta` to be symmetric-balanced (Proposition 1 defect
factorization: `n_13(ab) - n_12(a) n_23(b) = ` unit-conjugate of `n_23(b) n_12(a)`). Since `R.R = R`
(indeed `1 = s_0 t_0 + s_1 t_1`), `beta` is "onto `R`" while valued in a bounded-rank abelian
square-zero group. Plan: show a bounded-rank bilinear pairing that is onto `R` and has nonzero
defect forces an infinite chain of orthogonal rank pieces (from `R ~= R^2`), contradicting
`rk(N_13) < infinity`, unless `D = 0`. This uses only the EL_3 centre, so it is independent of
Plan 1's fourth index; ranked lower because the bounded-rank-versus-onto tension is not yet a
contradiction.

## Plan 3 (reframing / negative direction): the algebra dichotomy

Node `leavitt-unit-linear-soficity-is-ring-rank-approximability` (OPEN).

`R^x` is `F_p`-linear sofic iff the `F_p`-algebra `R` is **rank-approximately representable**: for
every finite `F ⊂ R` and `eps > 0` there is a unital `phi : R -> M_n(F_p)` (not a homomorphism) with
`rk(phi(ab) - phi(a)phi(b)) < eps` and `rk(phi(x)) > c` for `x in F \ {0}`, respecting the Leavitt
relations up to rank `eps`. Forward: from a linear sofic model of `R^x = EL_2(R)` read off `phi` on
`R` from the `(1,2)` root data. Backward: `GL_n(R) = EL_n(R) = R^x` amplifies `phi` to a group model.
This makes the gate an **algebra**-approximation question and isolates the exact gap from
`leavitt-algebra-has-no-unital-rank-model`: the exact (ultraproduct) Leavitt family is impossible by
stable finiteness, so the whole question is whether the isometries can be *approximately proper*
(`rk(1 - s_i t_i) > 0` in the limit while `rk(t_i s_j - delta_ij) -> 0`). A clean testable target,
and the precise object Plan 1 shows cannot exist if the four-index assembly goes through.

## Ranking

1. **Plan 1** -- the four-index Cuntz assembly. It is the only plan that directly answers the
   isometry lane's "non-circular assembly is the whole gate," and the fourth index is free.
2. **Plan 3** -- the algebra dichotomy. Not a proof by itself, but it converts the gate into a
   sharp, characteristic-uniform algebra-approximation statement that Plan 1 would refute.
3. **Plan 2** -- the centre pairing. Independent and elementary, but the contradiction is not yet
   closed.
