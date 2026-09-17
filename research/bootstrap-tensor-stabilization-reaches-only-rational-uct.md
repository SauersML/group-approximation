---
rg: 2
id: bootstrap-tensor-stabilization-reaches-only-rational-uct
kind: claim
title: If A tensor C satisfies the UCT for some bootstrap algebra C with nonzero rational K-theory, then A tensor Q does, so tensoring by bootstrap algebras cannot extend the rationally UCT positive case of exact X(1)
distinct_from:
  exact-x1-reduces-to-q-stable-algebras: that proves exact X(1) whenever A tensor C satisfies the UCT for some exact C with a faithful amenable trace; this proves that every bootstrap choice of C reaches no algebra beyond those with A tensor Q satisfying the UCT, so the tensor route adds nothing there.
  coprime-uhf-stabilizations-detect-uct: that splits the UCT of a nuclear algebra over UHF stabilizations; this shows that any bootstrap stabilization with nonzero rational K-theory is dominated by the rationalization, for arbitrary separable A.
  bootstrap-tensoring-cannot-create-qd-trace-positive-class: that is about singular K_0-classes positive on quasidiagonal traces; this is about the UCT of the tensor product itself.
artifacts:
  - research/bootstrap-tensor-stabilization-reaches-only-rational-uct-proof.md
---

**ESTABLISHED (derivation `bootstrap-tensor-stabilization-reaches-only-rational-uct-proof`).**

"Satisfies the UCT" means, for a separable C\*-algebra `D`: `D` is
KK-equivalent to a commutative C\*-algebra. Equivalently (Rosenberg--Schochet,
Meyer--Nest), `KK_*(D, B) = 0` for every separable `B` with `K_*(B) = 0`.
`Q` is the universal UHF algebra.

**Theorem (rationalization dominates bootstrap stabilization).** Let `A` be a
separable C\*-algebra. Let `C` be a separable C\*-algebra in the bootstrap
class with `K_*(C) ⊗ Q ≠ 0`. If `A ⊗ C` satisfies the UCT, then `A ⊗ Q`
satisfies the UCT.

The key point is that `Q` (or `SQ`) is a KK-retract of `C ⊗ Q`. Hence
`A ⊗ Q` (or `A ⊗ SQ`) is a KK-retract of `A ⊗ C ⊗ Q`.

**Corollary (class kill for the tensor route to exact X(1)).** Let `(A, tau)`
be a separable exact algebra with a faithful amenable non-quasidiagonal trace.
Then `A ⊗ C` fails the UCT for every bootstrap algebra `C` with
`K_*(C) ⊗ Q ≠ 0`. This includes every bootstrap `C` with a tracial state,
since a trace sends `[1]`, or the class of a nonzero projection, to a nonzero
real number. So Corollary 3 of `exact-x1-reduces-to-q-stable-algebras`,
applied with a bootstrap `C` (`Z`, any UHF or AF algebra, Cuntz--Krieger
algebras, commutative algebras), proves exact X(1) for no algebra beyond those
with `A ⊗ Q` UCT.

The positive tensor route therefore dies at exactly one step: the UCT of
`A ⊗ C` is never easier to verify than the UCT of `A ⊗ Q`. The route stays
alive only for a non-bootstrap exact `C`, and only if some separable exact
`A` has `A ⊗ Q` non-UCT while `A ⊗ C` is UCT for such a `C`. No example of
this is known.

## Calibration

- **Hypothesis `K_*(C) ⊗ Q ≠ 0` is sharp.**
  - A KK-contractible bootstrap `C` (`O_2`, the cone `C_0((0,1])`) makes
    `A ⊗ C` KK-contractible, hence UCT, for every `A`.
  - But such a `C` breaks the pullback step of the reduction. `O_2` has no
    trace. Cone traces pull nothing back: every amenable trace on a cone is
    already quasidiagonal (`stw10-contractible-algebras-have-qd-amenable-traces`),
    including for non-exact `A` such as `C*(E)`.
  - So the two halves of the tensor route, UCT of the tensor product and
    pullback of quasidiagonality, need opposite properties of `C`.
- **`C = M_{p^∞}`** reproduces the known upward closure of the UCT-support
  filter in `coprime-uhf-stabilizations-detect-uct`.
- **`C = Q`** is the identity case.

Credit: the retract argument is elementary KK-theory. No priority is claimed
for the theorem. The recorded content is its consequence for the X(1) tensor
route.
