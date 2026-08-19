# The four stubborn atlas relators do not kill the phase locally

Date: 2026-08-11

> **Status.** This local certificate is retained as the first exact
> obstruction.  It is superseded globally by
> `FALSE_ATLAS_DUAL_NUMBER_CENTRAL_QUOTIENT.md`, which extends to both full
> `A_8` charts and kills all 24 certified zero classes simultaneously.

## Result

The phase-preserving multi-relator search identified certified-zero boundary
classes `70`, `86`, `90`, and `91` as the persistent worst package near the
exact class-`11` phase.  This note determines the exact group-theoretic scope
of that observation.

All five words lie in a subgroup

\[
S_4*S_4\ \subseteq\ A_8*A_8.
\]

Let (w_{70},w_{86},w_{90},w_{91}) be the four zero words and let (r) be
class `11`.  Then

\[
r\notin
\left\langle\!\left\langle
w_{70},w_{86},w_{90},w_{91}
\right\rangle\!\right\rangle_{S_4*S_4}.             \tag{1}
\]

More precisely, the quotient of (S_4*S_4) by the four displayed relators
has a finite quotient of order (168) in which (r) is a nonidentity
involution.  The image is the standard degree-eight permutation model of
(operatorname{PSL}(2,7)).

Thus the numerical four-class tradeoff is not a consequence of those four
relations and the local finite-group laws alone.  Any exact obstruction must
use more of the 24 certified-zero classes, the requirement that the two local
(S_4)'s extend to the full (A_8) charts, or a genuinely analytic feature
of the selected representation.

## The local presentation

For each factor choose generators (s_i,t_i) satisfying

\[
s_i^2=t_i^3=(s_it_i)^4=1.                           \tag{2}
\]

Exact enumeration over (mathbb F _2) gives order (24) for each generated
matrix group.  Since `(2)` presents the spherical triangle group
(Delta(2,3,4)\cong S_4), these are the asserted local (S_4)'s.  The
matrix keys used by the certificate are

| generator | row-major (mathbb F _2) matrix key |
|---|---|
| (s_1) | `01000000000100000001010000000001` |
| (t_1) | `01010100000101000001000000000001` |
| (s_2) | `01000000000101000000010000000001` |
| (t_2) | `01000000010101000001000000000001` |

The script reconstructs the complete 234-word boundary directly and factors
every matrix syllable of the five selected words in these generators.  No
stored transcription of the atlas words is trusted.

## Finite certificate

Define a homomorphism from the free product presentation to (S_8) by

\[
\begin{aligned}
s_1&\mapsto(1\,8)(2\,7)(3\,5)(4\,6),\\
t_1&\mapsto(2\,4\,5)(3\,8\,6),\\
s_2&\mapsto(1\,2)(3\,4)(5\,8)(6\,7),\\
t_2&\mapsto(3\,5\,7)(4\,6\,8).
\end{aligned}                                       \tag{3}
\]

Direct permutation multiplication verifies `(2)` and

\[
w_{70},w_{86},w_{90},w_{91}\mapsto 1,
\qquad
r\mapsto(1\,3)(2\,8)(4\,6)(5\,7).                 \tag{4}
\]

The four permutations in `(3)` generate a group of order (168).  Equation
`(4)` proves `(1)`: membership in the normal closure would force (r) to
vanish under every homomorphism which kills the four normal generators.

## Scope

This is a rigorous no-go result for an attempted *local* proof that the four
persistent optimizer classes force the phase to vanish.  It is not a
survival proof in the full Leavitt relation module.  The finite certificate
does not extend either local (S_4) map to a homomorphism from its ambient
(A_8): a nontrivial homomorphism from simple (A_8) into a group of order
(168) is impossible.  It therefore does not satisfy the other 20
certified-zero relations or the full infinite relation package.

The useful next target is consequently the extension obstruction itself:
combine enough certified-zero words outside this (S_4*S_4) slice to force
the ambient (A_8) charts, rather than seeking an inequality in the four
local words alone.

## Reproduction

The self-contained exact certificate is

```text
python3 experiments/atlas_stubborn_s4_certificate.py
```

It checks the two local orders, reconstructs and translates the original
atlas boundary words, verifies all four identities and the nontrivial phase,
and enumerates the order-168 image.  The independent discovery calculation
is

```text
/Users/user/.pixi/bin/gap -q \
  experiments/atlas_stubborn_s4_quotient.g
```

GAP simplifies the finitely presented quotient and searches standard finite
targets; it returns 32 epimorphisms onto (operatorname{PSL}(2,7)) under
which the phase survives.  The Python certificate is the durable proof and
does not require GAP.
