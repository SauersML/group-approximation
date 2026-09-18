---
rg: 2
id: integral-counting-group-avoids-leavitt-linear-simple-hosts
kind: claim
title: The C_=P-complete integral Leavitt group Γ_Z has no simple host among Leavitt-linear groups over Z[1/M], and rational or finite-field ones would force C_=P ⊆ ∀·Mod_pP
distinct_from:
  leavitt-tensor-unit-word-problems-have-one-counting-quantifier: that bounds word problems of Leavitt-linear groups and constructs Γ_Z; this shows why none of those groups, nor their central quotients, can be a simple host of Γ_Z.
  leavitt-scalar-commutators-block-fp-central-quotients: that is the Schur-multiplier obstruction for groups containing L_K(1,d)^x over an infinite field; this uses it as one of four obstructions, specialized to hosts of Γ_Z.
requires:
  - leavitt-tensor-unit-word-problems-have-one-counting-quantifier
  - leavitt-scalar-commutators-block-fp-central-quotients
---

**ESTABLISHED** (route `integral-counting-group-hosts-proof`; lane proof by bh-free-26,
elementary, not independently reviewed). This is a kill for one family of hosts, with
conditional parts. It does not settle whether `Γ_Z` has a finitely presented simple overgroup.

## Setting

`Γ_Z ≤ (L_Z(1,2)^(⊗2))^x` is the finitely generated group of
`leavitt-tensor-unit-word-problems-have-one-counting-quantifier` (part 3). Its word problem is
`C_=P`-complete. Boone--Higman predicts a finitely presented simple overgroup, which would be a
finitely presented simple group with `C_=P`-hard word problem. Below,
`A_K = L_K(1,n_1) ⊗ ... ⊗ L_K(1,n_k)`.

## Statement

1. **Integral hosts are never simple.** Let `M >= 1`, `A = L(1,2)^(⊗2)`, `U_M = (A_(Z[1/M]))^x`,
   and fix a prime `p ∤ M`.
   - (i) No subgroup `G` with `Γ_Z ≤ G ≤ U_M` is simple. Reduction mod `p` has a kernel on
     `G` that contains `1 + p a_c a_d^* ∈ Γ_Z` but not `1 + a_c a_d^* ∈ Γ_Z`.
   - (ii) No central quotient of `U_M` or of `[U_M, U_M]` is simple.

   This holds whatever the `K`-theory of `A_(Z[1/M])`. The Khanh and Ara--Cortiñas inputs
   used for `P_p` need simplicity of the coefficient algebra, and that fails over `Z[1/M]`.
   (Within `Γ_Z` itself the elements `1 + a_c X a_d^*` are central, so (ii) is stated only
   for `U_M` and its derived group.)
2. **Rational hosts containing `L_Q(1,2)^x` have no finitely presented central quotient.** Let
   `R` be a `Q`-algebra containing a Leavitt pair, and `L_Q(1,2)^x ≤ H ≤ R^x`. Then no `H/C`
   with `Q^x ≤ C ≤ Z(H)` is finitely presented
   (`leavitt-scalar-commutators-block-fp-central-quotients`, part 1). This covers
   `(L_Q(1,2)^(⊗2))^x / Q^x`, the rational version of the candidate host.
3. **Simple rational Leavitt-linear groups reduce mod p.** Let `G ≤ GL_N(A_Q)` be a nontrivial
   finitely generated simple group. Then reduction mod some prime `p` embeds `G` in
   `GL_N(A_(F_p))`. Consequently:
   - (a) `G` contains no element `1 + X ≠ 1` with `X^2 = 0`. In particular, `G` does not
     contain `Γ_Z` in its standard position, since `Γ_Z ∋ 1 + a_c a_e^*`.
   - (b) `WP(G) ∈ ∀·Mod_pP`. So if `Γ_Z` embeds abstractly in `G`, then
     `C_=P ⊆ ∀·Mod_pP`.
4. **Finite-field hosts.** If `Γ_Z` embeds in any finitely generated subgroup of `GL_N(A_(F_q))`,
   then `C_=P ⊆ ∀·Mod_pP` for `p = char F_q`.
5. **Affine actors over `Z[1/M]` are not of type (A).** For `Γ_Z ≤ G ≤ (A_(Z[1/M]))^x`, the affine
   action of `C(C^k, Z[1/M]) ⋊ G` on `C(C^k, Z[1/M])` has infinitely many orbits on pairs. So the
   affine route that gives permutational Boone--Higman for `L_(F_2)(1,2)^x`
   (`binary-leavitt-unit-group-satisfies-pbh`) does not give a type (A) actor for `Γ_Z`, and
   no twisted Brin--Thompson group over that actor is available.

## Reading

The inclusion `C_=P ⊆ ∀·Mod_pP` fails relative to an oracle. With oracle `A`, "exactly half of
the strings of length `n` lie in `A`" is in `C_=P^A`. Placing it in `(∀·Mod_pP)^A` would
compute exact threshold by quasi-polynomial `AC^0[p]` circuits, contrary to
Razborov--Smolensky. So a proof that `Γ_Z` embeds in a finitely generated simple group linear
over a rational or finite-field Leavitt tensor algebra would prove an inclusion of counting
classes that fails relative to an oracle.

Together, parts 1--5 say that **the first finitely presented simple group with `C_=P`-hard
word problem, if Boone--Higman supplies one, is not built from finite-depth Leavitt linear
algebra**, unconditionally for parts 1, 2, 3(a) and 5, and unless `C_=P ⊆ ∀·Mod_pP` for
parts 3(b) and 4:
- over `Z[1/M]` there are congruence quotients;
- over `Q` the scalars block finite presentation;
- simple subgroups reduce to one prime, and there the counts are mod `p`.

The exact counting has to come from somewhere other than a coefficient ring. Possible
sources:
- a non-linear type (A) action of an overgroup of `Γ_Z`;
- a family of the groups `P_p` of `leavitt-square-units-mod-p-complete-word-problem`, embedded
  uniformly (generators given by words of length polynomial in `p`) and generating their
  direct product inside one finitely presented simple group. This suffices by the Chinese
  remainder theorem: counts below `2^q` agree iff they agree mod each of the first `O(q)`
  primes, and in a direct product a product of tests is trivial iff each test is.

## Lesson for general BH

**Characteristic-zero linear hosts face a dichotomy.** The proof of part 3 uses only a
multiplicative `Z`-form that is a free `Z`-module spanning the algebra. Leavitt path,
Weyl, group and Nekrashevych algebras over `Q` all have one. For such algebras:
- a finitely generated simple subgroup of `GL_N(A_Q)` reduces injectively mod some prime;
- it therefore has no nontrivial square-zero unipotent, and in effect it has positive
  characteristic;
- `Z[1/M]`-forms carry congruence quotients;
- `Q`-algebras containing `L_Q(1,2)` have scalar commutators that block finitely presented
  central quotients.

So an input whose infinite-order square-zero unipotents are placed standardly cannot sit in
any simple host of this kind. Such inputs include `SL_3(Z)` blocks, the unipotents of
`GL_n(Q)`, and the counters of `Γ_Z`. A host must realize them as non-unipotent elements, or
use a ring such as the Leavitt resolvent ring, which contains `Q` internally rather than
through a `Z`-form. This is a design constraint for `gl-n-q-embeds-in-fp-simple-group`.
