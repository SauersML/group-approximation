---
rg: 2
id: baumslag-char-zero-metabelian-group-satisfies-boone-higman
kind: claim
title: Baumslag's torsion-free finitely presented metabelian group Z[x^±1,(1+x)^-1] x| Z^2 embeds in a finitely presented simple group
distinct_from:
  char-zero-linear-groups-satisfy-boone-higman: that is Boone--Higman for every finitely generated linear group in characteristic zero; this is one finitely presented metabelian case of transcendence degree one, the first case of BBMZ Problem 5.3(7) not covered by positive-characteristic or number-field hosts.
  positive-char-surface-linear-groups-satisfy-boone-higman: that covers Baumslag's group with the extra relation a^p, which is linear in characteristic p; this is the torsion-free version, which is linear over no field of positive characteristic.
artifacts:
  - research/artifacts/bh-baumslag-char0-metabelian-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`baumslag-char-zero-bh-via-char-zero-linear-groups`, now that the root
`char-zero-linear-groups-satisfy-boone-higman` is established. This rests on
`polynomial-linear-groups-satisfy-boone-higman`~~, whose independent review is still
pending (lane `bh-poly-linear-review`)~~.
*Reviewed (lane `bh-poly-linear-review`, 2026-09-12).* The status stands.
- The review checked the chain below, including the Nagata relation, and
  corrected one step of the polynomial theorem.
- See `research/artifacts/review-bh-polynomial-linear-2026-09-12.md`.

**Statement.** Let

```text
B = < a, s, t | [s,t], [a, a^t], a^s = a a^t > ≅ R x| Z^2,   R = Z[x^±1,(1+x)^-1],
```

with `s` and `t` acting by multiplication by `1+x` and `x`. Then `B` embeds in a
finitely presented simple group.

**The chain, explicitly** (lane `bh-char0-linear-reduction`, 2026-09-12).
- **Affine.** `B <= Aff(Q(x)) <= GL_2(Q(x))` by `r -> [[1,r],[0,1]]`,
  `s -> diag(1+x,1)`, `t -> diag(x,1)`.
  - Conjugation `g [[1,r],[0,1]] g^-1` multiplies `r` by `1+x` and by `x`. So
    `a^s = a a^t` holds when `a^g` is read as the action of `g`, as in the
    presentation.
  - The image lies in `GL_2(R)`.
- **Coordinates.** `R = Z[x][1/f]` with `f = x + x^2`. Put `u = 1/f` and
  `s' = x - u^3`, the Nagata substitution with weight `D = 3`. Then
  `u^7 + (1+2s')u^4 + (s'+s'^2)u - 1 = 0` is monic over `Z[s']`, and
  `[Q(x) : Q(s')] = 7`, the degree of `s'` as a rational function of `x`.
  - So `R = Z[s'][u]` is free over `Z[s']` with basis `1, u, ..., u^6`.
  - It follows that `B <= GL_2(R) <= GL_14(Z[s'])`.
- **Host.** Apply `polynomial-linear-groups-satisfy-boone-higman` with `k = 1`,
  `m = 1` and `N = 14`. The host is `Z[s']^28 x| E_28(Z[s'])`.

**Why this case.** Problem 5.3(7) of Belk--Bleak--Matucci--Zaremsky
(arXiv:2306.16356) asks for Boone--Higman for finitely presented metabelian
groups.
- **Covered cases.** Metabelian groups linear over number fields or over
  one-variable function fields in characteristic `p` are reached through
  finitely presented self-similar affine hosts.
- **B is the smallest uncovered case.** It is finitely presented (Baumslag
  1972) and residually finite. It is linear over `Q(x)` of transcendence degree
  one, via `r -> [[1,r],[0,1]]`, `s -> diag(1+x,1)`, `t -> diag(x,1)`, and over
  no field of positive characteristic.
- **Subgroups already covered.** `Z wr Z <= B` satisfies Boone--Higman, since
  it lies in Thompson's `F`.

## Attempts

1. **Zaremsky's Theorem 1.1 applied to `B` itself.** `B` is finitely presented,
   so a faithful state-closed action would settle it.
   *Dies:* `baumslag-char-zero-metabelian-group-is-not-self-similar`. `B` has no
   faithful state-closed action on any regular rooted tree, transitive or not.
   *Not excluded:* a larger finitely presented self-similar overgroup of `B`.
2. **Affine digit self-similar hosts** (Zaremsky's Example 4.7).
   - *Dies for commutative coordinate rings* of positive transcendence degree
     (`affine-self-similar-coordinate-rings-are-one-dimensional`), and `R` has
     transcendence degree one.
   - *Dies for virtually abelian linear parts, whatever the translations.* Take a
     finitely generated digit-affine self-similar group over `O`, for a
     uniformizer with `pi^e = p`. If its linear parts form a virtually abelian
     group, its translation subgroup has finite rank. That subgroup would contain
     a nonzero ideal of `R`, which has infinite rank
     (`digit-affine-hosts-with-abelian-linear-parts-have-finite-rank`).
   - *Not excluded:* overgroups whose linear parts are not virtually abelian, such as
     `R'^n x| GL_n(R')` with `n >= 2`; other uniformizers and non-scalar
     contractions; self-similar hosts that are not affine.
3. **Algebra unit-group hosts through matrices.**
   *Dies* by `char-zero-algebra-unit-hosts-exclude-unipotents`. Any such host
   containing `B` through matrices over a characteristic-zero algebra contains
   the unipotent `a`.
4. **Characteristic-`p` hosts and mixed-characteristic products.**
   *Dies for `B`.*
   - **No positive characteristic.** A finitely generated solvable linear group
     in characteristic `p` is virtually (unipotent `p`-group)-by-abelian. `B` is
     torsion-free and not virtually abelian, so it is linear in no positive
     characteristic.
   - **Products must be faithful on one factor.** Every nontrivial normal subgroup
     of `B` meets `R` in a nonzero ideal (Step 1.2 of
     `baumslag-char-zero-metabelian-not-self-similar-proof`), and finitely many
     nonzero ideals of a domain intersect nontrivially. So an embedding of `B`
     into a finite product is faithful on one factor, and the product step of
     5.3(7) gives nothing for `B`.
5. **Bux--Llosa Isenrich--Wu Theorem B through the `p`-adic tree.**
   - **The action.** Send `x` to a transcendental `xi in Q_p` with
     `v_p(xi) = 1`. Then `B <= PGL_2(Q_p)` acts faithfully and cocompactly on the
     Bruhat--Tits tree, since `R` is dense in `Q_p` and `t` has translation
     length one.
   - *Dies for this action:* the edge stabilizer is `(R ∩ pZ_p) x| <1+xi>`. It is
     not finitely generated, because `p^(k+1) xi^-k in R ∩ pZ_p` for every `k`,
     while a finitely generated `Z[(1+xi)^±1]`-submodule has bounded
     `xi`-denominators.
   - **Other valuations give nothing new.** `v_p(xi) = 0` makes `B` fix a vertex
     and the action is not cocompact. The remaining cases are anharmonic images
     of this one.
   - *Not done:* a finitely generated overgroup such as
     `Z[1/p, x^±1,(1+x)^-1] x| <x, 1+x, p>`, acting on the same tree, whose edge
     stabilizers are finitely presented. Its edge-stabilizer module still has to
     be tested against the Bieri--Strebel tameness criterion. See the artifact,
     Section 4.
6. **Twisted Brin--Thompson hosts (type (A) actions).**
   *Not attempted here;* lane `bh-type-a-actions` owns that route. The affine
   actions of `B` have infinitely many orbits of pairs, because
   `R \ 0` splits into infinitely many unit classes.
7. **Lamplighter hosts** (M. R. Almeida and two coauthors, arXiv:2609.01868v1,
   1 September 2026). Abstract, read 2026-09-12. When `G` is a non-torsion
   contracting self-similar group, they show that under certain conditions
   `V_m(Z^d wr_X G)` is finitely presented and virtually simple. "Moreover, we
   prove that Z^d ≀_X G embeds into a finitely presented simple group."
   - *For `B` this reduces to `G`.* Suppose `B <= A wr_X G` with `A` finitely
     generated abelian. If the composite `B -> G` is not injective, its kernel
     meets `R` in a nonzero ideal `I` (Attempt 4). `I` is torsion-free, so it
     embeds as a `Z[s^±1,t^±1]`-module in the free part `Z[X]^d` of the base.
   - *No room in the base.* Every nonzero element of `I` has annihilator
     `P = (s - 1 - t)`, which is prime. So `P` is an associated prime of some
     orbit module `Z[Z^2/H]`, and it contains `h - 1` for every `h in H`. Since
     `(1+x)^a x^b = 1` forces `a = b = 0`, we get `H = 1`. But `Z[Z^2]` is a
     domain, and its only associated prime is `0`.
   - *Consequence.* This route needs `B` inside the contracting self-similar
     group `G` itself.
