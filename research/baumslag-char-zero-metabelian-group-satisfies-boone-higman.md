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

**OPEN.** Let

```text
B = < a, s, t | [s,t], [a, a^t], a^s = a a^t > ≅ R x| Z^2,   R = Z[x^±1,(1+x)^-1],
```

with `s` and `t` acting by multiplication by `1+x` and `x`. Does `B` embed in a
finitely presented simple group?

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
   *Dies* for every commutative coordinate ring of positive transcendence degree
   (`affine-self-similar-coordinate-rings-are-one-dimensional`), and `R` has
   transcendence degree one.
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
