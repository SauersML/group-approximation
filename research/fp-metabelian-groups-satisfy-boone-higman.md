---
rg: 2
id: fp-metabelian-groups-satisfy-boone-higman
kind: claim
title: Every finitely presented metabelian group embeds in a finitely presented simple group
root: true
distinct_from:
  positive-char-surface-linear-groups-satisfy-boone-higman: that is a linear class in one positive characteristic, and it contains Baumslag's metabelian groups over F_p; this is the whole finitely presented metabelian class, whose members mix characteristics.
  char-zero-linear-groups-satisfy-boone-higman: that is the characteristic-zero linear class; this is the metabelian class, which is not linear over any single field in general and needs a product step.
  global-field-soluble-linear-products-satisfy-boone-higman: that is the established part, soluble groups linear over finite products of number fields and positive-characteristic fields of transcendence degree at most one; this is every finitely presented metabelian group.
  baumslag-char-zero-metabelian-group-satisfies-boone-higman: that is the first uncovered one-factor case, Baumslag's torsion-free group over Z[x^±1,(1+x)^-1]; this is the whole finitely presented metabelian class.
  no-uniform-metabelian-higman-compiler: that rules out a uniform effective metabelian Higman compiler; this is the Boone--Higman embedding question for metabelian groups, with no effectivity requirement.
  boone-higman-conjecture: that is the conjecture for all decidable finitely generated groups; this is its named metabelian case.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**OPEN.** Every finitely presented metabelian group embeds in a finitely
presented simple group.

*Marked `root` because it is a named open class:* item (7) of Problem 5.3 in
Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, still open after their
Remark 5.4. Their footnote 9, verbatim from the extracted PDF text: "By a
theorem of Baumslag and Remeslennikov, every finitely generated metabelian group
embeds into a finitely presented one [4, 94]. Such groups have solvable word
problem [5]". Since Boone--Higman passes to subgroups, this claim is equivalent
to Boone--Higman for every finitely generated metabelian group.

## Exact reduction

By `fg-metabelian-groups-embed-in-products-of-coprimary-quotients` (Wehrfritz
1975, Corollary 1.2, with a direct primary-decomposition proof), a finitely
generated metabelian `G` embeds in `G_0 x G_(p_1) x ... x G_(p_s)`. The primes
`p_j` are distinct, and each `G_c` is a metabelian quotient of `G` that is linear
over one field of characteristic `c`. Products of such groups are finitely
generated metabelian. So the claim is **equivalent** to:

- **(P)** Boone--Higman for every finite product of finitely generated metabelian
  linear groups over fields of pairwise distinct characteristics.

Its one-factor cases are:
- **(M0):** Boone--Higman for finitely generated metabelian linear groups in
  characteristic zero;
- **(Mp):** the same in characteristic `p`, for each prime `p`.

**The mixing is essential.** `(Z wr Z) x (Z/p wr Z)` is linear over no field: the
first factor is not linear in positive characteristic, and the second is linear
only in characteristic `p`. See the artifact, §2.

Route `fp-metabelian-bh-via-linear-factors-and-products` derives the claim from:
- the decomposition;
- the two linear roots;
- `boone-higman-closed-under-finite-direct-products`.

## What is established

`global-field-soluble-linear-products-satisfy-boone-higman` settles every
finitely generated soluble group that embeds in a finite product of linear groups
over number fields and positive-characteristic fields of transcendence degree at
most one. It puts each factor, up to finite index, inside a finitely presented
self-similar group, and the product inside the permutational class `B_A`.

It covers:
- **Baumslag's metabelian groups** `F_p[x^±1, (1+x)^-1] x| Z^2`. These were
  already covered in substance by Kochloukova--Sidki, arXiv:1710.04745,
  Theorem A, together with Zaremsky's Theorem 1.1.
- **Mixed products.** Their products over different primes, and their products
  with S-arithmetic groups such as `Z[1/m] x| Z^k`.

## What is missing, precisely

1. **Characteristic zero, positive transcendence degree.** *Settled for one factor
   (2026-09-12).*
   - **The root.** `char-zero-linear-groups-satisfy-boone-higman` is ESTABLISHED
     through `char-zero-linear-bh-via-polynomial-s-integer-hosts`, so (M0) holds.
     This rests on `polynomial-linear-groups-satisfy-boone-higman`~~, whose review
     is pending (lane `bh-poly-linear-review`)~~. *Reviewed (lane
     `bh-poly-linear-review`, 2026-09-12):* that claim stands, with one corrected
     step.
   - *First case:* Baumslag's torsion-free group `Z[x^±1, (1+x)^-1] x| Z^2`,
     linear over `Q(x)`. It is now established as
     `baumslag-char-zero-metabelian-group-satisfies-boone-higman`, through
     `GL_14(Z[s'])`.
   - *The product step cannot help it.* It is a one-factor case.
   - *Excluded hosts,* which still stand. The envelope comes instead from
     parameter-coordinate affine hosts:
     - `B` itself as a self-similar input (`baumslag-char-zero-metabelian-group-is-not-self-similar`);
     - affine self-similar hosts (`affine-self-similar-coordinate-rings-are-one-dimensional`);
     - Leavitt unit groups over characteristic-zero rings, which are not simple
       (`char-zero-leavitt-unit-groups-have-congruence-kernels`);
     - unit groups modulo central units of `Q`-algebras with bounded
       divisibility, whenever the embedding keeps a translation unipotent
       (`char-zero-algebra-unit-hosts-exclude-unipotents`).
2. **Positive characteristic, transcendence degree at least two.**
   - Degree two has envelopes (`positive-char-surface-linear-groups-satisfy-boone-higman`),
     but they are not known to be highly transitive, MIF, or in `B_A`. So products
     with other characteristics are not covered.
   - Every degree now has envelopes. `positive-char-linear-groups-satisfy-boone-higman`
     is established, according to `cairn why`, through Leavitt projective
     elementary hosts. Those envelopes are not known to lie in `B_A` either.
3. **The product step** outside `B_A` (`boone-higman-closed-under-finite-direct-products`).

**Route status (2026-09-12).** `cairn why` on MSI reports three inputs of
`fp-metabelian-bh-via-linear-factors-and-products` as established:
- the decomposition;
- `positive-char-linear-groups-satisfy-boone-higman`;
- the characteristic-zero root~~, which rests on the pending review~~. The review
  is complete (2026-09-12) and the root stands.

Its one remaining input is `boone-higman-closed-under-finite-direct-products`,
which is OPEN.

## Attempts

1. **Linear factors and products** (this node's route). *Stops* at the product
   step alone (see route status above).
2. **Global-field factors through finitely presented self-similar hosts.**
   *Established* (`global-field-soluble-linear-products-satisfy-boone-higman`).
   - *Stops at transcendence degree one in positive characteristic.* Zaremsky's
     Example 4.7 criterion needs a principal ideal `xR` of finite index with
     `∩ x^k R = 0`. If `R` is a finitely generated commutative domain and `R/xR`
     is finite for a nonzero nonunit `x`, then `R` has Krull dimension at most one.
   - *Stops at degree zero in characteristic zero,* by
     `affine-self-similar-coordinate-rings-are-one-dimensional`.
3. **Leavitt tensor envelopes in positive characteristic.** They give
   Boone--Higman for transcendence degree at most two, one characteristic at a
   time. *Stops* at the product step. The natural test is whether
   `(L_p ⊗ L_p)^x / F_p^x` is MIF, or embeds in a finitely presented simple MIF
   group, and it is untested (`fp-simple-groups-embed-in-fp-simple-mif-groups`,
   Attempts).
