---
rg: 2
id: exactly-matricial-rings-are-lef-rings
kind: claim
title: A ring that embeds unitally in an ultraproduct of matrix algebras over fields is locally embeddable into finite rings
distinct_from:
  exactly-matricial-rings-have-lef-general-linear-groups: that passes from exact matriciality to LEF of the general linear groups through Malcev's theorem; this passes from exact matriciality to LEF of the ring itself, by residual finiteness of finitely generated commutative rings.
  lef-simple-rings-are-not-finitely-presented: that shows finitely presented simple LEF rings are finite; this supplies the LEF input from exact matriciality, so exactly matricial finitely presented infinite simple rings do not exist.
---

**ESTABLISHED (unreviewed; proof in `exactly-matricial-rings-are-lef-rings-proof`).**

Let `R` be a unital ring with an injective unital ring homomorphism `R -> prod_omega M_(d_k)(F_k)`, the
algebraic ultraproduct over commutative fields `F_k`. Then `R` is LEF, in the sense of
`lef-simple-rings-are-not-finitely-presented`: every finite window of sums and products embeds exactly and
injectively in a finite unital ring.

**Consequence.** Combine this with `lef-simple-rings-are-not-finitely-presented`. A finitely presented
infinite simple unital ring has no unital embedding in any ultraproduct of matrix algebras over fields, of
any characteristics.
