---
rg: 2
id: swap-twist-centralizer-is-the-congruence-core
kind: claim
title: The centralizer in the S-arithmetic group of the swap twist word is exactly the depth-one congruence core
distinct_from:
  hnn-stable-letter-rounds-to-finite-order: that records the descent direction informally in its attempts, with the centralizer left as "the exact centraliser"; this computes it -- the elliptic-hyperbolic axis argument gives exactly the depth-one congruence core, no more -- turning the descent's amalgam base from a guess into a theorem.
  atkin-lehner-twist-of-vertex-orbit-representation-is-disjoint: that computes the total-variation asymmetry of congruence data under the Atkin--Lehner twist at depth k; this is a group-theoretic computation in the swap extension whose answer is the same tower's first floor, the subgroup the twist word centralizes.
---

Work in `E = Gamma *_Lambda (Lambda x <s>)` for any pair with
`Lambda <= Gamma` and an element `h in Gamma - Lambda`; the instance of
record is `Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/p])`, `h = diag(p,1,1/p)`,
where

```text
C_0 = Lambda cap h Lambda h^(-1)
    = { g in SL_3(Z) : p | g_21, p | g_32, p^2 | g_31 },
```

a finite-index congruence-type subgroup (depth one of the Atkin--Lehner
tower), still co-dense in `Gamma` since it contains the principal
congruence subgroup of level `p^2` and coprime-level quotients of
`Gamma` are full by strong approximation.

**THEOREM (established here; proof in
`swap-twist-centralizer-proof`).**  Let `z = s (h s h^(-1))`.  Then

```text
C_Gamma(z) = C_0.                                            (ZC1)
```

Moreover `z` is hyperbolic on the Bass--Serre tree of `E` with
translation length `4`, its axis passes through the vertices fixed by
`Gamma`, by `Lambda x <s>`, and by `h (Lambda x <s>) h^(-1)`, and `s` and
`h s h^(-1)` are free involutions generating an infinite dihedral group.

**Why it matters.**  `z` commutes with `C_0` and is Haar-distributed in
every canonical model of `E` (free product of two centered involutions).
`(ZC1)` says the largest subgroup of `Gamma` that `z` centralizes is
exactly `C_0` -- but centralizing is not the whole story: by
`weyl-reverser-blocks-naive-swap-twist-descent` the normalizer of `<z>`
in `Gamma` is strictly larger,

```text
N_Gamma(<z>) = C_0  cup  x_0 C_0,      x_0 = h w_13,  x_0^2 = e,
x_0 z x_0 = z^(-1),
```

so `z` can never be an amalgamated-free HNN letter over `C_0` relative
to `Gamma`: the descent of an involution enemy to a Haar enemy over the
deeper pair happens only in the DIHEDRAL form, with the inverting
involution `x_0` sitting inside `Gamma` itself.  Iterating the twist
with `h^k` reaches the depth-`k` cores `Lambda cap h^k Lambda h^(-k)`,
the tower whose genuine-representation asymmetry is quantified by the
Atkin--Lehner disjointness theorem -- and each floor carries its own
Weyl reverser `h^k w_13`.
