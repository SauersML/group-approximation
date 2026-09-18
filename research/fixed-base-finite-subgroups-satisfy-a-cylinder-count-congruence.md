---
rg: 2
id: fixed-base-finite-subgroups-satisfy-a-cylinder-count-congruence
kind: claim
title: In a fixed-base shell enumeration over V_(h,r)(<a>), every finite subgroup C of the input satisfies gcd(|C|, h-1) | r, and the level-one digit rotation turns the shift into a local odometer
distinct_from:
  fixed-base-shell-inputs-embed-in-odometer-rn-groups: that excludes infinite Kazhdan subgroups from fixed-base inputs; this is an arithmetic constraint on their FINITE subgroups, tying the base h and the number of roots r to the orders of torsion elements.
  finite-index-odometer-near-shift-groups-pass-the-germ-gate: that says finite index of R_nu in B passes the germ gate; this records two design tools for reaching finite index, a necessary congruence and a seed mechanism.
  a5-free-product-has-simple-arithmetic-shell-envelope: that is one explicit fixed-base enumeration of A_5*A_5 with h = 59, r = 2; its parameters satisfy the congruence here (gcd(60, 58) = 2 divides 2), which serves as a calibration.
artifacts: []
---

**ESTABLISHED** by `fixed-base-finite-subgroups-cylinder-count-proof` (lane proof,
elementary, not independently reviewed; no novelty claimed).

## Setting

`B = V_(h,r)(<a>)` acting on `N` by near permutations as in
`odometer-prefix-groups-have-fg-index-kernels`, on `X` = `r` copies of the `h`-adic Cantor
set, with `N` dense in `X`. `P`, `S`, `nu` satisfy the fixed-base hypothesis of
`fixed-base-shell-inputs-embed-in-odometer-rn-groups`, so `lambda(P) <= B` near infinity.

## Statement

1. **Fixed sets of torsion.** If `g in B` has finite order, its fixed-point set in `X` is
   clopen. So if `g` fixes no point of `N`, it fixes no point of `X`.
2. **Cylinder-count congruence.** Every finite subgroup `C` of `P` satisfies
   `gcd(|C|, h-1) | r`. In particular, if `h - 1` is even then `P` has no element of order
   2 unless `r` is even.
3. **Digit-rotation seed.** Take `r = 1` and let `v` be the level-one digit rotation
   `d + h y -> (d+1 mod h) + h y`. Then `v` lies in `V_(h,1)`, acts freely on `N`, and
   `s v^-1 = a_[0]` is the local odometer on the cylinder of lowest digit `0`
   (`h y -> h(y+1)`, identity on the other residue classes mod `h`). So any enumeration with
   `v in lambda(P)`, for example one in which a factor `C_h` of a free product acts by `v`,
   has all level-one local odometers `a_[d] = v^d a_[0] v^-d` inside `R_nu`.

## Calibration

The arithmetic enumeration of `A_5*A_5` has `h = 59` and `r = 2`, and `A_5` has order 60:
`gcd(60, 58) = 2` divides `2`, as item 2 requires. With `r = 1` that base would be
impossible.

## Use

Item 2 prunes the parameter search for a fixed-base enumeration with `R_nu` of finite
index in `B`. Item 3 is a seed for that search: once `R_nu` contains the local odometers
of one level, its conjugates by level-changing elements of `lambda(P)` supply local
odometers on deeper cylinders, and quotients `a_[w] a_[w']^-1` supply finitary tree
automorphisms. Whether a second, level-changing free factor can complete this to a
finite-index subgroup of `B` is open.
