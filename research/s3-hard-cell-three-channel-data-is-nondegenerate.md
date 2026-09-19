---
rg: 2
id: s3-hard-cell-three-channel-data-is-nondegenerate
kind: claim
title: The atlas S3 hard cell has three exact nondegenerate channel transforms
distinct_from:
  regular-subgroup-branching-is-hall-balanced: that proves bare regular-type incidence never has a Hall deficit; this retains coupled channel maps and proves three exact transforms are invertible.
  regular-chart-wedderburn-coefficient-compiler: that gives a general coefficient path-sum language for every finite group; this computes the specific three-dimensional local data for the S3/S4 hard cell.
  atlas-hard-packet-s3-channel-decoder: that asks whether the literal full hard packet exposes an invertible projected relation system; this claim establishes only the universal finite representation-theoretic matrices available to such a system.
  s3-standard-operator-channel-has-fivefold-reduced-gauge: that counts five standard-channel sources for an arbitrary relative operator; the Racah matrix here acts only on the three intermediate carrier bracketings after an operator subchannel has been authenticated.
artifacts:
  - notes/TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md
  - notes/FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md
  - experiments/atlas-s4-s3-branching.txt
---

Order the complex irreducibles of `S3` as `1, epsilon, sigma`, with
`dim(sigma)=2`.  Every tensor-product multiplicity is zero or one:

```text
epsilon epsilon = 1,
epsilon sigma = sigma,
sigma sigma = 1 + epsilon + sigma.                    (S3C1)
```

Consequently the two orthonormal coupling bases of

```text
Hom_S3(sigma tensor sigma tensor sigma, sigma)
```

are each indexed by the three intermediate channels `1,epsilon,sigma`.
For one Clebsch--Gordan sign convention, their change-of-bracketing matrix is

```text
F_sigma = [ 1/2       -1/2        1/sqrt(2) ]
          [ 1/2       -1/2       -1/sqrt(2) ]
          [ 1/sqrt(2)  1/sqrt(2)  0         ].        (S3C2)
```

It satisfies

```text
F_sigma^* F_sigma = I,       det(F_sigma)=1.          (S3C3)
```

Changing Clebsch--Gordan signs multiplies rows and columns by signs and does
not change non-singularity.

There are two further exact three-dimensional fingerprints in the same hard
cell.  The three `S4` types which meet in the standard `S3` channel are
`2,3,3 epsilon`.  Coupling their complete restrictions to the three
`S3` channels gives

```text
B = [ 0  1  0 ]
    [ 0  0  1 ]
    [ 1  1  1 ],                 det(B)=1.             (S3C4)
```

For the two `S4` vertices `A,B` in their generated `GL3(2)` cell, the
normalized central-idempotent overlap matrix on those same types is

```text
M = [ 1/24  1/16  1/16 ]
    [ 1/16  3/16  3/32 ]
    [ 1/16  3/32  3/16 ],       det(M)=3/8192.         (S3C5)
```

Here

```text
tau(P_lambda^A P_mu^B)
 = d_lambda d_mu/96
   <Res^S4_S3 chi_lambda, Res^S4_S3 chi_mu>.           (S3C6)
```

Thus the three extension directions which bare standard-channel dimensions
cannot distinguish do have nondegenerate coupled-channel and moment data.
This is not a decoder theorem: it does not say that the actual atlas relators
measure these three coordinates.  Exactification of the cross-chart prefix
as an `S4` representation is now supplied separately by
`actual-hard-prefix-generates-s4-over-raw-s3`; the relative external
multiplicity geometry between two such extensions remains outside this
finite carrier calculation.

Nor does the equality of the two dimensions `3` canonically identify the
Racah intermediate-channel space with the `2,3,3 epsilon` extension-label
space.  An arbitrary relative operator has the five standard-channel sources
listed in `s3-standard-operator-channel-has-fivefold-reduced-gauge`.
The packet must first isolate an extension-labelled triple inside that larger
reduced operator channel.
