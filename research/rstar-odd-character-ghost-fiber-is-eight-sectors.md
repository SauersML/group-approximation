---
rg: 2
id: rstar-odd-character-ghost-fiber-is-eight-sectors
kind: claim
title: Only the seven Fano lines and the full set are ghost-valued odd characters of R-star
distinct_from:
  rstar-fano-ghost-affine-hull-criterion: that detects whether one chosen support contains an odd zero-xor subset; this classifies every character of the full noise-free long-code packet and computes its marked Plancherel mass.
  rstar-cap-support-is-one-character-row: that deletes enough local atoms to put the original spectral support in one cap; this decodes arbitrary odd long-code characters and isolates the much smaller fiber on which decoding fails.
  linear-encoding-lcs-admits-odd-subset-cheats: that gives a conditional global statement for general constraint systems; this is an unconditional one-context calculation for the fixed seven-point relation.
---

Let `S=R_*`, let `E=F_2^S`, and index the characters of `E` by subsets
`T subseteq S`.  The central long-code mark selects the 64 odd characters

```text
|T|=1 mod 2.                                             (OCG1)
```

For such a character define its decoded four-bit assignment by

```text
d(T)=xor_(s in T) s.                                    (OCG2)
```

Because every member of `R_*` has odd parity, `d(T)` lies in the odd affine
hyperplane `H`.  Moreover

```text
d(T)=g
```

holds for exactly eight odd subsets: the seven translated Fano lines and the
full seven-point set `S`.  Every other odd character decodes to a member of
`R_*`.

Equivalently, write `V=F_2^3` and translate `S` by the ghost.  The xor of all
seven nonzero vectors of `V` is zero.  An odd zero-xor subset cannot have size
one.  At size three it is exactly a Fano line.  At size five its complementary
pair has the same xor, which is nonzero for two distinct points.  At size
seven it is the full set.  These are all possible odd sizes.

The map `(OCG2)` is linear from `F_2^7` onto `F_2^4`.  Each fiber has eight
elements, and its odd part maps onto `H`.  Thus every allowed point of `R_*`
has exactly eight odd-character preimages, while the ghost fiber consists of
the eight bad characters above.

Let `p_odd` be the odd-character projection in `C[E]` and let `q_good` be the
sum of the 56 atoms whose decoded value is in `R_*`.  For the canonical trace,

```text
tau(p_odd)=1/2,
tau(q_good)=56/128=7/16,
tau(p_odd-q_good)=8/128=1/16.                            (OCG3)
```

Hence the good and ghost masses conditioned on the marked sector are `7/8`
and `1/8`.  The projection `q_good` is invariant under the Fano automorphism
group `GL(3,2)`, so it is central in the finite semidirect packet

```text
E semidirect GL(3,2).                                   (OCG4)
```

On `q_good`, the decoded coordinate involutions have joint spectrum exactly
`R_*`, each allowed point with equal multiplicity.  Shared-variable long-code
marginal equations identify the corresponding decoded involutions, so no
priority choice is needed away from the ghost fiber.

This does not pin `q_good` to the identity.  The complementary ghost
projection has positive canonical trace by `(OCG3)`, and the regular-trace
firewall forbids deleting it by an exact identity valid in every
representation.  The remaining matrix-specific problem is therefore sharply
localized: transport or eliminate the seven line sectors and the one full-set
sector without destroying the exact marked model.  Treating all 63
nonsingleton odd characters as independent cheats is unnecessary.

