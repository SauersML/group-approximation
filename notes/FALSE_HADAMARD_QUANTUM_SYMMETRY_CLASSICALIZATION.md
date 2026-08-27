# Walsh--Hadamard transport is not automatically classical

Date: 2026-08-14

## 1. The tempting shortcut

For a perfect binary pairing `b : V x W -> F_2`, the sign table

```text
H_b(v,w) = (-1)^(b(v,w))                             (HQS1)
```

is a Walsh--Hadamard matrix of size `N=2^r`.  One might try to replace the
missing whole-map decoder by the assertion that every quantum transport
preserving this table is a classical mixture of pairing-preserving
permutations.

That assertion is unavailable in precisely the ranks needed by the
paired-radical program.  Gromada proves that every Hadamard matrix of size at
least four has nonclassical quantum symmetries; see Daniel Gromada,
[Quantum symmetries of Hadamard matrices](https://arxiv.org/abs/2210.02047),
in particular the main result advertised in the abstract.  Since `r>=2`
gives `N>=4`, the ordinary Walsh table is not protected by a general
"Hadamard symmetry implies permutation" theorem.

## 2. Relation to the elementary pairing box

`FALSE_NONSIGNALING_PAIRED_QUOTIENT_SHORTCUT.md` gives a more direct no-go
for the present proof architecture.  It constructs, for every `N>=4`, exact
source-pair correlations with

```text
b(output_left,output_right)=b(input_left,input_right)
```

on the two diagonal contexts and value zero on the crossed context, while
all endpoint marginals are the same uniform law on nonzero labels.  Hence
pairing preservation plus no-signaling does not produce a hidden whole map.

The quantum-symmetry theorem and the elementary box close two slightly
different shortcuts:

* the box rules out every argument using only labelwise laws, perfect winning,
  and matching marginals;
* Hadamard quantum symmetry rules out automatic classicality of a diagonal
  pairing transport merely because its Fourier sign matrix is Hadamard.

The cited theorem is not being used to assert that Gromada's quantum
symmetry is itself the particular three-context box above.  The box is proved
independently by finite counting.  The citation only closes the proposed
general rigidity principle for the individual Walsh--Hadamard transport.

## 3. Surviving target

The live statement remains special to the atlas relations:

```text
raw deterministic branch routing
        + comb extension-fiber covariance
        + cross-root multiplication
        => one decoder constant on each character fiber.       (HQS2)
```

Once `(HQS2)` is obtained, character PVM coarsening produces whole-map PVMs,
tree gluing produces a common latent-map law, and the robust `1/36` floor
gives the contradiction.  Neither generic no-signaling consistency nor
generic Hadamard quantum symmetry can supply `(HQS2)`.

This audit was recorded without running a local or MSI build.
