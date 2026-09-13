---
rg: 2
id: kazhdan-compression-instances-have-infinite-vcd
kind: claim
title: A compressed pair with a commuting factor J puts J^n inside the compressed subgroup for every n, so compression criteria never fire in a group of finite virtual cohomological dimension
distinct_from:
  vcd-two-groups-contain-no-kazhdan-commuting-pairs: that uses dimension two to make any commuting partner of an infinite Kazhdan subgroup finite, with no compressor; this uses the compressor to build unbounded direct powers of the commuting factor, which excludes the criterion in every finite virtual cohomological dimension.
  fournier-facio-group-contains-simple-wreath-shift: that derives the internal wreath shift and the self-similar tail (W7) for the Fournier--Facio data; this is the same nesting for every instance of the criterion, with its consequence for cohomological dimension.
  openai-expander-matching-criterion: that is the criterion; this is a structural consequence of its hypotheses alone, which holds whether or not the ambient group is sofic.
---

**ESTABLISHED.**

**(N1) Nesting.** Let `Gamma, J <= G` with `[Gamma, J] = 1` and `Gamma cap J = 1`, and let
`t in G` satisfy `t Gamma t^-1 <= Gamma` and `t J t^-1 <= Gamma`. Put `J_k = t^k J t^-k`. Then,
for every `n >= 1`, an internal direct product sits inside `Gamma`:

```text
Gamma >= J_1 x J_2 x ... x J_n x t^n Gamma t^-n.
```

**(N1') Formalized form.** The hypotheses of `one-sided-compression-nonsofic-criterion` give
`J <= Gamma` and a compressor `q` with `q Gamma q^-1 <= Gamma` that centralizes `J` and meets it
trivially. Then `Gamma >= J x q J q^-1 x ... x q^(n-1) J q^-(n-1) x q^n Gamma q^-n` for every `n`.

**(N2) Dimension.** In either form, if `J != 1` then `G` contains `J^n` for every `n`. So no
finite-index subgroup of `G` has finite cohomological dimension:
- if `J` has an element of infinite order, `G` contains `Z^n` for every `n`;
- otherwise `G` contains `(Z/p)^n` for every `n`, for some prime `p`.

## Consequences

- **The criterion needs infinite dimension.** A group certified nonsofic through
  `openai-expander-matching-criterion` or `one-sided-compression-nonsofic-criterion` has a
  non-LEF, hence nontrivial, factor `J`. So it has no finite-index subgroup of finite
  cohomological dimension. The same holds for Kun--Thom generalized wreath products over an
  infinite coset space, whose lamp group is an infinite direct sum.
- **Groups of finite vcd are out of its reach.** No subgroup of a group of finite virtual
  cohomological dimension is an instance. This covers the open roots that ask for nonsofic groups
  in finite dimension:
  - `titz-witzel-kernel-nonsofic` (cohomological dimension two);
  - `radu-bmw-lattice-nonsofic` and `nonsofic-one-vertex-square-complex-group` (virtual dimension
    two);
  - `nonsofic-one-relator-group` (virtual dimension at most two), where local indicability
    already excluded Kazhdan subgroups;
  - every virtually torsion-free candidate for `nonsofic-hyperbolic-group`.
- **Not covered: the Kun--Thom double.** `G *_Gamma G` (`kt-pair-group-double-is-nonsofic`) is
  certified by infranormality alone, with no commuting factor. Its recorded instances, including
  the Bowen--Chapman Lean witness (`bowen-chapman-witness-is-kt-double-at-q2-r3-d3`), have
  infinite virtual dimension for a different reason: they contain the root subgroups
  `e_12(F_q[x^(±1)])`, infinite elementary abelian `p`-groups. Whether an infranormal but not
  normal Kazhdan pair can exist in finite virtual cohomological dimension is not settled here.

So every nonsofic group this graph obtains from the compression criterion, from lamps, or from
the recorded Kun--Thom doubles has infinite virtual cohomological dimension. A nonsofic group of
finite virtual cohomological dimension, if one exists, needs a different certificate.

Credit: the nesting is the argument of `fournier-facio-group-contains-simple-wreath-shift` (W7),
stated for arbitrary criterion data. Proof: `kazhdan-compression-instances-have-infinite-vcd-proof`.
