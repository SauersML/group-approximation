---
rg: 2
id: kt-one-compressor-and-sl3-normalizer-lifts-paste
kind: claim
title: A one-compressor Kun--Thom lift and the full SL3 lift paste over their cyclic overlap
distinct_from:
  kt-one-compressor-normalizer-cocycle-splits: that splits the pullback over `H_A=<Gamma,A>` alone; this puts that split in one matrix ultraproduct with a split over the whole external group `S=SL_3(Z)` and makes the two copies of `A` literally equal.
  kt-two-compressor-normalizer-cocycle-splits: that removes Gamma and splits over `S`; this proves simultaneous compatibility with the full one-compressor subgroup through amenable-edge amalgamated-free-product permanence.
  kun-thom-finitary-action-lifts-to-normalizer: that asks for a lift of the quotient actor `G`; this lifts the larger amalgam actor `H_A*_<A>S`, whose kernel over `G` contains genuinely mixed Gamma--compressor words.
---

**ESTABLISHED.**  Use the `q=2`, `d=3` Kun--Thom pair, put

```text
H_A=<Gamma,A>,             S=<A,B>=SL_3(Z),
P_A=H_A *_<A> S,
R=L(Sym_fin((G/Gamma) x {0,1})).                       (KPA1)
```

The two restricted actions on `R` agree on `<A>`, so they induce an action
of `P_A`.  Then

```text
R rtimes P_A
  ~= (R rtimes H_A) *_(R rtimes <A>) (R rtimes S)      (KPA2)
```

is Connes embeddable.  Equivalently, there is a trace-correct homomorphism

```text
u:P_A -> N_(R^omega)(R),       Ad(u_p)|R=alpha_p.       (KPA3)
```

In particular the established lifts on the one-compressor group and on the
full external `SL_3(Z)` can be chosen in one copy of `R^omega` with their
`A`-unitaries literally identical.  The analogous statement holds with
`B` in place of `A`.

This removes a possible false bottleneck from
`kun-thom-finitary-action-lifts-to-normalizer`: there is no compatibility
obstruction on the cyclic overlap, and no obstruction coming merely from
choosing the compressor lift in two different matrix-ultraproduct models.
The first possible obstruction is the kernel of the natural quotient

```text
P_A -> <Gamma,A,S>=G.                                  (KPA4)
```

That kernel already contains explicit mixed normalization words, isolated
in `kt-c-normalization-is-the-first-finite-normalizer-seam`.

DERIVATION
kt-one-compressor-sl3-afp-paste-proof
