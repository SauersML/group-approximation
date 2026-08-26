---
rg: 2
id: fixed-literal-mark-fp-hardness-proof
kind: route
title: Apply the explicit Adian--Rabin transform to the fixed invisible mark
target: fixed-literal-mark-fp-first-level-hardness
requires:
  - adian-rabin-transform-for-mf
  - literal-central-mark-corona-invisible
---

# Fixed literal marked query on finite presentations: unconditional first-level hardness

## Statement

Let `E` be the fixed literal finitely presented non-MF group and `w` its
nontrivial MF-invisible mark.  For a finite-presentation code `c`, write

```text
SURV(c) := ∃ φ : E → Carrier(c), φ(w) ≠ 1,
KILL(c) := ∀ φ : E → Carrier(c), φ(w) = 1.
```

There is a computable transformation from a coded finite-presentation word
problem instance `(c,v)` to a finite-presentation code `T(c,v)` such that

```text
SURV(T(c,v)) iff v ≠ 1 in Carrier(c),
KILL(T(c,v)) iff v = 1 in Carrier(c).
```

Consequently `SURV` is not recursively enumerable, `KILL` is not co-r.e., and
neither predicate is decidable.  This theorem is weaker than second-level
hardness, but it is entirely finite-presentational and assumption-free.

## Construction

Use adequacy of the repository's explicit finite-presentation code syntax to
choose once and for all a code `eCode` and an isomorphism

```text
Carrier(eCode) ≃ E.
```

This is a fixed constant, not an oracle or an input theorem.  Define

```text
T(c,v) = RawTransform.rawTransform c eCode v.
```

`RawTransform.rawTransform` is literal list surgery, and the repository proves
it computable for every fixed second code.

## The surviving-word branch

The raw transformation presents the same group as the Rabin variant applied
to the free product `Carrier(c) * E`.  If `v ≠ 1` in `Carrier(c)`, its image in
the free product is nontrivial.  The proved Rabin-variant embedding clause then
embeds that whole free product into the output.

Compose the following explicit injective homomorphisms:

1. the inverse of `Carrier(eCode) ≃ E`;
2. the coded-presentation equivalence for `eCode`;
3. the right free-product inclusion;
4. the coded free-product equivalence;
5. the source embedding into the Rabin variant;
6. the variant-code equivalence;
7. the raw-transform equivalence.

The composite is an injective homomorphism `E → Carrier(T(c,v))`, so it keeps
the nontrivial mark nontrivial.  Hence `SURV(T(c,v))`.

## The trivial-word branch

If `v = 1`, the Rabin variant collapses to a free group and is operator-MF.
The raw-transform equivalence transfers operator-MF to `Carrier(T(c,v))`.

For any homomorphism `φ : E → Carrier(T(c,v))`, functoriality sends the
MF-invisible mark to an MF-invisible element of the target.  An operator-MF
group has trivial MF residual, so `φ(w)=1`.  Hence `KILL(T(c,v))`.

Since `SURV` and `KILL` are complements, the two implications give both exact
biconditionals.

## Computability consequences

The complement of the uniform finite-presentation word problem is not
recursively enumerable, proved internally from the repository's Boone machine
and raw certificate machinery.  Its computable reduction to `SURV` therefore
shows that `SURV` is not recursively enumerable.  Complementation gives that
`KILL` is not co-r.e.  A decidable predicate and its complement are both r.e.,
so neither side is decidable.

No Higman theorem, Chiodo theorem, property `(T)` input, undecidability
assumption, or literature theorem is used.
