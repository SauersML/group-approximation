---
rg: 2
id: simple-inputs-have-fp-elementary-leavitt-tensor-hosts
kind: claim
title: Every infinite computably presented simple group sits in the units of a finitely presented central simple algebra whose Leavitt tensor has a finitely normally generated Steinberg kernel
distinct_from:
  decidable-group-algebras-have-fp-central-simple-hosts: that asks every decidable group algebra to embed in a host with K_1 and K_2 of B ⊗ L zero; this asks only for infinite simple inputs in the unit group and for finite normal generation of one unstable Steinberg kernel, with no K_1 condition, and that claim implies this one.
  decidable-group-ring-has-fp-projective-simple-host: that asks for an arbitrary ring host with three conditions (finitely normally generated Steinberg kernel, finitely generated centre, simple projective elementary group); this restricts to hosts B ⊗ L with B central simple, where simplicity and trivial centre are theorems, so only the kernel condition and the existence of B remain.
  infinite-simple-input-boone-higman: that asks for any finitely presented simple overgroup; this asks for one of algebraic origin, which yields such an overgroup through the Leavitt tensor elementary host criterion.
---

**OPEN.** Let `S` be an infinite, finitely generated, computably presented
simple group. Then there exist
- a finitely presented central simple unital `F_2`-algebra `B`,
- an injective group homomorphism `S -> B^x`, and
- an integer `n >= 4`,

such that `ker( St_n(B ⊗ L) -> E_n(B ⊗ L) )` is finitely normally generated
in `St_n(B ⊗ L)`, where `L = L_(F_2)(1,2)`.

## Why it is a certificate

By `leavitt-tensor-elementary-host-criterion`, `E_n(B ⊗ L)` is then a finitely
presented simple group containing `S`. That is `infinite-simple-input-boone-higman`,
equivalent to `boone-higman-conjecture`
(route `infinite-simple-input-bh-via-elementary-leavitt-hosts`).

## Where the difficulty sits

- **The kernel condition is the easy half.** It holds with trivial kernel
  whenever `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`
  (`leavitt-tensor-hosts-acyclic-steinberg-and-fp`), for instance when `B` is
  regular supercoherent (Ara--Cortiñas Proposition 6.2, imported as
  `ara-cortinas-leavitt-tensor-k-theory-vanishes`).
- **The existence of `B` is the wall.** What is missing is a finitely
  presented SIMPLE algebra containing `S` in its unit group. That is the
  algebra form of Boone--Higman itself.

## Attempts

1. **From the old premise.** Route `elementary-leavitt-hosts-from-central-simple-hosts`
   derives this claim from `decidable-group-algebras-have-fp-central-simple-hosts`.
   *Does not reach*: that premise is open and stronger.
2. **Published algebra embedding theorems.** Evans--Mandelberg--Neff (1975)
   give the weak half for algebras: a simple algebra inside a finitely presented
   one. Belyaev (1976--78) gives a Higman embedding for associative algebras,
   with no simplicity. *Dies*: no published theorem supplies a finitely
   presented simple envelope. The literature scout `bh-lit-map` found none
   (`research/artifacts/boone-higman-frontier-2026-09-12.md` §4, a bounded check).
3. **Maximal-ideal quotient.** Take a finitely presented algebra `P` containing
   `S` in its units (Belyaev), and pass to `P/M` for a maximal two-sided ideal
   `M` missing `S - 1`. *Dies*: `P/M` is finitely presented only if `M` is
   finitely generated as an ideal. This is the ring counterpart of
   `fp-quotient-iff-kernel-finitely-normally-generated`, and nothing controls it.
4. **Fixed Leavitt-type hosts.** Taking `B` from one fixed family (tensor powers
   of `L`, Leavitt path algebras) bounds the word-problem complexity of
   `E_n(B ⊗ L)`. *Dies* by `complexity-bounded-host-classes-are-not-universal`.
5. **Dropping `K_1`.** Done: `leavitt-tensor-elementary-host-criterion` needs no
   `K_1` hypothesis and only finite normal generation of one unstable kernel.
   This is why this claim, not the old premise, is the weakest known sufficient
   algebra premise on this route.
6. **Correction: the wall is overstated (lane `bh-algebra-envelopes`).** This
   premise needs only `S -> B^x`, not `F_2[S] ⊆ B`.
   - *Units without group algebras.* `full-group-units-embed-in-steinberg-algebras`
     puts topological full groups into Steinberg algebra units, while
     `full-group-algebra-to-steinberg-algebra-not-injective` shows the canonical
     group-algebra map has a kernel.
   - *What that makes of algebra BH.* `algebra-boone-higman-conjecture` is
     sufficient for the existence of `B` but not necessary.
   - *The real existence question.* A finitely presented central simple algebra
     whose unit group contains `S`. Candidates: Steinberg algebras of finite-type
     ample groupoids, matrix algebras over them, tensor products with `L`.
   - *Where new cases come from.* New Boone--Higman cases need unit groups
     larger than topological full groups. If `S` lies in a full group with fp
     simple derived subgroup, group BH already holds there.
   - *Still missing:* the Steinberg kernel condition for such `B ⊗ L`, and the
     universality of the host family. No single host or fixed family can serve,
     by `no-fp-simple-algebra-hosts-every-decidable-algebra`.
