---
rg: 2
id: decidable-group-algebras-have-fp-central-simple-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds in a finitely presented central simple algebra with K-theoretically trivial Leavitt tensor
distinct_from:
  decidable-group-ring-has-fp-projective-simple-host: that asks for a ring host whose projective elementary group is finitely presented and simple, which still requires finitely normally generating an unstable Steinberg kernel; this asks only for a finitely presented central simple algebra B with K_1 and K_2 of B ⊗ L zero, because tensoring with L makes that kernel trivial.
  boone-higman-conjecture: that is the group embedding conjecture; this is an algebra embedding statement which implies it through the Leavitt tensor host theorem, with no known converse.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem. Then
there is a finitely presented central simple unital `F_2`-algebra `B` with:
- a unital embedding `F_2[G] -> B`;
- `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`, where `L = L_(F_2)(1,2)`.

By Ara--Cortiñas Proposition 6.2, the `K`-theory condition holds whenever `B`
is regular supercoherent.

## Why it is a certificate

By `leavitt-tensor-hosts-acyclic-steinberg-and-fp` and
`central-simple-leavitt-tensor-unit-groups-are-simple`, `(B ⊗ L)^x` is
finitely presented and simple. It contains `G <= F_2[G]^x <= B^x`. This is the
route `boone-higman-via-central-simple-leavitt-tensor-host`.

## Attempts

1. **Evans--Mandelberg--Neff (1975).** Their Boone--Higman type theorems for
   algebras give the weak half: a simple algebra that embeds in a finitely
   presented algebra.
   *Does not reach*: finite presentation of the simple host is exactly the
   missing half, the algebra counterpart of the group wall.
2. **Fixed Leavitt-type hosts.** `B = L^(⊗d)` or a Leavitt path algebra.
   *Dies*: one finitely presented algebra has one word-problem bound. Its unit
   group is a finitely presented simple group, so
   `complexity-bounded-host-classes-are-not-universal` forbids universality.
   A universal family needs hosts with unbounded complexity.
3. **Maximal-ideal quotient.** Embed `F_2[G]` in a finitely presented algebra
   `P` missing every proper ideal, and pass to `P/M` for a maximal ideal `M`.
   *Dies* at the same point as `fp-quotient-iff-kernel-finitely-normally-generated`:
   `M` need not be finitely generated as an ideal. The requirement that `B`
   be central simple, not just simple, is inessential: a finite centre only
   changes `(B ⊗ L)^x` by a finite central quotient.
4. **Complexity test.** A proof must produce algebras `B` with arbitrarily hard
   decidable word problems. Nothing in the statement conflicts with that,
   unlike fixed hosts.
5. **Regular supercoherent hosts (lane `bh-steinberg-hosts`).** The sufficient
   condition in the statement cannot hold for hosts of the usual shape once
   `G ⊇ Z wr Z`. By `coherent-flat-group-algebra-hosts-force-fp-infinity`, a left
   coherent `B` that contains `F_2[G]` flatly as a right-module summand forces
   every finitely generated subgroup of `G` to be of type `FP_infinity`, and
   `Z wr Z` is not even `FP_2`. That shape includes a free module with `1` in a
   basis, and crossed-product, free-product and HNN hosts over `F_2[G]`.
   *Not a refutation*: the statement asks only for vanishing `K_1` and `K_2` of
   `B ⊗ L`, and allows non-coherent or non-flat hosts. A proof must obtain the
   `K`-theory without regular coherence, or embed `F_2[G]` non-flatly.
6. **Nilpotent trace screen (swarm-0917, `leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`).**
   *Necessary condition proved; the hole stays OPEN.*
   - *Detector.* A tail-orbit trace on `L` and the logarithmic derivative of the
     grading give homomorphisms `χ_(φ,m) : K_1(B ⊗ L) -> F_2`. They send
     `1 + x ⊗ e_1` to `φ(tr x^m)`, for nilpotent `x` over `B` and traces `φ` of `B`.
   - *Screen on `B`.* `K_1(B ⊗ L) = 0` forces `tr(x^m) ∈ [B,B]` for every
     nilpotent matrix `x` over `B`.
   - *Screen on the embedding.* For every `g ∈ G` of `2`-power order,
     `(g - 1)^m ∈ [B,B]` for all `m >= 1`. So `F_2[G] -> B` must send `g` to
     `1` in `HH_0(B)`, although `[g] != [1]` in `HH_0(F_2[G])`.
   - *Class killed.* `K_1(F_2[G] ⊗ L) != 0` whenever `G` has 2-torsion. Every
     vanishing argument valid for a class containing `F_2[ε]` dies at `1 + ε ⊗ e_1`.
     That includes coefficient-free swindles and arguments natural in `B`.
   - *Open.* Whether some simple, or central simple, `F_2`-algebra fails the
     screen. Semisimple Artinian algebras pass it.
