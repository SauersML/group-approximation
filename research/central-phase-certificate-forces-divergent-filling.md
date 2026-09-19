---
rg: 2
id: central-phase-certificate-forces-divergent-filling
kind: claim
title: A finite central certificate for a residual word needs filling length at least inverse in the relator phase
distinct_from:
  controlled-central-phase-finite-group-barrier: that says a universally sound finite groupification of a controlled central phase must be affine over F_2, a statement about which phase *functions* a finite overgroup can realize; this fixes an arbitrary central certificate and bounds below the number of relator phases it must consume, a quantitative filling statement with no linearity conclusion.
  kun-thom-clifford-radical-phase: that exhibits one exact Clifford phase detector for the Kun--Thom sofic-radical word in an infinite crossed product; this constrains every *finite* central certificate for any residual word in any finitely presented group, and is a lower bound rather than a construction.
  boolean-predicate-central-phase-word: that compiles a Boolean predicate into a central phase word; this measures the modular cost any such compilation must pay when its relator phases are small.
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
---

Let `P=<S | r_1,...,r_l>` be finitely presented and let `w` be a word lying
in the finite residual

```text
R_fin(P) = intersection of kernels of homomorphisms P -> finite groups.
```

Every sofic-radical word satisfies this: if `w` survives in a finite quotient
`Q`, then `P -> Q -> Sym(Q)` is an exact finite model placing `w` at
normalized Hamming distance `1` from the identity, so `w` is sofic-visible.

Call a **finite central certificate** for `w` the data of a finite group `E`,
a central element `z in Z(E)` of order `m`, and a homomorphism from the free
group on `S` into `E` under which

```text
r_j |-> z^(b_j)   (1 <= j <= l),        w |-> z^a.               (CPC1)
```

Write `|k|_m = min_(n in Z) |k - n m|` for the distance to `0` in `Z/m`.
Then:

1. **(Filling identity.)**  There are integers `c_1,...,c_l` with

```text
a = sum_j c_j b_j   (mod m).                                     (CPC2)
```

2. **(Divergence.)**  Suppose the relator phases are uniformly small and the
   witness phase stays macroscopic:

```text
|b_j|_m <= eps m   for all j,        |e^(2 pi i a / m) - 1| >= eta > 0.
```

   Put `kappa(eta) = (1/pi) arcsin(eta/2)`.  Then

```text
sum_j |c_j| >= kappa(eta) / eps.                                 (CPC3)
```

## What this rules out

A central-character construction certifying a residual word cannot simply
drive the relator phases to zero while holding the witness phase fixed.  The
**modular filling length** of the witness -- the total coefficient mass
needed to write its phase out of the relator phases -- must diverge at least
like `1/eps`.  The bound is vacuous once `eps >= kappa(eta)`; it bites
exactly in the regime such constructions want to work in.

Consequently, wherever the free part of the relation module contributes only
*bounded* filling coefficients, the divergence in `(CPC3)` cannot be carried
there, and any successful central construction must place it in genuinely
growing torsion -- Schur multipliers, `H_2` -- instead.  This is a necessary
condition on the central-phase route, not a kill: nothing here says the
required torsion growth is unavailable.
