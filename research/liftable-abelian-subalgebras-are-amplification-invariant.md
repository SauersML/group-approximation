---
rg: 2
id: liftable-abelian-subalgebras-are-amplification-invariant
kind: claim
title: An abelian subalgebra of a matrix ultraproduct lifts to finite partitions iff its amplification by matrix algebras does, through a linear POVM orthogonalization
distinct_from:
  hs-block-gap-iff-liftable-masa-of-actor-commutant: that characterizes when a given partition algebra is a masa of an actor commutant; this shows liftability of any abelian subalgebra does not depend on tensoring with a matrix algebra, so partitions of the amplified algebra can always be pushed down.
  amenable-type-cycle-kills-liftable-masas: that is an obstruction to liftable masas; this is a transfer tool, used to move obstructions between a group and an ultraproduct model tensored with a fixed representation.
---

**ESTABLISHED.**

**Lemma 1 (orthogonalization).** Let `(M_k, tau)` carry the normalized trace, and let `{a_A}_(A in F)` be
positive contractions with `sum_A a_A = 1` and

```text
gamma  =  sum_A tau(a_A - a_A^2) .
```

Then there is a partition of unity `{p_A}_(A in F)` of `M_k` by projections with

```text
sum_A ||a_A - p_A||_2^2  <=  512 gamma + 128 gamma^(1/2) .
```

**Lemma 2 (amplification).** Let `U` be a free ultrafilter, `N_n, k_n >= 1`, and `D <= prod_U M_(k_n)` an
abelian von Neumann subalgebra. Then `D = prod_U C_n` for partition algebras `C_n` of `M_(k_n)` if and
only if `1 (x) D <= prod_U (M_(N_n) (x) M_(k_n))` is `prod_U C~_n` for partition algebras `C~_n` of
`M_(N_n) (x) M_(k_n)`.

In particular, if `Q <= prod_U M_(k_n)` has no liftable masa, then neither does `1 (x) Q` inside the
amplified ultraproduct: masas of `1 (x) Q` are `1 (x) D` for masas `D` of `Q`.

## Reading

- **What the lemma removes.** Partitions of the amplified algebra need not be of the form `1 (x) p`.
  The partial trace turns them into a POVM whose non-projectivity is exactly the 2-norm distance from
  the blocks to `1 (x) M_k` (`gamma = sum_A ||q_A - 1 (x) E(q_A)||_2^2`). Lemma 1 rounds that POVM with
  a square-root loss, uniformly in the number of blocks.
- **Use.** A model `sigma = tau (x) (h o q)`, with `tau` genuine and irreducible on a Kazhdan subgroup
  containing `ker q`, has actor commutant `1 (x) (h' cap prod_U M_(k_n))`. By Lemma 2 its liftable masas
  are exactly those of the relative commutant of `h`. This moves a non-liftability witness for `h` into
  any configuration that admits such a `tau`.
- **Credit.** Orthogonalization of almost projective POVMs with a bound independent of the number of
  outcomes is standard in the analysis of nonlocal games: Kempe--Vidick, Ji--Natarajan--Vidick--Wright--Yuen,
  and a linear bound due to de la Salle. The exact statements were not verified against those sources.
  The proof here is self-contained and uses only the Naimark dilation.

Derivation: `liftable-abelian-subalgebras-are-amplification-invariant-proof`.
