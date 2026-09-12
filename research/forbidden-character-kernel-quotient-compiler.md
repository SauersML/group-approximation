---
rg: 2
id: forbidden-character-kernel-quotient-compiler
kind: claim
title: A perfect-model kernel that separates every forbidden character gives a nonhyperlinear quotient
root: true
artifacts:
  - research/forbidden-character-kernel-quotient-compiler-proof.md
distinct_from:
  canonical-trace-forbids-supercritical-character-packing: that proves conjugate packing cannot exceed canonical capacity while the context packets embed; this changes the context packet images by a normal quotient and annihilates the forbidden characters directly.
  centralized-clause-zero-face-is-exact-affine-bcs-quotient: that characterizes the local affine spectra left by a clause quotient; this gives the exact kernel-character test and the resulting nonhyperlinearity theorem.
  ce-projective-kernel-face-gap-gives-nonhyperlinear-quotient: that assumes an entire finite-phase character face contains no CE trace; this starts from one perfect non-CE contextual trace and a local kernel-separation condition.
---

Let `Gamma` be a contextual group skeleton with a nontrivial central
involution `J`.  For each forbidden local type `i`, let `H_i<=Gamma` be its
finite abelian seed-context subgroup, let `chi_i` be the corresponding
character with `chi_i(J)=-1`, and put

```text
e_i=|H_i|^(-1) sum_(h in H_i) overline(chi_i(h)) h.    (FKQ1)
```

Suppose

```text
theta:Gamma->U(M)                                      (FKQ2)
```

is a perfect tracial contextual representation with `theta(J)=-1`, and its
contextual trace has no Connes-embeddable perfect realization.  Let
`N normal Gamma` satisfy

```text
N<=ker(theta),
chi_i is nontrivial on N intersect H_i   for every i.  (FKQ3)
```

Then the quotient

```text
barGamma=Gamma/N                                      (FKQ4)
```

is nonhyperlinear.

The local algebra is exact.  For any finite abelian subgroup `H<=Gamma`,
character `chi`, and `K=N intersect H`, the image of the character
idempotent in `C[H/K]` is

```text
0,                         if chi|K is nontrivial,
e_(H/K,barchi),             if chi|K is trivial.       (FKQ5)
```

Thus `(FKQ3)` is necessary and sufficient for this quotient to annihilate
each specified forbidden character idempotent.  Since `N<=ker(theta)`, the
perfect representation descends to `barGamma`; in particular `J` remains
nontrivial.

If `barGamma` were hyperlinear, its canonical group trace would be Connes
embeddable.  Cutting by the nonzero central projection `(1-J)/2` would give
a Connes-embeddable perfect contextual trace, because `(FKQ5)` makes every
forbidden local projection zero.  This contradicts the hypothesis on the
contextual trace.

The maximal possible choice is `N=ker(theta)`.  Hence some normal subgroup
as in `(FKQ3)` exists exactly when

```text
chi_i|_(ker(theta) intersect H_i) is nontrivial
for every forbidden i.                                (FKQ6)
```

Because there are only finitely many context groups, `(FKQ6)` has a much
smaller finite form.  Put `K_i=ker(theta) intersect H_i`, choose a finite
generating set `W_i` for each `K_i`, and set

```text
N=normalClosure_Gamma(union_i W_i).                    (FKQ7)
```

Then `(FKQ3)` holds for every forbidden type at once.  If `Gamma` is
finitely presented, this quotient is finitely presented as well.  For
binary contexts one needs only `dim_(F_2) K_i` relations from context `i`,
which is optimal locally by
`local-kernel-bases-optimally-annihilate-character-types`.

The remaining construction problem is therefore purely algebraic: arrange
one perfect non-CE contextual representation whose group kernel locally
separates every forbidden character.
