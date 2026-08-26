# Alekseev--Thom boundary for a finitely presented Kazhdan kernel

Date: 2026-08-26

## Primary source

Vadim Alekseev and Andreas Thom, *Centralizers of sofic approximations of
Kazhdan groups*, arXiv:2608.05362:
https://arxiv.org/abs/2608.05362

Section 6 states Open Problem 6.1:

```text
Are there examples of finitely presented sofic groups with Kazhdan's
property (T) that are not residually finite?
```

The surrounding review separates the three known regimes relevant here:

- Thom supplies a finitely generated LEF Kazhdan group which is not
  residually finite; it cannot be finitely presented because finitely
  presented LEF groups are residually finite.
- de Cornulier supplies finitely presented non-Hopfian Kazhdan groups, and
  Thom supplies related hyperlinear examples, but their soficity is unknown.
- Kar--Nikolov supply finitely presented sofic non-residually-finite groups,
  but not property `(T)`.

## Consequence for the repository target

If the kernel `K` in the desired exact-radical-over-`Z` theorem were itself
finitely presented, it would solve the displayed open problem: it is a
subgroup of a sofic group and hence sofic; it is Kazhdan by hypothesis; and it
cannot be residually finite because a finitely generated residually finite
kernel has a residually finite automorphism mapping torus, whereas the target
mapping torus has nontrivial MF radical.

Accordingly, finite presentation of the total group `G` and finite
presentation of its kernel `K` must remain separate milestones.  The base
target asks only for the former.

## Additional construction constraint

The characteristic-zero Thom/Kida--Tucker-Drob seed recorded in
`torsion-free-lef-kazhdan-non-rf-seed` is LEF and therefore operator-MF by the
repository theorem `isOperatorMF_of_isLEF`.  Its product with `Z` is thus MF.
The cyclic automorphism must create the obstruction extrinsically; the trivial
action cannot complete the target.
