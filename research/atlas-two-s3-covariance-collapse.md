---
rg: 2
id: atlas-two-s3-covariance-collapse
kind: claim
title: The canonical Leavitt atlas packet collapses the two raw S3 covariance directions
distinct_from:
  raw-swap-forces-two-s3-covariance-energy: That proves the opposite lower bound under separation of the raw source word; this asks for the upper bound forced solely by the fixed atlas relator packet.
  full-packet-bicommutant-synchronization: That quantifies over arbitrary coordinate-selected elements of a full matrix commutant; this asks only about two fixed named elements of one six-element S3 subgroup.
  pauli-carrier-membership-decoder: That asks for membership of a transported projection in a raw finite algebra; this is the narrower fixed-word covariance statement already sufficient to contradict the raw swap.
artifacts:
  - docs/EXPLICIT_LEAVITT_ATLAS.md
  - docs/TRUE_RAW_WORD_REYNOLDS_GAP.md
  - docs/TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md
  - docs/ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md
  - experiments/atlas-raw-compressor-source-words.json
  - experiments/atlas_raw_reynolds_gap_audit.py
  - experiments/atlas-boundary-11-30.json
  - experiments/atlas_boundary_h_tangent_screen.py
  - experiments/atlas-boundary-h-irrep-greedy.json
  - experiments/atlas-boundary-h-finite-quotient-scan.json
---

Let `lambda:A_8->U(20160)` be the left regular representation and let
`bar_S` be the fixed finite normal generating packet from the canonical
regular-atlas criterion.  For arbitrary integers `k_n>=1` and relative chart
unitaries

```text
U_n in U(20160 k_n),
```

form the exact representations of `A_8*A_8`

```text
pi_n(h)=lambda(h) tensor I_(k_n)                         (h in K_1),
pi_n(h)=U_n(lambda(h) tensor I_(k_n))U_n^*               (h in K_2).
```

Let `h_a,h_b` be the two involutions in the certified raw `S_3` slice from
`TRUE_RAW_WORD_REYNOLDS_GAP`; they generate

```text
K=<h_a,h_b> ~= S_3.
```

Put

```text
a_n = ||U_n(lambda(h_a) tensor I)U_n^*-(lambda(h_a) tensor I)||_2,
b_n = ||U_n(lambda(h_b) tensor I)U_n^*-(lambda(h_b) tensor I)||_2.
```

Ask for the dimension-free implication

```text
max_(s in bar_S) ||pi_n(s)-1||_2 -> 0
       ==>
a_n^2+b_n^2 -> 0.                                      (ASC)
```

Equivalently, it would suffice to prove a quantitative inequality

```text
a^2+b^2 <= C * sum_(s in S_0) ||pi_U(s)-1||_2^2        (ASCq)
```

for some fixed finite `S_0` contained in the normal closure of `bar_S` and a
constant `C` independent of the external multiplicity `k`.

The lower side is already established:
`raw-swap-forces-two-s3-covariance-energy` says that preserving the nontrivial
raw source word forces `a_n^2+b_n^2 >= 1/40-o(1)`.  Thus `(ASC)` is the single
finite nonlinear estimate needed by the shortest present atlas route to an
explicit nonhyperlinear group.

## Finite geometry available

After the certified classical chart alignment, the hard boundary word in
class 11 has eight alternating syllables.  Its first two syllables fold to an
order-four element `D`; with the next raw `S_3` direction `Z`,

```text
<D,Z> ~= S_4,
```

while adjoining the complementary hard letter generates

```text
<D,Z,B> ~= GL_3(2)
```

of order `168`.  The two order-24 `S_4` extensions intersect exactly in the
raw `S_3`.

There is now an exact rational tangent certificate, not merely an SVD screen.
`atlas-boundary-h-irrep-greedy.json` shows that the five boundary indices

```text
0, 11, 30, 44, 55
```

have common derivative kernel equal to the `H=GL_3(2)`-fixed space in every
irreducible `A_8` representation.  Thus the classical fold is infinitesimally
rigid modulo the desired `H` symmetry in every representation type.  The
finite quotient scan also checks all `20160` inner `A_8` chart conjugators and
finds a unique exact solution for those five words, with the two `H` copies
coincident.

Neither fact is a global theorem: the quotient scan only ranges over inner
`A_8` positions, and tangent rigidity controls a neighbourhood of the
classical fold rather than arbitrary unitaries.

## Exact boundary-only no-go

A boundary-only proof of `(ASC)` is impossible.  The exact audit
`ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md` constructs

```text
E = M semidirect A_8,    dim_F2(M)=155,
```

with two injective `A_8` chart maps such that all `234` first-boundary words
vanish exactly, both chart restrictions are regular in the left regular
representation of `E`, yet the aligned copies disagree on the four standard
transvections generating `H`.  In particular the two raw `S_3` covariance
directions need not collapse under the complete boundary packet.

This is compatible with the tangent certificate: the affine solution is a
global characteristic-two escape, not an infinitesimal complex-unitary
motion of the classical fold.  It also explains why proving that the abstract
five-relator quotient is `H` would be insufficient for `(ASC)` even if the
Todd--Coxeter calculation terminated: the full 234-word boundary itself has
other exact regular-margin models.

Therefore every valid proof of `(ASC)` must use at least one genuinely
interior/full-atlas consequence of `bar_S` in addition to the boundary
geometry.  The same exact audit identifies collision word `19243` as a useful
test: one associated interior centrality condition kills the entire affine
boundary-countermodel family already in its order-zero quotient.  Before using
that particular word in a proof, its required centrality consequence must be
certified to lie in the normal closure of `bar_S` (or replaced by an explicit
member/consequence of `bar_S`).

## Attempts

1. **S3/S4 type counting.**  Dead.  `S3S4BranchingBalance.lean` and
   `FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md` show the restriction/branching
   counts are exactly balanced.  Any proof must use the actual multiplicity
   arrows, not dimensions of isotypic sectors.
2. **Full commutant synchronization.**  Unnecessarily strong and currently
   open.  The raw lower bound uses only `h_a,h_b`; proving `(ASC)` for these
   two fixed words bypasses coordinate-selected commutant unitaries.
3. **Boundary tangent rigidity.**  Closed locally: the rational all-irrep
   certificate gives exactly the `H`-fixed tangent kernel, and five words
   suffice.  It does not globalize by itself because of the exact affine
   countermodel above.
4. **Boundary-only nonlinear coercivity.**  Refuted.  No packet consisting
   solely of the 234 first-boundary relations can force the required two
   covariances in every regular-margin finite model.
5. **Boundary plus one interior separator.**  This is now the sharp local-to-
   global target.  Prove that a fixed interior/full-atlas consequence excludes
   every component outside a controlled neighbourhood of the classical fold;
   the exact all-irrep tangent gap can then supply local coercivity to `H`.
   The word-19243 centrality obstruction is the first concrete candidate
   because it kills the known affine escape family exactly.
6. **Matrix-specific positivity certificate.**  An ordinary tracial SOS valid
   in every finite tracial von Neumann algebra cannot work: the full atlas
   presentation has its exact group von Neumann algebra model.  A finite-
   dimensional/matricial certificate for the regular-`A_8` sector is still
   legitimate and would prove `(ASCq)`; it must use a genuinely matrix-specific
   ingredient rather than a universal group-algebra ideal identity.

The immediate finite task is therefore not another boundary search.  It is to
certify one interior consequence of `bar_S` and combine it with the exact
five-word tangent gap into a global matricial coercivity statement for the two
named `S_3` directions.
