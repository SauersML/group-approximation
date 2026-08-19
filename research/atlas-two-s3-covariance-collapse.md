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
  - experiments/atlas-raw-compressor-source-words.json
  - experiments/atlas_raw_reynolds_gap_audit.py
  - experiments/atlas-boundary-11-30.json
  - experiments/atlas_boundary_h_tangent_screen.py
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
raw `S_3`.  Hence the required estimate is a finite multiplicity-arrow
problem, not an unbounded group search.

## Attempts

1. **S3/S4 type counting.**  Dead.  `S3S4BranchingBalance.lean` and
   `FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md` show the restriction/branching
   counts are exactly balanced.  Any proof must use the actual multiplicity
   arrows, not dimensions of isotypic sectors.
2. **Full commutant synchronization.**  Unnecessarily strong and currently
   open.  The raw lower bound uses only `h_a,h_b`; proving `(ASC)` for these
   two fixed words bypasses coordinate-selected commutant unitaries.
3. **Linearized hard-boundary screen.**  The exploratory script
   `atlas_boundary_h_tangent_screen.py` tests tangent-kernel inclusion around
   the classical fold.  It is evidence only: no committed exact certificate
   upgrades its numerical SVD to a nonlinear, dimension-free estimate.
4. **Class-11 nonlinear coercivity.**  The promising target is to control the
   cross-chart prefix
   `P=U lambda(X)U^* lambda(B)` against its folded value
   `D=lambda(XB)`, then use finite `S_4`/`GL_3(2)` Reynolds averaging to force
   the two `S_3` covariance defects down.  One eight-letter relator alone may
   have nonclassical exact solutions, so a proof must use a fixed packet of
   compatible boundary/comb relations or an explicit sum-of-squares
   coercivity identity.
5. **Finite SOS / spectral certificate.**  Because all coefficient matrices
   live in the fixed algebra `M_20160(C)` and external multiplicity appears
   only as `tensor I_k`, seek a fixed noncommutative sum-of-squares identity
   proving `(ASCq)`.  No such certificate is currently present in the graph.
