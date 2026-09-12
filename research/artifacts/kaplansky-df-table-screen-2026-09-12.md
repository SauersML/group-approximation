# Rule-free screen of support windows for one-sided inverse pairs in F_2[L^x] (2026-09-12)

Lane `kdf-l-times-search`. Target: `leavitt-unit-group-algebra-not-directly-finite`, that
is `alpha beta = 1 != beta alpha` in `F_2[G]`, with `G = L_(F_2)(1,2)^x`. Tools:
`experiments/nonsofic-certificates/kaplansky-df/screen/df_table_screen.py` (screen and
replay) and `df_class_sat.py` (SAT on the classes that survive). Everything ran on MSI at
`nice 10`, with the shared library `nonsofic-certificates/current` (VERSION 2e9a9873e), GAP
from `sagemath/10.7`, and CryptoMiniSat from the kdf-sat venv.

## 1. The filter

`one-sided-inverse-pairs-transfer-to-table-realizations`, Corollary 1. Fix finite supports
`A, B`. The table group `U(A, B)` has one generator `x_g` per cell `g in A u B u AB u BA`,
with `x_1 = 1` and relators `x_a x_b = x_(ab)`, `x_b x_a = x_(ba)`. Let `phi` be any
homomorphism from `U(A, B)` to a finite group. A strict pair with these supports would give
`phi_*(beta alpha - 1) = 0`, while `beta alpha - 1` is nonzero and supported on
`BA u {1}`. So:

- **dead window:** the images found are jointly injective on `BA u {1}`. Then no strict pair
  has `supp alpha in A` and `supp beta in B`, and no solver is involved.
- **surviving window:** the defect vanishes at every cell that some image separates from all
  others, and has coefficient sum `0` on each class of cells merged by every image. Those XOR
  rows go into the SAT encoding (Section 4).

The certificates are exact. Characters are checked against every relator of `U(A, B)`, and
so are permutation images. Replay: `df_table_screen.py --verify`.

**Reach on ball windows (Corollary 3).** For `A = B = B_r(X)`, `U(A, B)` is the cover
`G_(4r) = <X | trivial words of length <= 4r>`. The filter therefore stops working at the
radius where `4r` reaches the relator lengths of a presentation of `<X>`. Thompson's `V` and
`L^x` are finitely presented, so this happens at some finite radius in both families.

## 2. Method

1. **Cells and relators.** Every product is an exact normal-form product in `G` (`leavitt.py`),
   and the balls are those of `dfsat.py`.
2. **Stage 1, characters `U -> Z/p`.** Primes `2, 3, 5, 7, 1000003`, by sparse reduced echelon
   form over `F_p` with pivots at later cells. Two cells are separated exactly when their normal
   forms modulo the relation span differ. The stored characters are replayed against all relators.
3. **Stage 2, nonabelian images.** First the presentation is compacted: each cell that is the
   product of two earlier cells is defined by that product. GAP then takes a Tietze
   simplification and enumerates:
   - every quotient, up to automorphisms of the target, onto `A5`, `PSL(3,2)`, `A6`, `PSL(2,8)`,
     `PSL(2,11)`, `PSL(2,13)`, `A7` and `A8`, in their natural actions;
   - coset actions on the subgroups of index at most 6.

   Each image is written as permutations of the compact generators, replayed in Python against
   all relators of `U(A, B)`, and used to refine the partition of `BA u {1}`.

## 3. Hosts

The lane brief named three families of nonsofic hosts. Only one of them can carry a pair
that computation might find.

- **Kun–Thom actors** `G = EL_r(F_q[x_1^(+-1), ..., x_d^(+-1)]) semidirect SL_d(Z)`, with
  `r >= 3`, contain no pair. `EL_r` of a finitely generated commutative ring is finitely
  generated for `r >= 3` and linear, hence residually finite (Mal'cev). A split extension of a
  finitely generated residually finite group by a residually finite group is residually finite.
  So `G` is residually finite, and `F_2[G]` is directly finite by the second paragraph of
  `subgroup-supported-one-sided-inverse-rigidity-proof`.
- **Kun–Thom wreaths** `C_2 wr_(G/Gamma) G` contain no pair either. Their group algebras are
  stably finite over every field (`kun-thom-wreath-stably-finite`, through
  `rf-lamp-permutational-wreaths-satisfy-stable-finiteness`).
- **Belegradek–Osin covers** `G -> L^x` are hyperbolic with property (T), and their soficity is
  open. No explicit presentation is on main (checked `experiments/` at 0ccfbb0f1), so there are
  no products to screen. A strict pair over `L^x` also need not lift to a cover. They are
  recorded as out of computational reach.

So the search runs on `L^x` windows. The new family is `v-eld1`: the four Cannon–Floyd–Parry
generators of `V`, the six `E_ij(1)` of the nine-leaf corner, and the compressors `u, v`.

## 4. Results

(pending: filled from the MSI runs)

## 4. Trust surface

- A **DEAD** verdict is an exact certificate: replayable characters and permutation images of
  the table group, jointly injective on `BA u {1}`.
- A **SURVIVES** verdict records only that the images found did not separate. It says nothing
  about existence.
- A **class-SAT UNSAT** is a CryptoMiniSat verdict without a proof log. It goes in `## Attempts`
  and certifies nothing.
