# Integer marker: one-ancilla residue for stable formalization (w5-integer-marker, 2026-09-12)

Lane `w5-integer-marker`. Target: decide whether the marker involution `tau` on `{0,1}^Z` becomes
formalizable after adding identity ancilla tracks (the integer warm-up of
`injective-binary-automata-are-stably-formalizable`). Not decided. This artifact proves a structural
disjointness lemma and uses it to pin the one-ancilla obstruction to a single Boolean-vanishing formal
residue.

## Section 1. Flip-control disjointness

`tau` flips cell `i` iff `m_i(x) = 1`, where `m_i = L_i R_i`,
`L_i = (1+x_{i-3})(1+x_{i-2})x_{i-1}` (left context `001` ending at `i-1`),
`R_i = x_{i+1}(1+x_{i+2})(1+x_{i+3})` (right context `100` starting at `i+1`). The control window
`C_i = {i-3,i-2,i-1,i+1,i+2,i+3}` omits `i`.

**Lemma 1.1.** Two markers are at distance `>= 5`, and no flipped cell lies in any active marker's
window. Proof: the four cases `d = 1,2,3,4` each force a single cell to be both `0` (from one marker's
context) and `1` (from the other's); left-right reflection handles `d < 0`. Full case table: see
`marker-flip-control-disjointness-proof`.

**Corollary 1.2.** `m(tau(x)) = m(x)` on every Boolean configuration, so `tau^2 = id`. The distance
bound `>= 5` is sharp: markers at `d = 5` coexist and their windows `C_i, C_{i+5}` share `{i+2,i+3}`.

## Section 2. The one-ancilla Bennett word and its residue

Two tracks over the free ring `F_2[X]`: data `x_g`, ancilla `y_g`. Gates, each a `Z`-equivariant
track shear and a formal involution:
`A: y += m(x)`, `B: x += y`, `A': y += m(x)` (reading the updated data). The word `W = A' B A` is
structurally reversible, hence a formalizable pair with `A B A'`
(`structurally-reversible-automata-are-formalizable`).

Trace on `y = 0`:
- after `A`: `(x, m(x))`;
- after `B`: `(x + m(x), m(x)) = (tau(x), m(x))`;
- after `A'`: data `tau(x)`, ancilla `r(x) = m(x) + m(tau(x))` with `tau(x) = x + m(x)` read formally.

By Corollary 1.2, `r(x)_g = 0` on all Boolean points, so `r in (x_h^2 + x_h)`. Formally `r != 0`: the
substitution `x_j -> x_j + m_j` perturbs `m_g` through any `j in C_g` that is itself a marker cell, and
Lemma 1.1 places such `j` only at distance `5 <= d <= 6` (overlapping windows). The lowest-degree part
of `r` is therefore a sum over these overlap cells; monomials have degree `>= 8`.

So `W` is formalizable but its shadow is `tau x id` only up to the ancilla residue `r`; a stable
formalization of `tau` with one ancilla exists iff `r` (and the higher layers its clearing spawns) is
cleared by a finite `Z`-equivariant word of allowed gates. This is the content of
`one-ancilla-marker-residue-is-supported-on-window-overlaps`.

## Section 3. Where it stands

- Each graded layer `I^k/I^{k+1}` of the clearing problem is onto
  (`binary-left-inverse-pairs-are-boolean-adically-formalizable`), so the only obstruction is
  termination: finite degree and finite memory.
- Regrouping along `4Z` terminates (`marker-involution-is-formalizable-after-regrouping`,
  `kari-words-give-virtual-formalizability-over-integers`), but uses blocking, not a `Z`-equivariant
  ancilla word.
- A single extra shear cannot equal `r` (degree/shape mismatch); two or more re-enter the graded
  problem. No `Z`-equivariant terminating word is known, and no multi-track invariant ruling one out is
  known.
- Scope: this is the integer warm-up. Per the hub's scope note, the load-bearing stable-formalization
  test object is a reversible binary automaton on a finitely generated simple host (no finite-index
  subgroups, so regrouping is unavailable). The disjointness method of Section 1 is specific to this
  marker's `001 | 100` pattern and does not transfer as stated.
