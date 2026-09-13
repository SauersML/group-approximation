# Integer marker: one-ancilla residue for stable formalization (w5-integer-marker, 2026-09-12)

Lane `w5-integer-marker`. Target: decide whether the marker involution `tau` on `{0,1}^Z` becomes
formalizable after adding identity ancilla tracks. This is the integer instance of
`injective-binary-automata-are-stably-formalizable`, and the dihedral and V markers reduce to it. It is
not decided. This artifact proves a flip-control disjointness lemma, computes the formal residue of the
one-ancilla Bennett word, and records why that word is not a candidate.

Revision after w3-vf-nonlinear's check of 62f488374. Section 1 adds the reverse inclusion to
Corollary 1.2. Section 2 replaces a false support and degree statement and a false shadow statement.

## Section 1. Flip-control disjointness

`tau` flips cell `i` iff `m_i(x) = 1`, where `m_i = L_i R_i` with `L_i = (1+x_(i-3))(1+x_(i-2)) x_(i-1)`
and `R_i = x_(i+1)(1+x_(i+2))(1+x_(i+3))`. The window `C_i = {i-3, ..., i+3} \ {i}` omits `i`, and `M(x)`
is the set of markers.

**Lemma 1.1.** Two markers are at distance `>= 5`, and the bound is sharp. So no marker lies in another
marker's window. Proof: a marker at `i` fixes `x_(i-1) = x_(i+1) = 1` and `x_(i±2) = x_(i±3) = 0`. A
marker at `i + d` needs `x_(i+2) = 1` for `d = 1, 3`, `x_(i-1) = 0` for `d = 2`, and `x_(i+1) = 0` for
`d = 4`. Reflection handles `d < 0`. On cells `i-3, ..., i+8` the configuration `0,0,1,*,1,0,0,1,*,1,0,0`
has markers at `i` and `i + 5`.

**Corollary 1.2.** For `S ⊆ M(x)`, `M(x + 1_S) = M(x)`, so `m(tau x) = m(x)` and `tau^2 = id`. Proof: an
active window contains no marker, so no flip reaches it and its marker stays. A new marker `i` of
`x + 1_S` would have a flipped `j ∈ C_i`. That `j` stays a marker, so `x + 1_S` would have two markers at
distance `<= 3`, against Lemma 1.1.

This subset stability is the hypothesis of `subset-stable-marker-flips-are-virtually-formalizable`. Its
artifact (Section 5.2) checks it for this marker, and Lemma 1.1 adds the sharp constant.

## Section 2. The one-ancilla Bennett word

Two tracks over the free ring `F_2[X]`: data `x_g` and ancilla `y_g`. The gates `A: y += m(x)`,
`B: x += y` and `A'`, which is `A` reading the updated data, are `Z`-equivariant track shears and formal
involutions. So `W = A' B A` forms a formal pair with its reverse. Trace from `(x, y)`:
- after `A`: `(x, y + m(x))`;
- after `B`: `(x + y + m(x), y + m(x))`;
- after `A'`: `(x + y + m(x), y + m(x) + m(x + y + m(x)))`.

At `y = 0` the output is `(x + m(x), r(x))` with `r_g = m_g(x) + m_g(x + m(x))`, the residue of the hub's
First-test entry.

**2.1 Boolean vanishing.** By Corollary 1.2, `r = 0` on points, so `r ∈ (x_h^2 + x_h)`.

**2.2 Expansion.** `m_g` is multilinear in `C_g`, so `r_g = Σ_(∅ ≠ S ⊆ C_g) (Π_(k ∈ S) m_k) ∂_S m_g`.
- Every `j ∈ C_g` gives a first-order term `m_j ∂_j m_g`, and that term carries a clash factor
  `x_h (1 + x_h)`. For example, `h = g + 2` when `j = g + 1`.
- Take `1` from every `(1 + x)` factor. The degree-3 part of `r_g` is then
  `x_(g-2) x_g x_(g+1) + x_(g-1) x_g x_(g+2)`, from `j = g -+ 1`.
- The terms with `|j - g| = 2, 3` and all terms with `|S| >= 2` have degree `>= 4`.

So `r` is formally nonzero, with lowest degree 3 and lowest-degree part supported on adjacent cells. The
earlier text put this part on the distance-5 overlaps with degree `>= 8`. That was wrong: Lemma 1.1 is
Boolean and constrains nothing formally.

**2.3 Not a realization.** For Boolean `y != 0` the data output `x + y + m(x)` is not `tau(x)`. So `W`
has shadow `tau x id` only on `y = 0`, and clearing `r` with more ancilla gates would not give
`tau x id`. The earlier claim that a one-ancilla stable formalization exists iff `r` is cleared was
wrong for this reason.

**2.4 A realization writes the data track at least twice.** Take a word of track shears between the
data track and ancilla tracks, together with automorphisms of the ancilla tracks alone. Suppose the data
track is written by a single gate `x += f(z)`, where `z` is the ancilla state at that moment. Before that
gate the data is still `x`, and every earlier gate is bijective in the ancilla for fixed `x`. So `z` runs
over every ancilla configuration as `y` does. Correctness needs `f(z) = m(x)` for every `z`, which forces
`f` to be constant. That is impossible. So between two data writes, the cells that marker windows read
carry `y`-dependent values. The `4Z` word avoids exactly this, because the flip of one residue class
reads only the other classes.

## Section 3. Where it stands

- Each graded layer is onto (`binary-left-inverse-pairs-are-boolean-adically-formalizable`), so a
  negative answer is a failure of termination in degree and memory.
- Regrouping along `4Z` terminates (`marker-involution-is-formalizable-after-regrouping`,
  `kari-words-give-virtual-formalizability-over-integers`), but it uses blocking.
- No `Z`-equivariant pair with shadow `tau x id` is known. No multi-track invariant ruling one out is
  known either.
- Scope: the method of Section 1 is specific to the pattern `001 | 100`.

## Section 4. Verification record

- w3-vf-nonlinear, on 62f488374. Lemma 1.1, Corollary 1.2 and the route
  `marker-flip-control-disjointness-proof` PASS with two notes, both applied: the reverse inclusion,
  and the `d = 1` and `d = 3` case texts.
- The residue node's support and degree statement FAILED. Section 2.2 is the corrected version, and the
  degree-3 part is w3-vf-nonlinear's computation.
- w3-vf-nonlinear, on 9cb380bf47 (verdict at 73bc73756f, Section 27 follow-up of its verification
  artifact): the corrections PASS, and so do Sections 2.3 and 2.4. Section 2.4 is a necessary condition
  for its gate class (data-ancilla track shears plus ancilla automorphisms), not a decision.
