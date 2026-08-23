# No-renormalization adversarial collision compiler

Date: 2026-08-23.

## Status

This note separates a proved operator-norm detector package from one open
finite-syntax compiler target.

Proved and formalized:

1. packet collision forces phase collapse;
2. a finite palette/cover turns high chromaticity into such a collision;
3. an unbounded uniformly authenticated challenge family defeats every fixed
   finite-dimensional model by choosing the challenge after the coordinate;
4. projections at operator distance less than one have equal rank, and a
   nontrivial multiplicative rank monodromy forces the finite rank to vanish.

Open:

5. one explicit finite presentation in which all deep packet, edge, and
   expander checks are controlled by finitely many root relators with a
   depth-independent operator-norm constant, while an exact
   infinite-dimensional representation keeps the marked phase nontrivial.

The open item is not promoted to an unconditional non-MF construction.

Lean file:

```text
GroupApproximation/Sofic/NoRenormalizationCapacity.lean
```

## 1. Packet collision

Let `A,B_v,B_w,Z` be unitaries and assume

```text
||A B_v - Z B_v A|| <= epsilon,
||A B_w - B_w A|| <= epsilon,
||B_v-B_w|| <= delta.
```

Then

```text
||Z-I|| <= 2 delta + 2 epsilon.                         (NC1)
```

Indeed

```text
A B_v-B_v A
 = A(B_v-B_w)+(A B_w-B_w A)+(B_w-B_v)A,
```

so its norm is at most `2 delta+epsilon`.  Also

```text
(Z-I)B_v A
 = -(A B_v-ZB_vA)+(A B_v-B_vA).
```

Right multiplication by the unitary `B_v A` preserves operator norm and
gives `(NC1)`.  This is theorem `collision_kills_phase`.

The estimate sees a rank-one sector with full strength.  It uses no trace.

## 2. Finite palette and chromatic overflow

For a graph `H`, fix a finite cover of `U(d)` by sets of operator-norm diameter
at most `delta`.  Color `v` by the cover element containing `B_v`.  If every
coloring by this palette has a monochromatic edge, then some adjacent states
collide, and `(NC1)` applies.

The Lean interface uses the equivalent predicate

```text
DefeatsPalette Adjacent :=
  forall color, exists adjacent v w with color(v)=color(w).
```

This avoids tying the analytic theorem to a particular graph library while
retaining exactly the chromatic input.  The resulting theorem is
`phase_close_of_palette_overflow`.

For each fixed `d` and `delta>0`, compactness of `U(d)` supplies a finite
palette.  Thus authenticated graphs of unbounded chromatic number force the
marked phase to collapse in every fixed dimension.

## 3. Why the challenge is chosen after the coordinate

A naive recursive family does not suffice.  If a depth-`n` check costs
`C(n)` relator applications, a matrix model with defect `epsilon` controls it
only by `C(n) epsilon`.  Dimension may outrun this accuracy.

The self-hash interface requires one constant `C_0`, independent of address
and challenge depth:

```text
deep_check_error <= C_0 * root_defect.                    (SH)
```

Literal conjugacy to a root relator is the ideal implementation, because
unitary conjugation preserves operator norm exactly.

After fixing one coordinate `U` of dimension `d`, the proof chooses a
challenge whose capacity exceeds `d`.  Condition `(SH)` says that this late
challenge is no less accurate than the first one.  The formal logical core is
`no_model_of_uniform_unbounded_capacity`; the Cairn theorem
`opnorm-coordinatewise-capacity-diagonal` records the matrix-corona wrapper.

The machine or group never reads the dimension.

## 4. Rank monodromy

The second detector is discrete.  For orthogonal projections,

```text
||P-Q||_op < 1  =>  rank(P)=rank(Q).                       (RM1)
```

This was already formalized as
`InvolutionRankMass.rank_eq_of_projections_close` and is re-exposed by
`projection_rank_rigid`.

Suppose a cyclic selector has finite carrier rank `r`, and one traversal
forces

```text
a^k r = b^k r,
```

where `k>0` and `a!=b`.  Then `r=0`.  This integer endpoint is
`rank_zero_of_power_monodromy`.

To turn it into a group theorem, a compiler still has to authenticate the
decoded projections and the transport checks in operator norm.  The rank
arithmetic itself is complete.

## 5. Two conditional non-MF endings

### Collision ending

Assume a finite presentation with:

- a marked word `z`;
- finite challenge graphs of unbounded chromatic number;
- local twisted packet checks and edge cross checks;
- one depth-independent root-defect bound for every addressed check;
- an exact representation with `z!=1`.

If a norm-corona representation kept `z` separated, freeze one sufficiently
accurate coordinate.  Choose a graph beyond the finite palette capacity of
that coordinate.  The packet collision theorem forces `z` closer to one than
its separation.  Contradiction.

### Recursive Clifford-capacity ending

Assume instead that the self-hash and a constant-degree quantum-expander
checksum permit coherent exactification of one new Pauli cell at every level,
without altering the old exact prefix.  A nonzero finite active sector would
then carry `n` independent qubits for every `n`, forcing

```text
2^n divides d  for every n,
```

which is impossible.

Both endings are operator-norm arguments.  Neither uses a normalized
Hilbert--Schmidt corner.

## 6. Existing components and exact remaining seam

The repository already contains:

- `free-cone-shift-finitely-wordizes-recursive-clifford-tails`, which makes
  addressed recursion relations literal conjugates of fixed root relators;
- `finitely-presented-oligomorphic-linear-pauli-addresser`, which supplies
  finite Pauli packets and exact infinite completeness;
- `quantum-expander-relative-commutant-rounding`, the uniform analytic
  commutant checksum;
- `uniform-relative-clifford-tape-cell`, the desired one-step relative
  exactification conditional on level-indexed expander words;
- `self-similar-clifford-quantum-expander-tape`, the still-open syntax target;
- `opnorm-coordinatewise-capacity-diagonal`, the already-established abstract
  post-coordinate diagonal.

The new open node `self-hashing-expander-collision-presentation` asks for the
composition not supplied by any one of those nodes: one finite presentation
with depth-independent authentication of the packet, cross-edge, and
expander interfaces and an exact nontrivial marked model.

Polynomial derivation cost is not enough for this node.  A claim that the
current Pauli addresser or Clifford tape already supplies the full interface
would be incorrect.

## 7. Research interpretation

A finite-dimensional representation is treated as finite memory.  The group
contains an unbounded challenge family, but the verifier complexity stays
fixed.  A model either corrupts one root check, which operator norm detects on
even one direction, or executes the verifier and eventually exceeds its
finite palette/rank/Clifford capacity.

The useful slogan is:

```text
generate unbounded challenges;
self-hash every late check to a fixed root budget;
let the proof choose the nemesis after seeing the finite coordinate.
```

That is a distinct open research lane from the already-complete seeded
self-aware MF compiler and from the shadow-saturation/Kazhdan-renormalization
route.
