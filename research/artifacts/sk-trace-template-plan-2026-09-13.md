# sk-trace-template plan (2026-09-13)

Lane `sk-trace-template` (wave 8, ROSTER-F). The brief comes from sk-fp-sofic-c's sharpest next target (4a4b6ad62c): a
trace-metric template theorem over products of gapped groups with bounded chief length, which would reduce every finite-group
hyperlinear model of a finitely presented infinite simple group to alternating constituents.

## Target
Let `S` be finitely presented, infinite and simple. Take any hyperlinear (or sofic) model of `S` through finite groups: maps
`X → Q_k` followed by unitary representations (or actions). Show that the model can be cut down, by finitely many canonical
steps, to a model whose terminal constituents are forced to be non-gapped, and identify those constituents as far as the
literature allows.

## Planned results (each with a complete proof, and a model test against G_X, SL_3(Z) and Thompson's V)
- **A. Irreducible sub-models and the constituent template.**
  - Every finite-group hyperlinear model of `S` contains a single-constituent (irreducible) model.
  - In any model, weight at least `δ/2` sits on constituents of dimension `> D` whose relator images are non-scalar but near
    scalar (`|χ̃| > θ`), for every `θ < 1` and every `D`.
  - Ingredients: the gap argument of `fp-simple-groups-have-no-gapped-finite-unitary-models`, run per constituent; the
    finite-projective-image collapse; a Mal'cev and compactness firewall for bounded dimension.
- **B. Products.** The per-constituent gap is inherited by arbitrary direct products and central quotients of θ-gapped groups,
  with no bound on the number of factors. So there are no models through them. This closes the "unbounded direct products"
  room left on `fp-simple-groups-have-no-classical-group-unitary-models`.
- **C. Bounded derived length.** A nontrivial perfect group has no hyperlinear or sofic model through finite solvable groups of
  bounded derived length. More generally, the model images can be pushed into the terminal derived subgroup.
- **D. Induced dichotomy.**
  - An irreducible model induced from a subgroup of index `t` yields either a sofic model of `S` through the transitive
    permutation image on `t` points, or an irreducible model through the stabilizer.
  - The proof uses the ultraproduct kernel dichotomy for simple `S`.
  - The permutation analog reduces transitive actions to primitive ones.
- **E. Sofic template.**
  - Every sofic approximation of `S` through finite permutation groups reduces to primitive permutation groups with no fixed-point
    gap. By `gap-sofic-approximations-are-local-embeddings` (PASS) those must exist.
  - By the minimal-degree theorem for primitive groups (Liebeck–Saxl 1991, Proc. LMS 63; to be quoted verbatim from the source
    before any citation route), their socles are `A_m^k` in product action on `ℓ`-subsets, with `m → ∞` and `ℓ/m → 0`: an
    alternating constituent.
- **F. What remains.** Primitive irreducible linear constituents with non-gapped layers: alternating components, outer parts,
  or permutations of components. These get an open claim with Attempts. "Bounded chief length" is not preserved under passing to
  stabilizers, and solvable wreath-type groups of bounded chief length are not gapped, so the template is organized by
  induction on constituents, not by chief length.

## Not duplicated
- sk-fp-sofic-a (permutation gap, affine and projective targets).
- sk-fp-sofic-c (gapped unitary models, classical groups).
- `fp-simple-weak-soficity-is-finite-field-linear-soficity`, which treats weak soficity.
- The Kac–Moody candidate scans (sk-fp-sofic-d).

All results land as Cairn claims with proof routes, queued with sk-verify-7, and wired as Attempts into
`hyperlinear-fp-infinite-simple-group` and `hyperlinear-fp-infinite-simple-kazhdan-group`.
