# Archimedean inputs for Higman's unit conjecture on the Promislow group (lane hl-promislow-positivity, 2026-09-14)

**Target.** `integral-unit-conjecture-torsion-free` on the Promislow group `P`,
equivalent on `P` to the rational form by `rational-units-rescale-to-integral-units`.
Gap (G1) of `research/artifacts/promislow-case-a-2026-09-13.md`: characteristic-p
shadow information cannot close Case A (e47194344), so a proof must use
characteristic-0 structure.

**Verdict: partial.** No unit found and no triviality proved. One archimedean
theorem landed: `integral-group-ring-units-have-arithmetically-large-spectra`.
It is a necessary spectral condition on every nontrivial unit, not a triviality
proof.

## 1. Archimedean positivity (directive step 1)

For a unit `u` of `Z[P]`, `w = u u*` is a positive unit. Its Fourier matrix
`M_w(theta)` (the induced representation from `L ≅ Z^3`) is positive definite
on `T^3` with `det M_w(theta) = 1`, by `promislow-group-ring-units-are-constant-reduced-norm`.
What each natural input gives:

- **AM--GM.** `tau(w) = (1/4) integral tr M_w >= 1`, with equality only when
  `M_w = I` on `T^3`, i.e. `u = +-g`. For a nontrivial unit this says
  `sum_g u_g^2 >= 2`, which the integrality of `tau(w)` already forces. No
  obstruction.
- **Fuglede--Kadison determinant.** `log det_FK(w) = tau(log w) = 0` for every
  unit, trivial or not. It is the Mahler measure of the constant `Nrd = +-1`
  and carries no information.
- **Integer moments.** `tau(w^k) in Z` for all `k in Z`. These are satisfied by
  the nontrivial unit `x + x^-1 - 1` of `Z[C_5]`, which has the same
  determinant and moment properties. So moments alone cannot use
  torsion-freeness.
- **Capacity (the input that bites).** Integer moments make the Stieltjes
  transform an integer series at infinity. Pólya's theorem forces finite
  spectrum below capacity one (`integral-spectra-of-small-capacity-are-finite`),
  and the domain property of `C[P]` turns finite spectrum into triviality. This
  is the landed theorem: every nontrivial unit has `||u||, ||u^-1|| > 2` and
  `max(||u||, ||u^-1||) >= 1 + sqrt 2`, and every integer Laurent polynomial of
  `u u*` has spectrum of capacity at least one.

**Remark, not a claim.** At a root of unity `theta`, `M_w(theta)` has
algebraic-integer entries and determinant `1`, so its eigenvalues are algebraic
units. Galois conjugation moves `theta` to another root of unity. So
`sigma(u u*)` contains complete conjugate sets of algebraic units, as a
Fekete--Szegő-type heuristic predicts once the capacity is at least one.

## 2. Oliver's integral logarithm (directive step 2): not executed

- The MSI login connection was down for the whole lane, so no source for Oliver's
  integral logarithm was pinned, and nothing depending on it was landed.
- **Structural limit, recorded as reasoning only.** `P` is residually a finite
  2-group (take the quotients `P/2^k L`), so a unit `u` of `Z[P]` gives units
  `u_N` of `Z_2[P/N]`. As Oliver's theorem is usually quoted (not pinned here),
  the integral logarithm on `K_1(Z_p[G])` for a finite `p`-group `G` has the
  torsion subgroup as its kernel. So vanishing would place the class of `u_N`
  in a torsion subgroup of `K_1`, not `u_N` in `+-P/N`. Turning that into
  triviality of `u` needs an extra input controlling `SK_1` and commutators,
  which is not on main.

## 3. Exact gap

- By the collapse lemma (Step 2 of
  `integral-group-ring-units-arithmetically-large-spectra-proof`), an
  archimedean proof of triviality for a unit `u` of `Z[P]` is exactly a proof
  that some nonconstant integer Laurent polynomial maps `sigma(u u*)` into a set
  of capacity below one.
- For Case A units, `u u*` is `1` on the three definite dihedral shadows. So
  `1 in sigma(u u*)`, and nothing more follows from the shadows.
- A counterexample must have both `||u||` and `||u^-1||` above `2`, and
  `sigma(u u*)` arithmetically large. No mechanism on main forces the spectrum
  of a Case A unit to be small, and none rules out a large one.

## 4. Checks

- **Local lint.** The ids are new, both files have a `title:`, and every
  `requires`, `target` and `distinct_from` entry names an existing claim on main.
- **Cairn.** Not run: the MSI login connection was down throughout. Per the
  lane rules the check has to run on MSI, so it is still owed.
- **Ownership.** No existing node was edited.
