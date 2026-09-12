# Laminar cycle configurations: overfilled stars

Lane `w5-laminar-cycle`, 2026-09-12. Target: `leavitt-units-have-laminar-finite-subgroup-defect`.
Supports `laminar-defects-localize-to-a-nonsofic-overfilled-star`. Builds on
`research/artifacts/finite-subgroup-combination-defects-2026-09-12.md` (lane `w4-kap-join`), whose
conventions, Theorem 2.1, Lemma 2.3, Corollary 2.4 and Theorem 2.6 are used below.

## 0. Setting

- `G` is any group, `p` a prime, `S = F_p[G]`.
- `H_0, ..., H_k <= G` are finite subgroups and `F = {x_i}` is a laminar family, `x_i` an idempotent of
  `M_n(F_p[H_(s(i))])`. Pairwise products lie in `{0, x_i, x_j}`.
- `r(x) = dim_(F_p)(x F_p[H]^n) / |H|` for an idempotent over a finite `H`, and `r(1) := n`.
- As in the proof of Theorem 2.1 of the `w4-kap-join` artifact: every member has a unique parent (the
  smallest member strictly above it, or `1`); `C(y)` is the set of children of `y in {1} u F`; the atoms
  `alpha_y = y - sum_(z in C(y)) z` are pairwise orthogonal idempotents summing to `1`; and every nonzero
  idempotent `d` of the span `B` of `1` and `F` is a sum of distinct nonzero atoms.
- `t_p` is the lifted trace on `K_0(S)`. On a laminar combination it takes the rational value
  `m n + sum m_i r(x_i)`.

## 1. A balanced configuration contains one nonsofic overfilled star

**Definition.** For `y in {1} u F`, the *star* of `y` is the laminar family `F_y = C(y) u {y}` (just `C(1)`
when `y = 1`), carried by the finite subgroups `Star(y)`: the subgroups of the members of `C(y)`, together
with the subgroup of `y` when `y != 1`. The star is *overfilled* when `sum_(z in C(y)) r(z) >= r(y)` and
`alpha_y != 0`.

**Theorem 1.1.** Let `d in B` be a nonzero idempotent with `t_p([d S^n]) <= 0` (for instance a balanced
combination, `t_p = 0`). Then some nonzero atom `alpha_y <= d` has an overfilled star, and that star occurs
in no sofic group, in the sense of Theorem 2.6: no sofic group contains finite subgroups `K_s ~= H_s`
(`H_s in Star(y)`) with isomorphisms agreeing on pairwise intersections and `K_s n K_t` equal to the image
of `H_s n H_t`.

*Proof.*
1. **Traces of atoms.** Write `d = sum_(alpha in T) alpha` over a nonempty set `T` of distinct nonzero
   atoms. Classes add over orthogonal idempotents, so `t_p([d S^n]) = sum_(alpha in T) t_p([alpha S^n])`.
   From `y = alpha_y + sum_(z in C(y)) z` and LFT1 of `lifted-trace-detects-finite-subgroup-projectives`,
   `t_p([alpha_y S^n]) = r(y) - sum_(z in C(y)) r(z)`, a rational number.
2. **One atom is overfilled.** If every `alpha in T` had positive trace, the sum would be positive. So some
   `alpha_y in T` has `sum_(z in C(y)) r(z) >= r(y)`, and `alpha_y != 0`.
3. **The star is laminar, and `alpha_y` is one of its atoms.** `F_y` is a subset of `F`, so its pairwise
   products lie in `{0} u F_y`. The members of `F_y` strictly below `y` are exactly `C(y)`: they are below
   `y` by definition, and no member of `C(y)` lies below another, since they are nonzero and pairwise
   orthogonal. So within `F_y` the children of `y` are `C(y)`, and `alpha_y` is an atom of `F_y`: a nonzero
   laminar combination of `F_y`.
4. **No sofic realization.** Suppose a sofic group contains `Star(y)`. Theorem 2.6, applied to the laminar
   family `F_y` over the subgroups of `Star(y)` and to the combination `alpha_y`, gives
   `t_p([alpha_y S^n]) > 0`. This contradicts step 2. QED

**Corollary 1.2 (shape of the star).** In Theorem 1.1, put `Y = y` and `C(y) = {z_1, ..., z_m}`. Then:
- `z_1, ..., z_m` are pairwise orthogonal, each `z_i <= Y`, and `z_1 + ... + z_m != Y`;
- `r(z_1) + ... + r(z_m) >= r(Y)`, although each `r(z_i) < r(Y)` by
  `nested-two-finite-subgroup-idempotents-have-strict-rank`, so `m >= 2`;
- the graph `Phi_y` on the distinct subgroups of `Star(y)`, with an edge for each nontrivial pairwise
  intersection, is not a forest, by Corollary 2.4 of the `w4-kap-join` artifact. So `Star(y)` has at least
  three distinct subgroups, and the children use at least two of them.

*Proof.* The first two items restate the definitions, step 2, and TFR1 applied to each pair `z_i < Y`.
If `Phi_y` were a forest, the intersection amalgam of `Star(y)` would be virtually free (Corollary 2.4),
hence sofic, and it contains `Star(y)` (Lemma 2.2), against Theorem 1.1. A graph with a cycle has at least
three vertices, and the parent's subgroup is at most one of them. QED

**Reading.** An overfilled star is a finite *paradoxical packing*. Finitely many pairwise orthogonal
finite-subgroup packets sit strictly inside one packet, yet their normalized sizes add up to at least its
size. Theorem 1.1 says every balanced configuration contains one, and Lemma 2.3 says no sofic group can host
one. With strict inequality `sum r(z_i) > r(Y)` the star's atom has negative lifted trace, so it would be an
even stronger certificate of nonsoficity than a balanced configuration.

**Corollary 1.3 (hosts).**
1. **Common finite overgroup.** If the subgroups of every star lie in a common finite subgroup of `G`, no
   nonzero laminar combination has `t_p <= 0`. In `R^x` this covers every star built from constants at
   finitely many prefix levels, which all lie in one `Theta(GL_(2^K)(F_2))` (Section 8.2 of the ternary
   normal-forms artifact).
2. **Sofic overgroup.** If the subgroups of a star lie in a sofic subgroup of `G`, that star is not
   overfilled with a nonzero atom. So an overfilled star with all its subgroups inside Thompson's group
   `V <= R^x` certifies that `V` is not sofic, which is open.
3. **The search is local.** A candidate for `leavitt-units-have-laminar-finite-subgroup-defect` is decided
   star by star: one parent packet, its orthogonal children, and a cycle of nontrivial intersections among
   at least three finite subgroups. The rest of the family can be discarded.

*Proof.* Items 1 and 2 are Theorem 2.6 with `Gamma` the finite overgroup or the sofic subgroup, which
contains the star with the actual intersections. Item 3 is Theorem 1.1. QED

**Answer to "does local finiteness kill cycles in `R^x`?"** Only in part. Local finiteness of the
constants kills every star inside finitely many levels (1.3.1). A star with a Thompson conjugate
`u H u^(-1)` escapes, and for stars inside `V` the question is at least as hard as soficity of `V` (1.3.2).
