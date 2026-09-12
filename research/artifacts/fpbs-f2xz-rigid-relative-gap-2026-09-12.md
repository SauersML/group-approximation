# The rigid F_2 x Z graph: relative gaps along subgroups give no easier target

Lane `bs-f2xz-rigid-relative-gap`, 2026-09-12.

**Target.** `p_c < p_u` on
`X_rig = Cay(F_2 x Z, {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}^±)`. This is the
smallest rigid tree-projected graph. Its automorphism group is discrete, so
Hutchcroft's nonunimodular theorem does not apply (Section 3 of
`fpbs-f2xz-all-generating-sets-2026-09-12.md`). The strategy tried here was the
relative gap of `fpbs-relative-gap-along-any-subgroup-separates`: find one infinite
subgroup `I` with `p_c(G) < p_c(I;G)`.

**Outcome.** No proof. The strategy has a precise obstruction, landed as
`fpbs-central-amenable-relative-threshold-is-pu`. On every Cayley graph of a group
with an infinite central subgroup, the relative-gap premise along any subgroup
containing an infinite amenable subgroup is at least as strong as `p_c < p_u`. It
is equivalent to `p_c < p_u` exactly along the amenable subgroups.

## 1. The squeeze

Let `C` be an infinite central subgroup and `A` an infinite amenable subgroup.
1. `J = AC` is an amenable subgroup containing `C`.
2. Any subgroup that contains an infinite central subgroup is wq-normal: every
   conjugate of an intermediate subgroup still contains `C`.
3. So `p_c(J;G) = p_u(G)`, by Hutchcroft–Pan's relative Burton–Keane theorem and
   their wq-normal uniqueness transfer, through
   `fpbs-amenable-wq-normal-pu-is-relative-pc`.
4. Relative thresholds decrease as the subgroup grows, so
   `p_u(G) = p_c(J;G) <= p_c(A;G)`.
5. Hutchcroft–Pan Theorem 1.4 gives `p_c(A;G) <= p_u(G)` for every infinite
   subgroup (Section 7(a) of the frontier map).
6. Hence `p_c(A;G) = p_u(G)`, and for any `I >= A`,
   `p_c(I;G) <= p_c(A;G) = p_u(G)`.

## 2. What this rules out on `X_rig`

`F_2 x Z` is torsion-free, so every infinite subgroup contains an infinite cyclic
subgroup, which is amenable. Candidate subgroups compare as follows.

| subgroup `I` | `p_c(I;G)` | premise `p_c(G) < p_c(I;G)` |
| --- | --- | --- |
| centre `{1} x Z` | `= p_u(G)` | equivalent to the goal (known) |
| line `<(g,k)>`, `g != 1` | `= p_u(G)` | equivalent to the goal |
| `<g> x Z` | `= p_u(G)` | equivalent to the goal |
| free factor `<(a,0)>` | `= p_u(G)` | equivalent to the goal |
| `F_2 x {0}`, or any nonabelian subgroup | `<= p_u(G)` | implies the goal along each cyclic subgroup; no easier |

So the "thin-subgroup crux" of Section 7(d) of the frontier map changes on these
graphs. Along a cyclic subgroup `I` it reads:
- critical finiteness `chi^I_(p_c(G)) < infinity`;
- divergence `chi^I_p -> infinity` as `p ↑ p_u(G)`.

Both are open, and together they give the gap. Neither is made easier by
choosing a thinner or larger subgroup.

## 3. Other quick exclusions on `X_rig`

**Spectral criterion (Pak–Smirnova-Nagnibeda, `rho < 1/2`).**
- Take the Fourier transform along `Z` at frequency `theta`. The walk becomes
  `(1/14)[sum_s (phi_s(theta) R_s + conj) + 2 cos theta]` on `l2(F_2)`, with
  `phi_a = 1 + e^(i theta) + e^(3 i theta)` and
  `phi_b = 1 + e^(i theta) + e^(4 i theta)`.
- Twisting by the character `s -> conj(phi_s)/|phi_s|` removes the phases.
- At `theta = 0` this gives norm `(3 · 2 sqrt 3 + 2)/14 ≈ 0.885`. The weights are
  largest at `theta = 0`, and the free-group norm is monotone in the weights, so
  `rho(X_rig) = (6 sqrt 3 + 2)/14`.
- That is far above `1/2`, so the criterion does not apply.
- This is an elementary computation, not recorded in Cairn.

**Girth criterion (Nachmias–Peres).** It needs large girth, and `X_rig` has
triangles.

## 4. What remains for `X_rig`

- **L2 boundedness.** The critical sphere-bubble / L2 gap:
  `fpbs-tree-projected-critical-sphere-bubble-below-one`, equivalent to L2
  boundedness on these graphs through `fpbs-tree-projected-sphere-bubble-l2-equivalence`
  and `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`.
- **Central subcriticality.** Relative subcriticality along the centre just above
  `p_c` (`fpbs-bs-iff-finite-relative-susceptibility`). By Section 1 this is the
  same statement as along any line.

Neither is attacked beyond this note. Both are equivalent to or at least as hard
as the goal on this graph. Novelty was checked only against Cairn. The squeeze is
elementary given the imported Hutchcroft–Pan theorems.
