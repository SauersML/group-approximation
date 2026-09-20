# Kourovka 20.44: consolidated state, 2026-09-19 (lane bh-2044-tc)

This supersedes the 20.44 section of bh-free-58's hand-off
(`research/artifacts/gq-bh-bh-free-58-kourovka-state-2026-09-19.md`, ce7ab8f74).
- **Status words.** "PASS" means a refereed PASS at the named commit; "lane proof" means not
  reviewed.
- **Credit.** Kohl posed 20.44 and built `G_T`. The tail, frozen-degree and corner framework is
  bh-free-58's. The referees are named per row.

## The problem (Kourovka Notebook, 21st issue, 2026, Problem 20.44, S. Kohl), verbatim

> The definition of CT(Z) is given in 17.57. Is it true that a finitely generated subgroup of
> CT(Z) either has only finitely many orbits on Z or there is a set of representatives for its
> orbits on Z which has positive density?

It is still **OPEN**. Settling it affirmatively is at least as hard as 3x+1 finiteness.

## Results

| result | node | commits |
|---|---|---|
| true in V = CT_∅(Z) | `ct-empty-z-subgroups-satisfy-the-orbit-transversal-dichotomy` | 2676555d5 (repair); **PASS** ab9d63e16 |
| true when every slope lies in `γ^Z`, `γ` an integer | `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44` | 50b7f0bf8; **PASS** 0de1f29ea |
| a frozen tail anywhere gives a positive-density transversal, for **every** f.g. `G` (reduction to TC groups) | `ct-z-frozen-tails-anywhere-give-kourovka-20-44` | bc9e6452b; **PASS** 643914a82 |
| cone-avoiding (trapped) lattices: frozen tails are trapped; `G` finite ⟺ finitely many slopes | `ct-p-z-cone-avoiding-slope-lattices-trap-frozen-tails` | eb4bbf804; **PASS** 8cf408649; refined 0aa2f4ef2 |
| mixed-sign ray: frozen tails force finite orbits | `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits` | 59f44f3c5; **PASS** a3b10b78d (bh-ref-d); heuristic sentence marked 77a7bd4d5 |
| TC core: finitely many orbits ⇒ TC; TC ⟺ finitely many orbits on a positive ray; `G_T` is TC | `ct-z-totally-consumable-core-of-kourovka-20-44` | 06eb299b0; **PASS** e2b397604 (items 1–3); heuristics marked 6586450a5 |
| Collatz-hard: `G_T` satisfies 20.44 iff 3x+1 has finitely many components on Z | `ct-z-orbit-transversal-dichotomy-is-collatz-hard` | 7b84a747f; **PASS** 23366da0a (bh-ref-q11) |
| infinitely many orbits of bounded size ⇒ positive density | `ct-z-orbit-transversal-counterexamples-need-unbounded-orbits` | 1c4a8a43c; lane proof |
| **orbit-local corner**: a TC group has ≤ 2Π^D orbits with local slope group in `γ^Z` | `ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups`, Theorem A | e8ef497b9; **PASS** c80ad216c (bh-ref-q12) |
| **joins**: every nonzero slope lattice is carried by a tame f.g. group; counterexamples travel from `M` to `M + Λ` | same node, Theorem B | e8ef497b9; **PASS** c80ad216c; `T_Λ` repair 77a7bd4d5 |
| **bounded transverse drift**: TC orbits whose drift lies within `f` of a positive ray meet `[−Π^(D+2f), Π^(D+2f))`; cohomological form (rcwa-conjugates of integer-ray groups) | `ct-z-bounded-transverse-drift-gives-kourovka-20-44` | 77a7bd4d5; **PASS with repairs** a64001bd6 (bh-ref-c); repairs applied in this landing |

Consolidated older statement: `kourovka-20-44-holds-for-rank-one-slope-groups` (b4cbe8e26,
da8e5dadd).

## Where the lattice picture now stands

- **Lattice shape is not a hardness invariant.** Every nonzero slope lattice carries a group with
  finitely many orbits. 20.44 for a lattice implies 20.44 for all its sublattices.
- **Collatz-hard lattices.** Via `G_T ⊔ Λ`, every lattice containing `Z e_2 ⊕ Z e_3` is
  Collatz-hard. No lattice with `dim C_Λ ≤ 1` contains it, and no other lattice is known to be
  Collatz-hard.
- **The class `dim C_Λ ≤ 1`.** It is equivalent to the tube class, which contains every trapped
  lattice as a sublattice. The method settles bounded trapped drift there; the rest is open.

## The exact remaining condition

**A counterexample's two necessary properties.** A finitely generated `G ≤ CT(Z)` that violates
20.44 must be:
1. **totally consumable:** no point of `Ẑ` has a frozen degree (frozen-tails node);
2. **of unbounded transverse drift across orbits:** for every `f ∈ N`, infinitely many orbits
   have all their points at transverse drift `δ(x) > f` from every positive ray (Theorem C).
   - A single orbit may still have finite drift. The obstruction is the lack of a uniform bound.

**Equivalently, for TC groups.** A TC group has finitely many orbits iff, for some `f`, only
finitely many of its orbits have transverse drift `> f`.
- The "if" direction is Theorem C.
- For "only if", note that finitely many orbits trivially have bounded drift after discarding
  them.

**Known instances of the condition.** Each is open.
- trapped sweeping, the Mahler-type analogy (heuristic);
- tube sweeping;
- Kohl's `G_T`, with 3x+1 drift `(−L, k)` (explanation, not a claim). Bounded drift for `G_T`
  would imply 3x+1 finiteness.

**Not known, and would be decisive.**
- A mechanism forcing descent under total consumption. Descent works in the explicit groups
  `E_γ`, and at the contracting end of a mixed ray, but it is not forced.
- Alternatively, a TC group with infinitely many orbits, of any density. That would refute the TC
  conjecture, and 20.44 too if the density is zero.

## Lessons (appended to LESSONS.md)

1. **Orbit hardness is orbit-local.** Joins make every slope lattice tame and carry counterexamples
   upward, so lattice shapes give only necessary conditions. The corner argument is orbit-local.
2. **The obstruction is transverse drift unbounded across orbits,** and it is a cohomological
   invariant. Bounded coboundaries, and so rcwa conjugation, never create it. The Mahler-type
   sweeping and 3x+1 both sit inside it.
3. **For BH hosts.** To keep an embedded subgroup's orbits tame, cobound its slope cocycle onto a
   positive ray. Host slopes elsewhere are irrelevant.

The lane stops here. The next step needs a new descent mechanism under total consumption; no lane
owns it.
