# Finitely presented simple groups and bounded-displacement actions on Z

Lane `hi-spec-zaremsky-1-10-fp-infinite-simp` (special case / strengthening), 2026-09-16.
- Root: `zaremsky-1-10-fp-infinite-simple-amenable-group`.
- Negation: `no-fp-infinite-simple-group-is-amenable`.
- Claims landed here:
  - `z-sft-full-groups-have-no-fg-infinite-simple-subgroup`, Theorem A;
  - `fp-simple-groups-avoid-the-wobbling-group-of-z`, Theorem B and Corollary C.

## 0. Outcome

- **Theorem A (full groups of `Z`-SFTs).** Let `V` be a `Z`-shift of finite type and `Γ ≤ [[Z ~ V]]` any subgroup.
  Let `N` be the subgroup fixing every periodic point, and `M = [N, N]`.
  - `Γ/N` is residually finite.
  - `M` embeds in a product of finitary symmetric groups, so every finitely generated subgroup of `M` is residually
    finite.
  - Hence no finitely generated infinite simple group embeds in `[[Z ~ V]]`.
- **Theorem B (wobbling group).** Every finitely presented subgroup of the wobbling group `W(Z)` is isomorphic to a
  subgroup of `[[Z ~ V]]` for some `Z`-SFT `V`. So it contains no finitely generated infinite simple subgroup. In
  particular, no finitely presented infinite simple group has a nontrivial homomorphism to `W(Z)`.
- **Corollary C.** A finitely presented infinite simple group `S` has no nontrivial homomorphism into:
  - C1: the bounded full group `W(φ)` of any bijection `φ` of a set. This includes the topological full group `[[φ]]`
    of every homeomorphism of a compact space, minimal or not.
  - C2: the bounded measurable full group `W(T)` of every measure-preserving `Z`-action, ergodic or not, modulo null
    sets.
  - C3: `W(Λ ~ Ω)` for every finitely generated virtually cyclic `Λ` and every `Λ`-set `Ω`.
  - C4: and `S` has no action on a set with an orbit where it acts nontrivially whose Schreier graph has finite
    bandwidth.

**What is new** (Section 6).
- Minimal `Z`-systems were already dead: Grigorchuk–Medynets LEF, recorded as
  `periodic-approximable-subshifts-host-no-fp-simple-group`.
- The new part is every non-minimal and non-free host over a virtually cyclic group. There LEF fails, since Houghton's
  `H_3` is finitely presented, is not residually finite, and lies in `W(Z)` and in the full group of an SFT.
- The mechanism replaces periodic approximation. Relators cut out an SFT neighbourhood, and in a `Z`-SFT an infinite
  simple group sees only germs at the two ends of orbits, which form a (locally finite)-by-abelian group.

Nothing here settles Problem 1.10.

## 1. Conventions

## 2. Theorem A

## 3. Theorem B

## 4. Corollary C

## 5. Sharpness and model tests

## 6. Literature and graph; what is new

## 7. Where the method stops
