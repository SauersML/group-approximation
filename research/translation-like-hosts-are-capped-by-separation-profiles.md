---
rg: 2
id: translation-like-hosts-are-capped-by-separation-profiles
kind: claim
title: Translation-like realizations over a fixed group are capped by growth and separation profile, so no fixed hyperbolic or amenable-growth host is universal, and decidable monsters need non-free orbits or a finitely presented Farrell–Jones group containing expanders
requires:
  - translation-like-inputs-embed-in-full-groups-over-a-fixed-group
distinct_from:
  decidable-host-classes-reduce-to-canonical-kazhdan-groups: that filters host classes by subgroup-closed algebraic properties such as amenability and residual finiteness; this filters the fixed acting group of a translation-like realization by coarse geometry (growth and separation), which is not subgroup-closed information about the host.
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that is one growth kill for one input in low-growth wobbling groups; this is the general growth-plus-separation cap for free realizations over any fixed group, and names the escape.
---

**ESTABLISHED** (lane proof, bh-invent-09; elementary given the cited coarse-geometry facts; not reviewed).
The separation-profile facts are recalled, not re-read: Benjamini–Schramm–Timár (sep is monotone under
regular maps; sep(Z^d) ≍ n^((d−1)/d); sep(T×T) ≍ n/log n; expander families have sep ≍ n) and
Hume–Mackay–Tessera (sep of a hyperbolic group ≍ n^(1−1/Q), Q the conformal dimension of the boundary).

## Theorem 4 (the cap)

Suppose `Γ` acts translation-like on `Λ`, as in `translation-like-inputs-embed-in-full-groups-over-a-fixed-group`.
For any `v`, the orbit map `γ ↦ v·γ` is injective by freeness, and `R`-Lipschitz from `Cay(Γ, S)` to `Cay(Λ)`.
It is therefore a regular map, so:
- `|B_Γ(n)| ≤ |B_Λ(Rn)|`, the growth cap;
- `sep_Γ ≲ sep_Λ`, the separation cap.

## Consequences

1. **Fixed virtually abelian hosts are useless.** `Λ = Z^d` admits only groups of polynomial growth
   of degree at most `d`, which are already virtually nilpotent and linear.
2. **No fixed hyperbolic host is universal, even for abelian inputs.** For `Λ` hyperbolic with conformal
   dimension `Q`, `sep_Λ ≍ n^(1−1/Q)`.
   - This excludes `Z^d` once `(d−1)/d > 1 − 1/Q`, that is, `d > Q`.
   - It excludes `F_2 × F_2`, since `n/log n` grows faster than `n^(1−1/Q)`.
   - In particular the free group `F_2` (bounded sep) hosts, in this sense, only groups of bounded sep.
     Those are the virtually free groups (recalled: bounded sep for a Cayley graph forces a quasi-tree).
   - Conversely, every infinite virtually free group acts translation-like on `F_2`: `Z` by Seward's
     theorem, and the non-elementary ones by Whyte's bilipschitz theorem (both recalled).
3. **Decidable monsters force expander-carrying hosts.** Suppose `Γ` contains a coarsely, hence
   regularly, embedded family of expanders. Gromov monsters and Osajda's graphical small cancellation
   groups do, including the decidable examples tracked on main. Then `sep_Λ(n) ≳ n` along a sequence, so
   `Λ` itself contains expander-like pieces.
   - Farrell–Jones and `sep ≍ n` are compatible: directed colimits of hyperbolic groups satisfy
     Farrell–Jones with coefficients (Bartels–Echterhoff–Lück; recalled), and graphical small cancellation
     monsters are such colimits.
   - But those are not finitely presented, and the ring side needs `Λ` finitely presented
     (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`).
   - **Open meta-gate:** a finitely presented Farrell–Jones group with `sep ≍ n`, i.e. containing
     regularly embedded expanders. Without one, free realizations cannot host decidable monsters.
4. **The escape is non-free orbits.** Membership in `[[Λ ⋉ X]]` needs only a faithful action by
   bounded-displacement permutations of `Λ`-orbits; the proof of Theorem 2 there never used (T3) except
   for faithfulness.
   - With infinite point stabilizers the orbit maps are not regular, and Theorem 4 says nothing.
   - Precisely: `Γ` embeds in `[[Λ ⋉ X]]` for some free Λ-subshift `X` iff `Γ` acts faithfully on
     `Λ × N` by permutations preserving each copy of `Λ`, with uniformly bounded displacement.
   - ⇒: restrict to a countable dense set of orbits.
   - ⇐: encode each copy's action by move tables, drop (T3), and take the closure of the union of the orbit
     closures times a free `Y`. It is effectively closed when the action is computable.
   - So the right target for gate U is **which decidable groups embed in the uniformly bounded wobbling
     group of `Λ × N` for one fixed finitely presented Farrell–Jones `Λ`** (candidate `Λ = F_2 × F_2`),
     through actions whose Schreier graphs need not look like the input.

## Lesson for general BH

A fixed-scaffold host sees the input only through the Schreier graphs of its bounded-displacement action
on the scaffold. On free orbits those graphs are copies of the input's Cayley graph, so the input's
coarse geometry (growth, separation, expanders) must fit inside the scaffold. That kills every fixed
hyperbolic or low-separation scaffold as universal, and forces decidable monsters onto non-free orbits.
The design freedom that remains is to choose actions, with large stabilizers, whose Schreier graphs are
tree-like or product-like even when the input is not. Programming *those* Schreier graphs into the
subshift's language is the real content of gate U.
