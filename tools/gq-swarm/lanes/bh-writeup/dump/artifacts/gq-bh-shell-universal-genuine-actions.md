# Genuine-action shell envelopes (bh-shell-universal, 2026-09-18)

Lane bh-shell-universal of the BH swarm. Target: the universal shell route
(`decidable-inputs-have-fp-shell-envelopes`, `perfect-decidable-inputs-have-fp-shell-envelopes`).
All proofs are lane proofs, not independently reviewed; no priority claimed.

## 1. The observation

Every shell node on main builds `hat(g)` from the left regular action of `P` transported to `N`
by a bijection `nu`. None of the positive shell proofs uses regularity: the embedding, the germ
identification, the parity fiber product, the necessity of the germ tests, and the
independent-germ finite generation of stabilizers all use only that `rho: P -> Sym(N)` is an
action in which nonidentity elements have infinite support
(`genuine-action-shell-envelopes-generalize-the-regular-shell`).

The obstructions that do use regularity are exactly the ones that make one-ended inputs look
hard: `one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`,
`accessible-shell-inputs-admit-no-shift-normalizing-enumeration` (window `N >= 1`), and the
virtually cyclic cap in `shell-prefix-core-detects-finite-ray-enumerations`.

## 2. The positive family

`eventually-periodic-genuine-shell-actions-give-fp-envelopes`: if every `rho_g` is eventually
`m`-periodic (`rho_g(n+m) = rho_g(n)+m` for large `n`), the normal-core proof of
`virtually-cyclic-inputs-have-fp-shell-stabilizers` transfers verbatim. All finite `S(M,M')` are
finitely presented, so `E_rho` is finitely presented and `P` embeds in a finitely presented
simple group. Such actions exist exactly for finitely generated virtually abelian `P`
(interleaved zigzag copies of `Z`, induced up from a finite-index `Z^d`).

Worked one-ended example, `P = Z^2`: positions `2j` / `2j+1` are zigzag index `j` of copy 0 /
copy 1, and `(a,b)` translates copy 0 by `a` and copy 1 by `b`. Then
`s^-1 rho(a,b) s = rho(b,-a)` near infinity, so `R_rho ≅ Z^2 ⋊ Z` (rotation by a quarter turn),
polycyclic, with window `N = 0`. For comparison, the square-spiral regular enumeration passes the
window gate only with `N = 2`, and its near group is metabelian and not finitely presented.

## 3. Ceilings

- A central `<tau^k>` in the isotropy germ group happens exactly for eventually periodic
  actions, hence exactly for virtually abelian inputs.
- Twisted self-normalization `s^-1 rho(g) s = rho(phi(g))` near infinity with `phi` of finite
  order forces eventual periodicity, so virtually abelian. With `phi = id` it is impossible.
- With finitely many translated copies of `Z`, a twist must permute a finite set of characters
  up to sign. So hyperbolic twists (`Z^2 ⋊_A Z` with `A` Anosov) cannot be realized that way;
  heuristic, not landed.

## 4. What this changes for the universal route

`decidable-inputs-have-fp-genuine-action-shell-envelopes` (OPEN) replaces the regular
enumeration by an arbitrary genuine action with infinite supports, of any overgroup `P >= G`.
It is implied by the regular claim and implies Boone–Higman
(`boone-higman-via-genuine-action-shell-envelopes`). The necessary germ tests still bind:
`R_rho` must be finitely presented and pass the ascending HNN gate. But for inputs that are
not virtually abelian, the obstruction set is now only the one that does not depend on
regularity.

## 5. Open, in order of promise

1. **Infinite-order twists.** Find a non-virtually-abelian `P`, an injective endomorphism or
   infinite-order automorphism `phi`, and a genuine infinite-support action with
   `s^-1 rho(g) s = rho(phi(g))` near infinity. Then `R_rho` is the ascending HNN extension
   `P *_phi`, which is finitely presented when `P` is. Equivalently: a near action of `P *_phi`
   on `N` in which the stable letter is the single-ray shift and `P` acts genuinely.
2. **Beyond the normal core.** A finite-presentation proof of `S(M,M')` that does not divide
   by a central shift power. This is needed for anything not virtually abelian.
3. **Kazhdan inputs.** Whether a genuine infinite-support action of a group containing an
   infinite (T) subgroup can pass the window gate with `N = 0` and an infinite-order twist.
   The fixed-base exclusion (`fixed-base-shell-inputs-embed-in-odometer-rn-groups`) is about
   a different realization and does not settle this.
