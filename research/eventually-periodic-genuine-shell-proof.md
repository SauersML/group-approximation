---
rg: 2
id: eventually-periodic-genuine-shell-proof
kind: route
title: Divide the isotropy germs by a central shift power and use virtually abelian quotients, then build the actions from interleaved zigzags
target: eventually-periodic-genuine-shell-actions-give-fp-envelopes
requires:
  - genuine-action-shell-envelopes-generalize-the-regular-shell
  - virtually-cyclic-inputs-have-fp-shell-stabilizers
  - contracting-srn-rational-stabilizers-are-fp
  - germ-complex-and-bux-gonzalez-morse-inputs
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**The ambient group.** Let `G_m` be the group of near permutations `f` of `N` with
`f(n+m) = f(n) + m` for large `n`. On each residue class mod `m` (a ray) such an `f`
eventually maps the ray of `r` onto the ray of `pi(r)` by a translation. So
`G_m ≅ Z^m ⋊ S_m`, and the diagonal translation `tau^m` (all translations `1`) is central.

**Item 1.** If `rho` is eventually `m`-periodic, so is every `rho_g` (products preserve the
rule), and `rho'_g` (even part `2 rho_g(n)`, odds fixed) is eventually `2m`-periodic, as is
`tau`. So `Q_x ≅ Q_rho <= G_(2m)` and `C_x = <tau_x^(2m)>` is central in `Q_x`, for every
`x in Omega` (transport by `V`). This is the input of the normal-core argument in
`research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md` (the proof of
`virtually-cyclic-inputs-have-fp-shell-stabilizers`), which then runs verbatim:
- The joint germ map `S(M,M') -> prod_(x in M) Q_x/C_x × prod_(x in M' \ M) H_x/C_x`
  (`H_x = <tau_x>`) is onto, by the independent germ realization (item 4 of the
  generalization claim).
- Its image is a subgroup of a finite product of finitely generated virtually abelian
  groups, hence finitely generated virtually abelian, hence finitely presented.
- Its kernel consists of elements whose germ at each point of `M'` lies in `C_x`. Those are
  `V` germs, so the kernel lies in `V`; it is the finite-index subgroup of `Fix_V(M')` cut out
  by the germ map `Fix_V(M') -> Z^(|M'|)` modulo `2m`. `Fix_V(M')` is finitely presented
  (`contracting-srn-rational-stabilizers-are-fp` with trivial coefficients), so the kernel is.
- An extension of finitely presented groups is finitely presented.
Theorem 2.1 of Belk–Hyde–Matucci with `n = 2` (`V` has finitely many orbits on pairs of
`Omega`, being highly transitive) gives `E_rho` finitely presented; the same for `E_F`.

**Item 2.** If `<tau^k>` is normal then `rho'_g tau^k rho'_g^-1 = tau^(±k)`; near index forces
`+k`, so each `rho'_g` commutes with `tau^k` near infinity, i.e. is eventually `k`-periodic, and
then so is `rho_g` (read on evens). Conversely eventual periodicity makes `tau^(2m)` central.

**Item 3.** If `rho` is eventually `m`-periodic, `rho` induces a homomorphism `P -> G_m`
(near classes). It is injective because every `g != 1` has infinite support. So `P` embeds
in `Z^m ⋊ S_m` and is virtually abelian. Conversely, let `A ≅ Z^d` have finite index in `P`
(finitely generated virtually abelian groups are virtually `Z^d`). Let `Z^d` act on `Y`,
the disjoint union of `d` copies of `Z`, with the `i`-th coordinate translating the `i`-th copy.
Enumerate `Z` by the zigzag `0, 1, -1, 2, -2, ...`; a translation by `a` then acts on zigzag
indices eventually as `+2a` on odd indices and `-2a` on even ones. Interleave the `d` copies
(position `dj + i` is index `j` of copy `i`); every translation is eventually `2d`-periodic.
Induce to `P`: `X = P ×_A Y`, a union of `[P:A]·d` copies of `Z`, interleaved the same way.
An element of `P` permutes the copies and translates each; it is eventually `2d[P:A]`-periodic.
The induced action is faithful, and a nonidentity `g` either moves a copy (infinite support) or
lies in `A \ {1}` and translates some copy. If `P` is finite this is vacuous; `P` is infinite.

**Item 4.** `d = 2`, `P = A = Z^2`, positions `2j` (copy 0, zigzag index `j`) and `2j+1`
(copy 1, index `j`), `rho(a,b)` translating copy 0 by `a` and copy 1 by `b`. Then
`s: 2j -> 2j+1` sends the point `x` of copy 0 to the point `x` of copy 1, and
`s: 2j+1 -> 2j+2` sends `x` in copy 1 to `-x` (if `x > 0`) or `-x+1` (if `x <= 0`) in copy 0.
Conjugating: on copy 0, `s^-1 rho(a,b) s` translates by `b`; on copy 1, far out, by `-a`.
So `s^-1 rho(a,b) s = rho(b,-a)` near infinity. `R_rho` is a quotient of `Z^2 ⋊_phi Z`; it is
isomorphic to it because `eta(s^k rho(g)) = k` and `rho` is near-faithful.

**Item 5.** `s^-k rho_g s^k = rho_(phi^k(g)) = rho_g` near infinity, so `rho_g` commutes with
`s^k`, i.e. is eventually `k`-periodic; apply item 3. For `phi = id`, `rho_g` commutes with `s`
near infinity, so it is eventually a translation `n -> n + c`; genuine permutations have near
index `0`, so `c = 0` and `rho_g` is near-trivial, forcing `g = 1`.
