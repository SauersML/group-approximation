---
rg: 2
id: locally-indicable-packets-have-zero-schur-kernel
kind: claim
title: A nonsingular equation kills no Schur class that survives in a locally indicable image, whatever its shape
distinct_from:
  amenable-t-shape-adjunctions-kill-no-schur-class: that allows any torsion-free coefficient packet but needs an amenable t-shape; this has no shape hypothesis but needs local indicability, or a locally indicable image that sees the class.
  amenable-coefficients-have-zero-schur-kernel: that uses matrix approximation of twisted algebras of amenable packets; this uses Howie's cohomology decomposition, with no approximation input.
  nonsingular-coefficient-kernel-in-locally-indicable-residual: that bounds the degree-zero coefficient kernel by locally indicable quotients; this is the degree-two analogue for the Schur kernel.
artifacts:
  - research/artifacts/sp4-schur-li-packets-2026-09-17.md
---

Let `Q` be a group, `w in Q * <t>` with `deg_t(w) != 0`, and
`K_2(Q, w) = ker(H_2(Q) -> H_2((Q * <t>)/<<w>>))`.

1. If `Q` is locally indicable, then `K_2(Q, w) = 0`.
2. For every homomorphism `phi : Q -> L` with `L` locally indicable,
   `K_2(Q, w) <= ker(phi_* : H_2(Q) -> H_2(L))`.
3. If the coefficient subgroup `B` of `w` is locally indicable, then
   `K_2(Q, w) = 0`. More generally, `K_2(Q, w)` lies in `iota_*` of the
   intersection of `ker phi_*` over all homomorphisms `phi : B -> L` to locally
   indicable groups.
4. *p-local form.* Let `p` be a prime. Suppose `B` has a finite normal subgroup
   `A` of order prime to `p` with `B/A` locally indicable, and that
   `B -> (B * <t>)/<<w>>` is injective. Then every element of
   `K_2(Q, w)` has finite order prime to `p`. So every `Z/p`-valued multiplier
   vanishes on `K_2(Q, w)`.

None of these needs a hypothesis on the `t`-shape.

**Consequence for `sp4-schur-kernel-meets-the-deligne-triple-class`.**

- The coefficient packet `B <= Sp_4(Z)` of a witness is not locally indicable.
  So it is not a surface group, a free-by-cyclic group, a torsion-free
  one-relator group, and so on.
- Nor is `B` locally indicable modulo a finite normal subgroup of order prime
  to 3, such as `<-I>` or a normal 2-subgroup, provided `B` injects into the
  adjunction. By `nonsingular-coefficient-kernel-in-locally-indicable-residual`,
  that kernel lies in the finite normal subgroup. Whether it is trivial is
  open here. The Klyachko--Mikheenko GR-by-locally-indicable theorem pinned
  in `research/artifacts/hl-kl-howie-overlap-2026-09-14.md` would give it, but
  it is not a node.
- The killed Maslov-detected class is invisible in `H_2` of every locally
  indicable image of `B`.
- If `B` is torsion-free, the shape of `w` must be non-amenable.

Every attempt that builds the witness from a locally indicable Maslov packet
dies at one step. By Howie's restriction epimorphism, the Deligne multiplier
restricted to `B` extends over `(B * <t>)/<<w>>`.
