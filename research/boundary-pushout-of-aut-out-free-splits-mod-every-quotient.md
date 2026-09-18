---
rg: 2
id: boundary-pushout-of-aut-out-free-splits-mod-every-quotient
kind: claim
title: Modulo any nontrivial normal subgroup of the boundary full group, the pushed Aut/Out(F_n) extension splits over a finite-index subgroup; so no quotient obstruction, nilpotent or otherwise, can refute piecewise-representative lifts, and every point stabilizer of such a lift embeds in Aut(F_n) through germs
requires:
  - out-free-extension-pushed-into-the-boundary-full-group
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - aut-out-free-abelianized-extension-virtually-splits
distinct_from:
  fox-rational-section-fails-class-two-virtually: that obstructs lifts of Aut(F_n) → Out(F_n) through the class-two quotient F_n/γ_3; this shows that after pushing the kernel into the boundary full group M, every proper quotient of M is abelian, and the pushed extension splits virtually modulo it.
  out-free-acts-on-boundary-by-piecewise-representatives: that is the open existence statement (PR); this proves that every obstruction to it factoring through a quotient of the kernel vanishes, and it constrains the stabilizers of any solution.
  aut-out-free-abelianized-extension-virtually-splits: that is the abelian level of the original extension; this uses it to kill every quotient level of the pushed extension at once.
---

**ESTABLISHED** (lane proof, bh-outfn-2, 2026-09-18; short, from the cited nodes; not
reviewed; no priority claimed).

**Notation.** As in `out-free-extension-pushed-into-the-boundary-full-group`:
- `M = [[F_n ⋉ ∂F_n]]` and `H = M·Aut(F_n)`, with `M ∩ Aut(F_n) = Inn(F_n) ≅ F_n` and
  `H/M = Out(F_n)`, where `n ≥ 2`;
- `Γ_n` is the finite-index subgroup of `aut-out-free-abelianized-extension-virtually-splits`,
  over which `E_1 = Aut(F_n)/[F_n,F_n] → Out(F_n)` splits.

## Statement

1. **Every quotient splits.** Let `1 ≠ N ⊲ H` with `N ⊆ M`. Then `H/N → Out(F_n)` splits over
   `Γ_n`.
2. **Proper quotients of `M` are abelian.** `D(M)` is simple and perfect. So every nontrivial
   normal subgroup of `M` contains `D(M)`, and every solvable (in particular nilpotent)
   quotient of `M` factors through `M^{ab}`.
3. **Stabilizers lift.** Let `h` be a (PR) action of `Γ ≤ Out(F_n)` on `∂F_n`, and
   `ξ ∈ ∂F_n`. The germ map `q ↦ Ψ_{q,ξ}` of item 5 of the parent is an injective
   homomorphism `Γ_ξ → Stab_{Aut(F_n)}(ξ)` lifting the inclusion `Γ_ξ ≤ Out(F_n)`. Here
   `Γ_ξ` is the stabilizer of `ξ` under `h`. Hence:
   - (a) if `ξ` is fixed by no nontrivial element of `F_n`, then `Γ_ξ` lifts homomorphically
     to `Aut(F_n)`;
   - (b) if `ξ = (uwu^{-1})^∞` with `w` root-free, then `Γ_ξ` splits the relative extension
     `1 → Z → Aut(F_n, uwu^{-1}) → Out(F_n)_{[w]} → 1` over `Γ_ξ`;
   - (c) if some `h`-orbit is finite, then `Aut(F_n) → Out(F_n)` has a section over a
     finite-index subgroup.

So a (PR) action that is not already a virtual section has only infinite orbits. The
section problem is spread over the point stabilizers of a Cantor action, and no single
quotient of the kernel sees it.

## Proof

**Item 2.**
- `F_n ⋉ ∂F_n` is minimal, purely infinite and essentially principal. So by
  `matui-purely-infinite-minimal-full-groups-have-simple-d`, every nontrivial subgroup of `M`
  normalized by `D(M)` contains `D(M)`, and `D(M)` is simple.
- It is nonabelian, since it contains commutators of non-commuting transpositions of
  cylinders. So it is perfect.
- A solvable quotient `M/K` has `M^{(k)} ⊆ K` for some `k`. But `M^{(k)} = D(M)` for every
  `k ≥ 1`, so `K ⊇ D(M)`.

**Item 1.**
- `N` is normalized by `D(M)`, so `N ⊇ D(M)` by item 2, and `H/N` is a quotient of `H/D(M)`.
  It suffices to split `H/D(M) → Out(F_n)` over `Γ_n`.
- **Pushout form.** Since `H = M·Aut(F_n)` with `M ∩ Aut(F_n) = F_n`, `H` is the pushout
  `(M ⋊ Aut(F_n))/{(u^{-1}, c_u)}`. So `H/D(M)` is the pushout of `Aut(F_n)` along
  `F_n → M^{ab}`.
- `M^{ab}` is abelian, so that map factors through `F_n^{ab} = H_1(F_n)`, and `F_n` acts
  trivially on `M^{ab}`. Hence `H/D(M)` is the pushout of `E_1` along the Out-equivariant map
  `H_1(F_n) → M^{ab}`.
- `E_1` splits over `Γ_n`, and composing a section with `E_1 → H/D(M)` splits the pushout.

**Item 3.**
- For `q, q' ∈ Γ_ξ`, `h_{q'}` fixes `ξ`, so germs at `ξ` compose:
  `Ψ_{qq',ξ} = Ψ_{q,ξ}Ψ_{q',ξ}`. Each `Ψ_{q,ξ} ∈ q` fixes `ξ`. Injectivity holds because the
  class of `Ψ_{q,ξ}` is `q`.
- (a): `Stab_{Aut(F_n)}(ξ) ∩ Inn(F_n) = {c_u : uξ = ξ} = 1`, so the lift lands in a subgroup
  mapping injectively to `Out(F_n)`.
- (b): `Ψ(uwu^{-1})^∞ = ξ` forces `Ψ(uwu^{-1}) = uwu^{-1}` for root-free `uwu^{-1}`. The kernel
  of the relative extension is the centralizer `⟨c_{uwu^{-1}}⟩`.
- (c): the stabilizer of a point of a finite orbit has finite index. In either case the germ
  map is a homomorphism from it into `Aut(F_n)` lifting the inclusion, that is, a section.
  `∎`

**Scope.**
- Item 1 is a statement about quotient invariants only.
- It does not decide (PR), since `H` itself is the case `N = 1`.
- The Euler constraint of the parent (item 6) is an instance of 3(b) at the surface word. It
  is the one known obstruction-type input, and it uses germs, not quotients.

## Lesson for general BH

**Simple-kernel pushouts are quotient-blind.** Push a group extension into a kernel `M`
whose derived subgroup is simple and perfect, such as any purely infinite minimal full
group.
- Every quotient-level obstruction then collapses to the abelianized extension. For
  Aut → Out that extension splits virtually, so it gives nothing.
- Obstructions that kill virtual sections through nilpotent quotients (class two, the
  Johnson/Fox level) therefore cannot touch the pushed problem.
- What remains is purely dynamical. A strict model must avoid finite orbits (else it is a
  virtual section), and its point stabilizers must lift through germs.

For BH hosts this means: once the band is pushed into a V-type group, the only way to
refute a host is by fixed-point/germ arguments. The only way to build one is to spread the
section problem over the infinite stabilizers of a Cantor action. That is again "scale at
the emitter, do not sit there".
