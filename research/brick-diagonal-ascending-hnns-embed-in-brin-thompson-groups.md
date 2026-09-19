---
rg: 2
id: brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups
kind: claim
title: Renormalization compiler - every ascending HNN extension of a subgroup of kV along a brick diagonal embeds in (k+1)V
distinct_from:
  renormalizable-thompson-elements-give-baumslag-solitar: that is the case H = <T> cyclic with T an odometer of the code; this is every subgroup H of kV closed under the diagonal of any brick code, with the finite-equation interface and the permutation-twisted variant.
  renormalizable-thompson-elements-are-odometer-codes: that characterizes renormalizable single elements; this needs no odometer, only closure of a whole subgroup under one brick diagonal.
  f-infinity-tail-ascending-hnns-satisfy-boone-higman: that puts ascending HNN extensions of bounded automata groups into Rover-Nekrashevych type hosts with one new singular orbit; this puts ascending HNN extensions of subgroups of kV into the untwisted Brin-Thompson group (k+1)V, with no germ extension.
  dynamically-v-separated-groups-satisfy-boone-higman: that realizes an endomorphism as a cross-depth germ relation over V at one point; this realizes it as a global brick diagonal in one fresh coordinate.
---

**ESTABLISHED** through `brick-diagonal-ascending-hnn-embedding-proof`. Elementary lane proof
(bh-invent-08), not reviewed. No priority claimed: the conjugator is the one of
`renormalizable-thompson-elements-give-baumslag-solitar`, used for a whole subgroup.

**Setting.** `X = C^k`, `C = {0,1}^N`. An `m`-ary **brick code** (`m >= 2`) is a tuple
`e = (e_0, …, e_{m-1})` of brick-local homeomorphisms `e_i: X -> X_i` onto clopen sets with
`X = X_0 ⊔ … ⊔ X_{m-1}` (as in `renormalizable-thompson-elements-are-odometer-codes`). Its
**brick diagonal** is

  `δ_e: kV -> kV`,  `δ_e(h)|_{X_i} = e_i h e_i^{-1}`   ("apply h inside every piece").

`δ_e` is an injective homomorphism (`h = e_0^{-1} δ_e(h) e_0`).

**Theorem (compiler step).** Let `H <= kV` with `δ_e(H) ⊆ H`. Then

  `H *_{δ_e} = ⟨H, t | t^{-1} h t = δ_e(h), h ∈ H⟩  ↪  (k+1)V`,

by `h ↦ h × id`, `t ↦ g`, where `g(e_i x, y) = (x, c_i y)` for a complete binary prefix code
`c_0, …, c_{m-1}`. If `H` is finitely generated, so is the image.

**Corollaries.**
1. **Finite-equation interface.** Let `G` be a group with an injective endomorphism `φ`, and
   `ρ: G ↪ kV` faithful. If for a generating set `x_1, …, x_r` of `G` there is ONE brick code
   `e` with `δ_e(ρ(x_j)) = ρ(φ(x_j))` for all `j`, then `G *_φ ↪ (k+1)V`, so `G *_φ` embeds in a
   finitely presented simple group. Only finitely many identities between finite brick tables
   must be checked, and bh-free-18's lazy exhaustive DFS certifies such identities exactly.
2. **Universal diagonal extension.** `kV *_{δ_e} ≤ (k+1)V` for every brick code `e`, since
   `δ_e(kV) ⊆ kV`. So every direct limit `lim(H, δ_e)` of a `δ_e`-closed `H <= kV` sits in `(k+1)V`.
3. **Twisted codes.** The same holds when `e_i = ê_i ∘ π` with `ê_i` brick-local and ONE global
   coordinate permutation `π` of `C^k`. Then `H` may lie in `kV ⋊ Sym(k)`, and the image lies in
   `(k+1)V ⋊ Sym(k)`. That group is an extension of the finitely presented simple MIF group
   `(k+1)V` by a finite group. So by `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`, or by
   `fp-simple-highly-transitive-groups-satisfy-pbh` with `boone-higman-type-a-class-closed-under-finite-extensions`,
   every image satisfies permutational Boone–Higman.
4. **Calibration.** `H = ⟨T⟩` with `T` an odometer of `e` has `δ_e(T) = T^m`, and gives
   `BS(1,m) ≤ (k+1)V`, recovering `renormalizable-thompson-elements-give-baumslag-solitar` and, via
   `odd-smart-induced-map-has-height-m-renormalization`, `bs-1-m-embeds-in-brin-thompson-3v-for-odd-m`.

**Uses on main.** `monomial-renormalization-compiler-gives-dilation-groups-in-nv` (several odometers
under one code). The limit of the mechanism is `compiled-bs-stable-letters-are-never-rediagonalized`,
through `brick-diagonal-power-conjugacy-forces-zero-drift`.

**Lesson for general BH.** Renormalization in Brin–Thompson hosts is a *compiler*. It turns one
algebraic identity, "φ equals a brick diagonal on generators", into an ascending HNN extension at the
price of one fresh coordinate. It needs no germ analysis and no finiteness proof, because the host `nV`
is already finitely presented and simple.

So the embedding question for `G *_φ` becomes a finite design problem inside `kV`: realize `φ` as
"do `g` in every piece" for a single brick code. SMART_m is the first solution of such an equation
(`φ = ×m` on `Z`). The general problem is a *renormalization equation solver*: given finitely many
words `w_j`, find brick elements `x_j` and one code `e` with `δ_e(x_j) = w_j(x)`.
