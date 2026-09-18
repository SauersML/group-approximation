---
rg: 2
id: rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman-proof
kind: route
title: Lift through the binary coding, where non-dyadic rationals are periodic points and a dyadic slope at such a point is a whole number of period shifts
target: rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman
requires:
  - periodic-germ-extensions-of-v-are-virtually-simple
---

Let `q: 2^N → R/Z` be the binary coding. It is two-to-one exactly over the dyadic points, and
injective elsewhere.

1. **Thompson's `T`.** Maps of the form `θ ↦ 2^nθ + d` with dyadic breakpoints lift through `q` to
   prefix replacements. This is the standard picture of `T ≤ V`.
2. **Lifting.** Let `g ∈ PL_2(Q)`. On each arc between consecutive breakpoints, `g` is a dyadic
   affine map `α_i`.
   - Lift on small dyadic subintervals of each arc, as for `T`. The arcs themselves may have non-dyadic
     endpoints.
   - At a non-dyadic rational breakpoint `s` the preimage is one point `p`, and the two one-sided
     lifts extend continuously to it.
   - This gives the unique homeomorphism `ĝ` with `qĝ = gq`, and `g ↦ ĝ` is an injective
     homomorphism.
3. **Periodic points.** Write `s = r/(2^a b)` with `b > 1` odd. Its binary expansion is eventually
   periodic with primitive period length `ℓ = ord_b(2) >= 2`. Dyadic affine maps preserve the tail of
   the expansion. Since `bp(gh) ⊆ bp(h) ∪ h^{-1}bp(g)`, every breakpoint of an element of a finitely
   generated `H` lies in the `H`-orbit of a generator's breakpoint, hence in finitely many tail classes, and `Π` is chosen to be their set of periods.
4. **Germs.** Let `p = uv^∞` lie over a non-dyadic breakpoint `s`, with left piece `α_-` and right
   piece `α_+`. The map `α_-^{-1}α_+` fixes `s` and has the form `θ ↦ 2^c θ + d`, with `d` dyadic.
   - Then `d = s(1 - 2^c)` is dyadic, which forces `ord_b(2) = ℓ` to divide `c`.
   - Write `c = ℓm`. Near `s`, the map `θ ↦ s + 2^{ℓm}(θ - s)` sends the dyadic interval of the cone
     `uv^{K+m}` onto that of `uv^K`. So its lift near `p` is the prefix replacement
     `uv^{K+m}ζ ↦ uv^Kζ`, a diagonal shift of the side cones by `-m`.
   - Dyadic affine maps change only finitely many binary digits of a non-dyadic point: the carries
     stop, because the expansion does not end in `1^∞`. So the breakpoint images stay in the tail
     class of `s`.
   - As in `quadratic-breakpoint-psl2z-groups-satisfy-boone-higman-proof`, step 4, the coding is
     order-preserving. So `ĝ` is, near `p`, a prefix-replacement germ composed with a shift of the
     right families. That is admissible with `π = id`.
5. **Conclusion.** Every `ĥ`, for `h ∈ H`, lies in `G_Π`. By
   `periodic-germ-extensions-of-v-are-virtually-simple`, `H` embeds in the finitely presented simple
   group `G_Π'`. ∎
