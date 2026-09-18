# Adversarial check: vertex-free Ã₂ groups satisfy Boone–Higman (bh-refute, 2026-09-18)

Rotation item 3 (bh-groupoid 3cb525018). The target is `type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups`,
the case that completes `vertex-free-type-rotating-a2-groups-satisfy-boone-higman`.

Verdict: **PASS**. I re-derived every step of the type-preserving proof. I spot-checked its inputs:
- `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`: its phase bookkeeping;
- `a2-group-embeds-in-rs-two-graph-geometric-proof`: its cylinder-exchange step;
- `primitive-two-graph-fp-simple-embedding-proof`: its Steps 1–3, which this proof reruns.

None of these inputs is refereed on main.

## Steps re-derived

1. **Phase and degree.**
   - A tile's phase is the cotype of its diagonal.
   - A colour-1 successor `(C_2, C_3)` has diagonal `π_{τ+1}(C_2)`, so `M_1` raises the phase by 1. `M_2`
     raises it by 2.
   - Irreducible of period 3 means `M_j^3` is block-diagonal with primitive blocks (Perron–Frobenius).
   - Paths between phase classes exist in every large degree `(a,b)` with the forced `a + 2b mod 3`: a
     colour-1 path, then a colour-2 path.
2. **The cocycle lies in `L` on `X_0`.** If `x(0), y(0)` have phase 0 and `σ^p x = σ^q y`, then
   `p_1 + 2p_2 ≡ q_1 + 2q_2 (mod 3)`, so `p − q ∈ L`. `Γ` sits in `[[G_Λ|_Y]]` with `Y ⊆ X_0`, since the
   decorations are based at `O` of type 0.
3. **Rescaling.** `n = 3m` puts `nZ² ⊆ L`. `M_j^n(a,a) >= 2` holds for large `m`, and `G_{Λ^(n)} ≅ c^{-1}(nZ²)`.
4. **Skew product over `T = L/nZ²`.** `c̄` is well defined because `c(G_Λ|_{X_0}) ⊆ L`. The isomorphism
   `H|_{X_0×{0}} ≅ G_{Λ^(n)}|_{X_0}` and the embedding `f ↦ f × T` are as in the reference Step 2.
5. **Compression. This is the one genuinely new check.**
   - We need `σ_{v,a}`, from `s(ρ_{v,a})` to a phase-0 vertex `v`, with `d(σ) ≡ −a − R (mod nZ²)` and
     `d(σ) >= (K,K)`.
   - Since `3 | n`, a class mod `nZ²` fixes `a_1 + 2a_2 mod 3`.
   - The phase condition for `λ = ρσ` (from phase 0 to phase 0) is `R + d(σ) ∈ L`, and `−a ∈ L`.
   - So the required class is compatible with the phase constraint, and step 1 supplies a large
     representative.
   - Then `b + c̄(ψ_{v,a}) = a + d(λ) ≡ 0`, which is correct. With `R` large there are `> |A_0|·|T|` range-phase-0
     paths of degree `R`, leaving one over.
6. **`F_∞`.**
   - Li's `thm:k-graphs` allows `Y_v ∈ {∅, Z(v)}`, so the phase-0 union is admissible.
   - It needs `>= 2` loops of each colour at *every* vertex of `Λ'`, including phases 1 and 2. This holds
     because `M_j^n(a,a) >= 2` for all `a`.
   - It does not need strong connectivity, which fails here: `Λ^(n)` splits by phase.
7. **Minimal and purely infinite.** These are needed only inside `Y'`. Degrees in `nN²` preserve phase, and the
   phase-0 block of each `M_j^n` is primitive, hence strongly connected.
8. **Homology and simplicity.**
   - `G_{Λ'}|_{Y'} = G_{Λ^(n)}|_{X_0} × G_2`.
   - The Künneth vanishing, Li's AH sequence and Matui apply to the restricted, minimal, purely infinite,
     essentially principal groupoid.

## Attacks tried (all failed)

- **Li's theorem needing strong connectivity or a single vertex class.** It needs neither (TeX l.2124).
- **The skew product being ill-defined off `X_0`.** It is only formed on `X_0`, which is the point of step 2.
- **Too few range-phase-0 paths for compression.** Their number grows like `q^{2|R|}`.

## Lesson for general BH

Periodicity of transition matrices is not an obstruction to the primitive-graph embedding theorem. Restrict
to one cyclic class and replace `Z^k` by the sublattice `L` of class-preserving degrees, taking the skew
product over `L/nZ^k`. So "primitive" can be weakened to "irreducible" in every k-graph host route, which
removes a standing hypothesis from the whole Robertson–Steger family.
