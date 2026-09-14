# sk-exchange part 1: local membership, clean elements, and where the naive gluing fails (2026-09-14)

Lane sk-exchange. Problem: is `R = LC(X,F) ⋊_T Z`, for a minimal Cantor homeomorphism `T` and a field `F`, an exchange ring? By sk-algebraic-putnam (reviewed by sk-verify-16), a yes gives `sr(R) = 1`. This part proves one membership lemma, records two reductions, and shows exactly where the natural gluing scheme breaks, with a worked repair of one failing configuration. Everything is unreviewed.

Notation: `(fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}`. The orbit representation at `ξ` is `V_ξ = F^{(Z)}`, `fδ_t = f(T^tξ)δ_t`, `uδ_t = δ_{t+1}`, so `a = Σf_ju^j` has entries `a(m,n) = f_{m−n}(T^mξ)`. A Kakutani–Rokhlin partition `𝒫` has cuts at base positions, and `A_𝒫 ≅ ∏_aM_{h_a}(F)` is its tower algebra of block-diagonal elements.

## 1. Lemma L (local membership), established
**Statement** (node `cantor-crossed-product-right-ideal-membership-is-local`). `z ∈ aR` iff there is `ρ` such that every column `zδ_t` of `z` has an `a`-preimage supported in `[t−ρ, t+ρ]`, in every `V_ξ`. Equivalently, each column has some finitely supported preimage; compactness makes the radius uniform.

**Proof** (route `…-proof`).
- Choose one preimage per window type (finitely many types).
- Assemble the coefficients into `r = Σ(η_n∘T^{−n})u^n ∈ R`.
- Covariance `V_ξ ≅ V_{T^tξ}` then gives `ar = z` in the faithful representation.

**Use.** An idempotent `e` is an exchange witness for `a` iff the columns of `e` and of `1−e` have local preimages under `a` and `1−a`. This is the test used in §§3–4.

## 2. Clean elements are suitable (elementwise), a standard reduction
If `a = e + g` with `e² = e` and `g ∈ R^×`, then `f := g(1−e)g^{−1}` is idempotent, `f ∈ aR` and `1−f ∈ (1−a)R`.
- *Proof.* `a(1−e) = g(1−e)`, and `(1−a)e = e − e − ge = −ge`, so `1−f = geg^{−1} ∈ (1−a)R`. ∎
- This is the element version of "clean ⇒ exchange" (Nicholson, Trans. AMS 229 (1977); the proposition number is not checked at source).
- Han–Nicholson, Comm. Algebra 29 (2001) 2589–2595 (abstract checked): if `eRe` and `(1−e)R(1−e)` are clean then `R` is clean. For `R` the corners over clopen sets are again minimal Cantor crossed products, so this alone is circular.

## 3. Square-zero cut correction, a sufficient condition for cleanness
Let `a` have propagation `w`. Choose `𝒫` with heights `h ≥ L ≫ w`, refined so that the local data of `a` determine the atoms.
- Write `a = D + N`. Here `D ∈ A_𝒫` is the block compression, and `N` holds the entries `a(m,n)` with `m, n` in different blocks.
- Then `N` kills every coordinate at distance `> w` from all cuts (the interior `Int`) and maps into the boundary windows `Bd`.

**Proposition Q.**
- *Statement.* Suppose `f ∈ A_𝒫` is idempotent and `g := D − f ∈ A_𝒫^×` satisfies `g^{−1}(Bd) ⊆ Int` on every block. Then `a` is clean, hence suitable.
- *Proof.* `(g^{−1}N)² = 0`: `Nv ∈ Bd`, so `g^{−1}Nv ∈ Int`, so `N(g^{−1}Nv) = 0`. So `a − f = g(1 + g^{−1}N)` is a unit, with inverse `(1 − g^{−1}N)g^{−1} ∈ R`. ∎
- *Refinement.* It is enough that `g^{−1}(im N) ⊆ ker N` blockwise, or more generally that `g^{−1}N` is nilpotent of bounded order.

**Block Lemma (needed for all block types).**
- For the compression `C ∈ M_h(F)` of a block, with windows `W` (`dim m = 2w`) and interior `Int` (`dim n = h − m`), there should be an idempotent `Φ` with `g = C − Φ` invertible and `g^{−1}(W) ⊆ Int`.
- *Necessary form.* `g^{−1} = [[P,Q],[S,0]]` in `Int ⊕ W`. So `g_{21}Q = I_W` and `g_{11}Q = 0`: some `S := Q(W) ⊆ Int` of dimension `m` is mapped by `g` isomorphically onto `W`, and killed by `g_{11}`.
- *Construction attempt.*
  - Choose `S ⊆ Int ∩ ker C_{21}` with `dim S = m`; there is room once `n ≥ 2m`. Choose an iso `β : S → W`, and put `Φ|_S = C|_S − β`.
  - `Φ(S)` has `W`-components `−βs ≠ 0`, so `S ∩ Φ(S) = 0` and `Φ|_S` is injective. `Φ` extends to an idempotent: the identity on `Φ(S)`, any idempotent `ψ` on a complement `R_0` of `S` in `Int`.
  - Then `g(S) = W`, and `g` is invertible iff `Λ : R_0 ⊕ S → Int`, `(r,s) ↦ (C_{11} − ψ)r + (C_{11}² − C_{11} − C_{12}β)s`, is bijective.
- *Degree of freedom.* Choosing `ψ` with `(C_{11} − ψ)|_{R_0}` invertible (possible, since matrix rings over fields are clean) reduces bijectivity of `Λ` to an `m×m` Schur complement `Σ(β) = X − C′_{12}β`.

**Where it fails.** For `C = 0`, and for `C = 1`, the `s`-columns of `Λ` vanish (`C_{11}² = C_{11}`, `C_{12} = 0`). No choice works. In fact invertibility of `C − Φ` forces `Φ = 1` or `Φ = 0`, so `g^{−1}(W) = W`. This happens over every field. Over `F_2` every scalar block is of this kind.

## 4. A repair: pieces straddling the cuts
- *Example.* Over `F_2` let `a` be the identity except on 2-dimensional windows straddling the cuts, where `a` acts by `J = [[1,1],[1,1]]`. With the pieces fixed at the cuts, the compressions are `1` and the couplings are nonzero, so the Block Lemma fails.
- *Repair.* Use the window pieces themselves as blocks, so `a` has no couplings. Take `f = 1` on the windows and `0` inside. Then `a − f` is `[[0,1],[1,0]]` on each window and the identity inside, a unit with banded inverse. So `a` is clean.
- *Lesson.* Where the pieces go matters. The failing configurations are those where `a` is locally idempotent near a piece boundary while coupling across it. Where `a` is locally idempotent, `e = a` is already a local witness.

## 5. Next steps
- **H1, hybrid gluing.** Combine Proposition Q on pieces where the Schur complement `Σ(β)` can be made invertible with local witnesses `e = a` where `a` is locally idempotent. Glue at the interfaces with sk-algebraic-putnam's one-cut Laplace splitting (Theorem DP), which already handles idempotents.
- **H2, adaptive boundaries.** By minimality, each local type of `a` recurs in bounded gaps. So piece boundaries can be placed at levels of a chosen type. Classify the boundary types for which `Σ(β)` can be made invertible, and show that every `a` has one.
- **H3, odometer test case.** `R_odo = ⋃_kM_{2^k}(F[t^{±1}])`. After passing up levels, `a = A_0 + tA_1 + t^{−1}A_{−1}` with low-rank corner couplings, and cleanness at a level means `det(a − Φ) ∈ F^×t^Z` for a constant idempotent `Φ`. Test the H2 classification there first.

## 6. Search bound
- Three web searches: Steinberg algebras and exchange rings; algebraic crossed products of minimal Cantor systems with exchange or stable rank; Han–Nicholson corner theorem.
- No algebraic exchange or clean theorem for these rings was found.
- The C*-level results do not transfer exactly: Putnam; Archey–Phillips arXiv:1505.00725; Phillips math/0408291; arXiv:2008.03361.
