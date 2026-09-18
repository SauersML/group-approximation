# Adversarial check of the Kourovka 17.57 chain (bh-free-43, 2026-09-18)

**Question** (Kourovka 17.57, S. Kohl): is `Out(CT(Z)) = ⟨n ↦ −n−1⟩ ≅ C_2`?

**Chain checked** (all on origin/main):
1. `out-ct-z-is-c2-iff-normalizers-are-somewhere-affine` (6a982abc9): reduction to local rigidity.
2. `ct-z-normalizers-are-2-and-3-regular` (547c68708): 2- and 3-regularity, then the conclusion.
3. `bell-generalized-cobham-theorem` (+ `-citation`, 0997abd2a): Bell's Theorem 1.4, read at source.
4. The Fatou–Kronecker step (inside node 2, §3).

**Verdict: PASS.** Every step was re-derived below, except the cited theorems listed at the end. I found no gap
in the two places I was asked to hunt, the quasi-polynomial ⇒ affine step and the flip normalization. Two
wording fixes are listed. This is a lane check, not an external review. The chain also rests on two upstream
lane proofs, `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` and item 3 of
`ct-p-z-is-a-one-vertex-k-graph-full-group`, which I did not re-check.

## 1. The reduction (node 1)

- **CT(Z) = F := [[G]].** Here G is the germ groupoid of canonical box maps on `Ẑ = ∏_p Z_p` (all primes). By
  the 17.59 node, every element of CT(Z) is piecewise canonical with finitely many pieces, and every
  piecewise-canonical permutation of Z fixing `N_0` lies in CT(Z). Restriction to the dense orbit `Z` is
  faithful. So `CT(Z) = [[G]]` as groups of homeomorphisms of `Ẑ`. This is upstream, not re-checked here.
- **Spatial.** I read the statements at source in `gq/src/kep/matui-1210.5800.tex`:
  - Theorem `spatial` (line 679): an isomorphism between class-F subgroups of Homeo of Cantor sets is
    conjugation by a homeomorphism.
  - Proposition `tfg=F` (line 772): if G is essentially principal, minimal and étale with Cantor unit space,
    every Γ with `D([[G]]) ⊆ Γ ⊆ [[G]]` is of class F.

  Checked for G on `Ẑ`:
  - Étale with Cantor unit space.
  - Minimal: every x lies in a box that some canonical map carries onto any given box.
  - Essentially principal: a canonical affine map that is the identity on an open set is the identity, and
    isotropy occurs only at countably many points.

  Purely infinite is not needed for these two results. The trivial-centralizer argument (an involution
  supported in A with ψ(A) ∩ A = ∅) is correct. So `Out(CT(Z)) ≅ N/F`. **PASS.**
- **φ(Z) = Z.** I checked this directly rather than through the cited Step 2.
  - A non-identity canonical germ z ↦ r + (m/m')(z − r') with a fixed point has m ≠ m'.
  - Its fixed point is (m'r − mr')/(m' − m) ∈ Q, and `Q ∩ Ẑ = Z`.
  - Every integer n has a nontrivial germ: use B(n, m) → B(n, m') for n ≥ 0, and
    B(n + m, m) → B(n + m', m') for n < 0, with m, m' > |n| and m ≠ m'. Then extend by a canonical
    patchwork on the complements; any two nonempty clopen sets are finite unions of boxes, and boxes split.
  - Conjugation by φ ∈ N preserves "nontrivial germ group".

  **PASS.**
- **φ(N_0) ∈ {N_0, Z_{<0}}.**
  - Canonical maps send r' + tm' ↦ r + tm with the same t, and t ≥ 0 iff the point is nonnegative. So F
    preserves `N_0`.
  - Class transpositions of large modulus are transitive on `N_0` and on `Z_{<0}`.
  - φ permutes F-orbits and fixes Z setwise.

  **PASS.**
- **The flip normalization.**
  - σ(r' + tm') = (m' − 1 − r') + (−t−1)m', so σ conjugates every canonical box map to a canonical box map.
    Hence σ ∈ N.
  - σ(N_0) = Z_{<0}, so σ ∉ F. Also σ² = 1.
  - If φ(N_0) = Z_{<0}, then σφ ∈ N fixes `N_0`. So N = F ⊔ σF and N/F = ⟨σF⟩ ≅ C_2, provided every
    N_0-fixing φ ∈ N lies in F.

  **PASS.**
- **(b) ⇒ (c) ⇒ (a).**
  - Suppose φ is affine on one box. For any x, minimality gives g ∈ F with g(x) in that box. Then
    φ = (φgφ^{-1})^{-1} ∘ φ ∘ g is affine with rational coefficients near x.
  - By compactness φ is piecewise affine on a finite box partition, so φ|_Z is residue-class-wise affine.
  - With φ(N_0) = N_0, the 17.59 node (steps 1–3: positive slopes, images are classes, zero shift) gives
    φ|_Z ∈ CT(Z).
  - Z is dense in Ẑ, so φ ∈ F.

  **PASS.** Item 3 of node 1 (germ groups fixed pointwise, via the 17.60 node) is not used by the conclusion,
  as node 2 says.

## 2. Regularity (node 2, items 1–2)

- **Dilations.** z ↦ bz + e is the canonical map B(r, b) → B(br + e, b²), since br + e ≤ b² − 1. It extends
  to g ∈ F by a canonical patchwork on the complements. **PASS.**
- **Recursion.**
  - h = φgφ^{-1} ∈ F is piecewise w ↦ A_i + B_i w with B_i ∈ Q_{>0}, and A∘φ, B∘φ are locally constant on Ẑ.
  - A locally constant function on Ẑ is uniformly so by compactness, hence factors through Z/P. So α and β
    are P-periodic on `N_0`.
  - For k ∈ N_0: Φ(bk + e) = h(Φ(k)) = β(k)Φ(k) + α(k).

  **PASS.**
- **b-regularity over Q.**
  - Write r = b r'' + e. Then Φ(b^j n + r) = β(b^{j−1}n + r'')Φ(b^{j−1}n + r'') + α(·), and n ↦ β(b^{j−1}n + r'')
    is P-periodic.
  - By induction every kernel sequence lies in W = {χΦ + χ' : χ, χ' P-periodic}, a Q-space of dimension ≤ 2P.
  - So `M_Q(Φ; b)` is finite-dimensional, i.e. Φ is (Q, b)-regular in Bell's Definition 1.2, for b = 2 and
    b = 3.

  **PASS.**
- **Growth.** |Φ(bk+e)| ≤ M|Φ(k)| + M gives |Φ(n)| ≤ C n^{log_b M}. **PASS.**

## 3. Bell and Fatou–Kronecker (node 2 §3, node 3)

- **Bell's Theorem 1.4.** With R = Q, k = 2, l = 3 (multiplicatively independent), it gives a linear
  recurrence over Q. Its hypotheses match exactly: R commutative, and regularity is finite generation of
  M_R(Φ; k).
  - Note: Bell's Theorem 1.5 (the integer-valued form) would need (Z, k)-regularity. That is not shown: a
    Z-submodule of a finite-dimensional Q-space need not be finitely generated.
  - Node 2 correctly takes the Q route: Theorem 1.4, then Fatou–Kronecker. **PASS.**
- **Fatou–Kronecker.**
  - Fatou's lemma: an integer power series that is rational equals p/q in lowest terms with p, q ∈ Z[x],
    q(0) = 1.
  - Polynomial growth gives radius ≥ 1, so all poles α have |α| ≥ 1.
  - The reversed polynomial x^d q(1/x) is monic in Z[x] with roots 1/α in the closed unit disk, and nonzero.
    By Kronecker they are roots of unity.
  - Partial fractions then make Φ eventually a quasi-polynomial, with period N the lcm of the orders.
  - On each class, a polynomial over Q(ζ_N) taking rational values at infinitely many points has rational
    coefficients, by interpolation.

  **PASS** (textbook inputs, not re-read).

## 4. Quasi-polynomial bijection ⇒ affine on a box (node 2 §3)

- Φ(n) = p_i(n) on n ≡ i mod N, n ≥ n_0.
- **deg p_i = 0 is impossible:** a constant on an infinite class contradicts injectivity.
- **Leading coefficients are positive:** Φ takes values in `N_0`.
- **Some class has degree 1.** If every deg p_i ≥ 2, then #{n : Φ(n) ≤ Y} ≤ n_0 + Σ_i O(√Y) = O(√Y). But Φ is
  a bijection N_0 → N_0, so this count is Y + 1.
- So some class has Φ(n) = an + c with a ∈ Q_{>0}.
- **Extension to the box.** {n ≥ n_0 : n ≡ i mod N} is dense in B(i, N), because N_0 meets every residue
  class mod every M. φ and z ↦ az + c are continuous into A_f = Ẑ ⊗ Q and agree on a dense set, so they are
  equal on B(i, N). That is (b) of node 1, with C = a ≠ 0.

**PASS.**

## 5. Fixes to make (wording only; the mathematics is unchanged)

- Node 2 item 3 can drop **CONDITIONAL**. It should require `bell-generalized-cobham-theorem`, and the
  citation should read "Sém. Lothar. Combin. **54A** (2006), Art. **B54Ap**" (not "55 (2005/07), B55f").
- Node 1 cites Step 2 of `ct-p-z-groups-are-pairwise-nonisomorphic` for "nontrivial germ ⇔ integer". The
  two-line argument in §1 above is self-contained and could replace the pointer.

## 6. Trust surface

- **Read at source:**
  - Matui 1210.5800, Theorem `spatial` and Proposition `tfg=F` (statements only);
  - Bell SLC 54A B54Ap, Theorem 1.4 and Definitions 1.2–1.3 (statements only).
- **Textbook, not re-read:** Fatou's lemma and Kronecker's theorem.
- **Upstream lane proofs, not re-checked here:**
  - `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` (its steps 1–3 were re-derived above; step 4
    uses the next node);
  - `ct-p-z-is-a-one-vertex-k-graph-full-group`, item 3, whose citations are FKPS, Li and Matui.

  These are where the remaining risk sits.
- **Priority** was not checked here; bh-kourovka reports the 2026 notebook lists 17.57 as open.
