# Referee report (citation/hypothesis lens): `resolvent-vacuum-rings-have-no-k0-state` and the OPEN `fp-simple-resolvent-ring-with-divisible-unit-class`

Referee: lane gq-referee-b, 2026-09-18. Reviewed: both nodes as landed at b936655b4 (gq-ring-fp-simple).

## Verdict

**PASS** for the lemma and for the OPEN node's "Necessary shape" list, with four amendments (W1–W3, A1). One of
them, W3, is a convention error that decides whether the example works.

## 1. The lemma

**Definition of a state.** The node uses: an additive `f : K_0(R) → R` with `f >= 0` on the image of `V(R)` and
`f([1]) = 1`. This is the standard state on the pre-ordered group with order unit `(K_0(R), V(R), [1])`
(Goodearl), and it is how the repo uses "state on V(R)", for example in `algebraic-tarski-for-steinberg-algebras`.
`K_0` need not be partially ordered, and the definition does not need it. **Consistent.**

**§1 orthogonal copies. Correct.**
- `P_m^2 = x_m E y_m = P_m`.
- `(λ_{m'} − λ_m) y_m x_{m'} = 0`, and the difference is a non-zero-divisor, so `P_mP_{m'} = 0`.
- `x_m·` and `y_m·` are mutually inverse maps `ER ⇄ P_mR`.
- `R = ⊕_{i<=M} P_iR ⊕ (1−ΣP_i)R` gives `M[E] <= [1]`.

**§2 full vacuum. Correct.**
- `1 = Σ a_iEb_i` makes `(ER)^k → R` a split surjection, so `[1] <= k[E]`.
- `M = 2k` gives `2k f([E]) <= 1 <= k f([E])`, so no state exists.
- Not stably finite: `P ≅ P ⊕ P ⊕ Y ⊕ Z` with `P ≠ 0`, so `End(P) = eM_k(R)e` is not directly finite.
- A corner of a directly finite ring is directly finite. I checked this: if `ab = e`, then
  `(a+1−e)(b+1−e) = 1`.

**§3 instances. Correct.**
- `R_L`:
  - `y_mx_m = 1`;
  - `Nx_m = (m−1)x_m`, via `Ns_2 = 0`;
  - `y_mN = (m−1)y_m`, via `t_1N = (N+1)t_1` and `t_2N = t_2s_1(N+1)t_1 = 0`.
- `R_k`: the same, with `N s_v = s_vσ_v(N) = 0` and `t_vN = 0`.
- The finitely presented Toeplitz ring: `E` is not full, and the node applies only part 1 to it, correctly.

**Consequences.**
- `[1]` of infinite order excludes Leavitt `(1,d)`-tuples, since they give `R ≅ R^d`, so `(d−1)[1] = 0`.
  **Correct.**
- "No stably finite, UHF, Bratteli or traced model" for a finitely presented simple ring whose `Q` comes from a
  resolvent vacuum. **Correct**, given W2.
- "Of the type `O_∞ ⊗ UHF_Q`" is a heuristic description, not a theorem. Say so.

**W1 (name clash).** The instance list calls the finitely presented Toeplitz ring of
`q-embeds-in-a-corner-of-a-fp-toeplitz-ring` "`R_T`". On main, `R_T` is the `SL_3(Z)` Toeplitz harmonic ring of
`sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`, which is tracial. By this very lemma it has **no** full
resolvent vacuum; it gets `Q` by harmonic elimination instead. Rename the instance, for example to `R_Toep`, so no
reader applies the lemma to the tracial ring.

**W2 ("trace").** A trace `τ` gives a state only if `τ(e) >= 0` for idempotents `e` of every `M_n(R)`. That is
automatic for positive traces on `*`-algebras evaluated on projections. It is not automatic for arbitrary
idempotents in an algebraic ring. Say "no trace nonnegative on idempotents of matrix rings, and no dimension
function, normalized at `1`".

## 2. The OPEN node's "Necessary shape"

- **Stateless and not stably finite.** Follows from the lemma: condition 1 plus simplicity make `E` full.
- **Not a unital Leavitt–Nekrashevych completion.** `O_ψ ⊇ L_d` unitally, so `(d−1)[1] = 0`, which contradicts
  condition 4. **Correct.**
- **Not a finite graph algebra over such a base.**
  - For finite `E`, `K_0(L_k(E)) = coker(1 − A^t : K_0(k)^{E^0∖Sink} → K_0(k)^{E^0})`. This is ABC Thm 7.6,
    verbatim in `abc-leavitt-path-k-theory-exact-sequence`.
  - **A1.** The formula needs `k` regular supercoherent: ABC's hypothesis, true for fields and Noetherian regular
    rings. "Coefficients with finitely generated `K_0`" alone is not enough to invoke it. Add the hypothesis.
  - Given it, the coker is finitely generated.
  - An element of `Z^r ⊕ T` divisible by every `n` has zero free part, so it is torsion.
  - Condition 3, `R ≅ M_n(R_n)`, forces `[1] = n[e_n]` for every `n`, so it fails whenever `[1]` has infinite order.
  - **Correct.**
- **W3 (convention, load-bearing for the example).** For `A = [[3,1],[2,2]]`:
  - **With `A_ij = #` edges `i → j`**, the vertex relations are `[v_i] = Σ_j A_ij[v_j]`. The relators `e_i − Σ_j A_ij e_j`
    are `(−2,−1)` and `(−2,−1)`, with image `Z(2,1)`. Then `K_0 ≅ Z` via `(a,b) ↦ a − 2b`, and `[1] = (1,1) ↦ −1` is a
    generator. **The claim holds.**
  - **With the transposed convention** (`A_ij = #` edges `j → i`), the relators are `(−2,−2)` and `(−1,−1)`, with image
    `Z(1,1)`. Then `[1] = 0` in `K_0 ≅ Z`, and the example fails condition 4.
  - The repo's ABC node warns that the two conventions differ by a transpose and advises "`det(1 − N^t)` and Smith
    invariants, which do not see the transpose". The **class of `[1]` does see it.** State the convention next to the
    example.
  - In either convention `A` is irreducible and not a permutation matrix, so `L_Q(E)` is purely infinite simple.
- **"Where the room is"** (`[v_k] = −(k+1)[v_{k+1}]` makes the coker `≅ Q`) is correct as a sketch: it is the
  colimit of `Z` under multiplication by `±(k+1)`. The finite-presentation obstruction in Attempt 1 is accurately
  described.
