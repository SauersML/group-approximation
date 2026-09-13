
## 3. Relations, D, and algebra-level models

A model of `Γ_0` is **algebra-level** if it is the restriction to `Γ_0` of a unital algebra homomorphism
`ψ : A(Γ_0) -> W`. The depth-monotone models `φ` and the symbol `q` of Theorem 2.1(d) are algebra-level.

**Lemma 3.1 (algebra-level models kill D).** Let `x_12(1), x_23(1) in Γ_0` and let `ψ : A(Γ_0) -> W` be a unital
algebra homomorphism. Then `D_ψ = ψ(s_10 t_11 s_0 t_10) = ψ(0) = 0`. The same holds in every conjugate frame
`u x_ab(1) u^(-1)` contained in `Γ_0`.

*Proof.* `N_23 N_12 = ψ(s_10 t_11) ψ(s_0 t_10) = ψ(s_10 t_11 s_0 t_10)`, and `t_11 s_0 = t_1 t_1 s_0 = 0`. In a
conjugate frame the product is `ψ(u s_10 t_11 s_0 t_10 u^(-1)) = 0`. QED

This is why Remark 3.2 of the depth-monotone artifact finds `D` killed. Section 4 leaves the algebra level.

**Proposition 3.2 (frames of S4).**
- (a) `x_12(1) = 1 + s_0 t_10` lies in `<S4>`, and `Φ(x_12(1)) = E_01(t_0)`.
- (b) `Φ(x_23(1)) = I + s_0 t_1 e_11` is not in `M_2(T)`, so `x_23(1) ∉ <S4>`.
- (c) In every ordering `(c_1, c_2, c_3)` of either three-leaf code `{0, 10, 11}` or `{1, 00, 01}`, a root
  `1 + s_(c_a) t_(c_b)` lies in `A(<S4>)` only if `{c_a, c_b}` is `{0, 10}` or `{1, 00}`. So no code frame has both
  `x_12(1)` and `x_23(1)` in `<S4>`. Whether some conjugate frame lies in `<S4>` is not decided.

*Proof.*
- (a) With `w = E_01(1) E_10(-1) E_01(1) = e_01 - e_10`, we get `w e_10 w^(-1) = -e_01`, so
  `w E_10(t_0) w^(-1) = E_01(-t_0)` and its inverse `E_01(t_0)` lie in `Φ(<S4>)`.
- (b) `T = span{s_0^a t_0^b}`, and `s_0 t_1` is a normal-form basis monomial outside that set.
- (c) The six roots of `{0, 10, 11}` have `Φ`-entries `t_0`, `s_0`, `t_1`, `s_1`, `s_0 t_1` and `s_1 t_0`; those of
  `{1, 00, 01}` are the same. Only `t_0` and `s_0` lie in `T`, and they come from the pair `{0, 10}` (respectively
  `{1, 00}`). Consecutive roots `x_12`, `x_23` use three distinct leaves. QED

**Proposition 3.3 (five-transvection sets).** Let `T = T_(σ,κ)(λ)` with `λ != 0`, and write `Φ(T) = E_ij(λ m)` with
`m = s_α t_β`. Let `W = K<s_0, t_0, m> <= R`.
- (a) `Φ(A(<S4, T>)) = M_2(W)`.
- (b) Every unital homomorphism `ψ` from `W` into a weakly finite algebra kills `Q = s_1 t_1`, and kills `m` whenever
  `α` or `β` contains the letter `1`.
- (c) `W` has a character `χ : W -> K` with `χ(s_0) = χ(t_0) = 1`. So `A(<S4, T>)` maps unitally onto a subalgebra of
  `M_2(K)`, and by Lemma 2.2 form (iii) is firewalled on `<S4, T>`.
- (d) Two extra transvections can remove every algebra-level model. For `S6 = S4 ∪ {T_(01,1), T_(1,01)}`, the entries
  are `s_1` and `t_1`, so `Φ(A(<S6>)) = M_2(R)` and `A(<S6>) = R`. `R` is simple and not weakly finite, so it has no
  nonzero weakly finite algebra image.

*Proof.*
- (a) `M_2(K) <= M_2(T)`, so `e_ki (m e_ij) e_jl = m e_kl` gives `m·I`. Conversely every generator lies in `M_2(W)`.
- (b) `ψ(t_0) ψ(s_0) = 1` forces `ψ(s_0) ψ(t_0) = 1`, so `ψ(Q) = 0`. If `j` is the first position of a `1` in `β`,
  then `m = m · s_0^(j-1) Q t_0^(j-1)`; if `i` is the first position of a `1` in `α`, then
  `m = s_0^(i-1) Q t_0^(i-1) · m`. Both factors lie in `T <= W`.
- (c) Let `Ω` be the sequences in `{0,1}^N` that are eventually `0`. `R` acts on `K[Ω]` by `s_i e_ξ = e_(iξ)` and
  `t_i e_(jξ) = δ_ij e_ξ`; the defining relations are immediate. There are three cases.
  - If `β` contains a `1`, then `t_β e_(0^∞) = 0`, and the line `K e_(0^∞)` is `W`-invariant. `s_0, t_0` act as `1`
    and `m` acts as `0`.
  - If `β` is `0^b` and `α` contains a `1`, then `U = span{e_ξ : ξ != 0^∞}` is `W`-invariant, since `s_0` and `t_0`
    preserve it and `m` lands in `e_(αξ')` with `αξ' != 0^∞`. On the one-dimensional quotient, `s_0, t_0` act as `1`
    and `m` as `0`.
  - Otherwise `m = s_0^a t_0^b` lies in `T`, and `χ` is the symbol at `ζ = 1`.
- (d) Both entries lie in `W`, so `W` contains all four generators of `R`. A nonzero homomorphism from the simple
  algebra `R` is injective and carries `t_0 s_0 = 1 != s_0 t_0` into its image. QED

Over `F_3`, (c) sends `<S4, T>` into `GL_2(F_3)` with `z -> -I`, which is a finite weakly finite model for form (iii).
Its restriction to `<S4>` is the symbol at `ζ = 1`, with image `SL_2(F_3)`.

**Corollary 3.4 (Γ_5).** Let `Γ_5 = <S4, x_23(1)>` over `F_3`, so `m = s_0 t_1`. Since `t_0 · s_0 t_1 = t_1`,
`W_5 = K<s_0, t_0, s_0 t_1> = K<s_0, t_0, t_1>`, with basis the normal-form monomials `s_0^a t_ν` (`a >= 0`, `ν` any
word).
- (a) Form (iii) is firewalled on `Γ_5` (Proposition 3.3(c)).
- (b) Every algebra-level weakly finite model `ψ` of `Γ_5` has `ψ(x_23(1)) = 1`. So `N_23 = 0`, and every tensor power
  `ψ^(⊗k)` also has `N_23 = 0`.
- (c) The symbol extends to `σ_5 : W_5 -> F_3[ζ, ζ^(-1)]`, with `σ_5(s_0^a t_ν) = ζ^(a - |ν|)` if `ν = 0^|ν|` and `0`
  otherwise. So `Γ_5 -> SL_2(F_3[ζ, ζ^(-1)])` has the same image as `Γ_4` and kills the normal closure of `x_23(1)`.

*Proof.*
- (b) The images of the `e_ij` are matrix units summing to `1`, so `W = M_2(W')` with `W' = ψ(e_00) W ψ(e_00)`
  weakly finite, and `ψ∘Φ^(-1) = M_2(ψ')` for a unital `ψ' : W_5 -> W'`. By Proposition 3.3(b),
  `ψ'(s_0 t_1) = 0`, so `ψ(x_23(1)) = ψ(Φ^(-1)(I + s_0 t_1 e_11)) = 1`. For the tensor powers,
  `(1 + 0)^(⊗k) - 1 = 0`.
- (c) `s_0^a t_ν · s_0^b t_λ` is `s_0^a t_(λν'')` if `ν = 0^b ν''`, is `s_0^(a+b-c) t_λ` if `ν = 0^c` with `c < b`, and
  is `0` otherwise. In each case `σ_5` of the product is the product of the values, and it is `0` as soon as `ν` or
  `λ` contains a `1`. QED

So `Γ_5` escapes every algebra-level firewall for form (iv), and the tensor-power upgrade of Section 4 as well.
Section 5 records it as open.

## 4. Question 3: a weakly finite model with z -> -1 and D != 0

**Theorem 4.1 (sofic corner).** Let `Γ_0 <= G` be sofic with `z, x_12(1), x_23(1) in Γ_0`. Then
`ρ(g) = ε_- g` is a homomorphism `Γ_0 -> (ε_- F_3[Γ_0])^x` into a weakly finite algebra, with `ρ(z) = -1` and
`D_ρ != 0`.

*Proof.*
- `F_3[Γ_0]` is stably finite (`linear-sofic-group-algebra-is-stably-finite`; sofic groups are linear sofic).
- `z` is central in `G`, so `ε_-` is a central idempotent: `ε_-^2 = 4(2 - 2[z]) = 2(1 - [z])` mod `3`. The corner
  `ε_- F_3[Γ_0]` is weakly finite, `ρ` is a homomorphism, and `ρ(z) = ε_-[z] = -ε_-`, which is `-1` in the corner.
- `D_ρ = 2(1 - [z])(x_23 x_12 - x_23 - x_12 + 1)`. In `R`:
  - `x_23(1) x_12(1) = 1 + s_0 t_10 + s_10 t_11`;
  - the four elements `1, x_12(1), x_23(1), x_23(1) x_12(1)` are pairwise distinct;
  - `z` times them gives their negatives, which have coefficient `-1` on the basis monomial `1`, so they differ from
    all four.
  So `D_ρ` has eight distinct group elements with coefficients `±2 != 0`. QED

**Corollary 4.2.** If `ω(0) <= ω(1)`, then `H^ω_≤` over `F_3` contains `z`, `x_12(1)` (`ω(0) <= ω(10)`) and
`x_23(1)` (`ω(10) <= ω(11)`), and it is sofic (depth-monotone artifact, Theorem 1(b)). So it has a weakly finite
representation with `z -> -1` and `D != 0`. In particular this holds for `H^1_≤`.

In rank form, `anti-central-sofic-data-cannot-force-defect-submultiplicativity` already realizes anti-central regular
ranks with cylinder defects of rank `5/9` on every sofic subgroup. Theorem 4.1 is the weakly finite statement for the
standard frame, read directly from stable finiteness of the group algebra. Corollary 4.2 adds that `H^ω_≤` is such a
subgroup. Theorem 4.3 needs neither soficity nor rank functions.

**Theorem 4.3 (explicit tensor cube).** Let `ω(0) <= ω(1)` and `K = F_3`. For `g in H^ω_≤`, let
`g_k = π(g)|_(F_k)` for `k >= k(g)` (Lemma 1.2 there), and define
`ρ_3(g) = [(g_k ⊗ g_k ⊗ g_k)_k] in Q_3 = ∏_k End(F_k^(⊗3)) / ⊕_k End(F_k^(⊗3))`.
Then `ρ_3` is a homomorphism into `Q_3^x`, `Q_3` is stably finite, `ρ_3(z) = -1` and `D_(ρ_3) != 0`.

*Proof.*
- **Homomorphism.** `(gh)_k = g_k h_k` for large `k`, and `(ab)^(⊗3) = a^(⊗3) b^(⊗3)`. Finitely many `k` do not
  matter in the quotient.
- **Stably finite.** If `AB = I_n` in `M_n(Q_3)`, then `A_k B_k = I` for all large `k`. These are finite matrices,
  so `B_k A_k = I` for large `k`.
- **Sign.** `ρ_3(z) = (-1)^(⊗3) = -1`. The tensor square would give `+1`; the odd power is needed.
- **Defect.** Let `n = π(s_0 t_10)|_(F_k)` and `m = π(s_10 t_11)|_(F_k)`, so `mn = 0`. Then
  `(1+n)^(⊗3) - 1 = Σ_(∅ != S) n^S`, where `n^S` has `n` in the positions of `S` and `1` elsewhere. In the product
  `Σ_(S,T != ∅) m^T n^S`, positions in `S ∩ T` carry `mn = 0`. The survivors are the `12` ordered pairs of nonempty
  disjoint subsets of `{1,2,3}` (`27 - 8 - 8 + 1`). Each is a distinct elementary tensor in `1, n, m`. So
  `D_k != 0` once `1, n, m` are linearly independent.
- **Independence for large k.** Take `k` with `1_[10], 1_[11] in F_k`. Then `n 1_[10] = 1_[0]`, `m 1_[10] = 0`,
  `n 1_[11] = 0` and `m 1_[11] = 1_[10]`. If `a + bn + cm = 0`, applying it to `1_[11]` gives `a = c = 0`, and then
  `b = 0`. QED

**Remark 4.4 (answer to question 2).** No obstruction to combining exists. `z -> -1` and `D != 0` fail together only
for algebra-level models (Lemma 3.1), and `ρ_3` is not additive. So form (iv) is firewalled on every depth-monotone
unit group that contains the standard frame, that is on `H^ω_≤` with `ω(0) <= ω(1)`. Theorem 4.1 gives the same for
every sofic subgroup of `G` containing `z` and the standard frame. The anti-involution `g -> (g*)^(-1)` carries this
to `H^ω_≥`, with the frame replaced by its image.
