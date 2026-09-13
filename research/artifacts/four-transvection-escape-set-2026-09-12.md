# The four-transvection set: depth-monotone escape, algebra firewalls, and the combined defect firewall

Lane `w7-escape-set`, 2026-09-12. Verifier `w4-vf-gate`: Sections 1–5 PASS with no corrections (Section 36 of
`research/artifacts/gk-vf-gate-verification-2026-09-12.md`, 89d646844c; its wording advisories are applied here).
Questions from `w6-mismatch-c3`
(`depth-monotone-configurations-cannot-force-ternary-minus-one`).

## 0. Task and verdict

**Questions.**
1. Is `S4 = {T_(0,1), T_(1,0), T_(1,00), T_(00,1)}` conjugate into some depth-monotone unit group `H^ω_≤` or `H^ω_≥`?
   What about `x_0` together with one transvection?
2. If `S4` escapes, what is `<S4, z>`, is it caught by the sofic or graph-of-groups firewall, and do its relations touch
   the two-root defect `D`?
3. Does `H^1_≤` have a weakly finite representation over `F_3` with `z -> -1` and `D != 0`?

**Verdict.**
1. **No, proved (Section 1).** The algebra spanned by `<S4>` contains a one-sided inverse pair that is not two-sided.
   Stably finite algebras contain no such pair, so no conjugate of `<S4>` lies in any `H^ω_≤` or `H^ω_≥`. Every
   three-element subset of `S4` lies in one of them without conjugation, so `S4` is a minimal escaping set. A second
   invariant, local finiteness on cylinder functions, excludes `x_0`, and so every group containing it.
2. **S4 is not the candidate input (Section 2).** Code `(0,1)` puts `<S4>` inside `EL_2` of the ternary Jacobson
   algebra. There `z` is already in `<S4>`, the symbol image is `SL_2(F_3[ζ, ζ^(-1)])`, and the symbol is a
   weakly finite representation with `z -> -1`. So form (iii) is firewalled on `<S4>` by an explicit model that
   realizes every relation. The same holds for every five-transvection set `S4 ∪ {T}`, by a character from the eventually-0 sequence representation (Proposition 3.3).
   Soficity of `<S4>` is not decided; it has the locally-finite-by-linear shape of `w7-el3j-sofic`.
3. **Relations and D (Section 3).** Models that come from algebra homomorphisms kill `D` in every frame whose roots they
   contain; that is why the depth-monotone models kill it. In the standard frame `x_12(1)` lies in `<S4>` and
   `x_23(1)` does not. For `Γ_5 = <S4, x_23(1)>`, every algebra-level weakly finite model sends `x_23(1)` to `1`. So
   `Γ_5` escapes all algebra-level firewalls for form (iv). Whether it escapes all firewalls is recorded as an open
   claim, with its consequences.
4. **Yes, proved (Section 4).** For `ω(0) <= ω(1)`, `H^ω_≤` has a weakly finite representation over `F_3` with
   `z -> -1` and `D != 0`. One proof is abstract: `H^ω_≤` is sofic, so the corner `ε_- F_3[H^ω_≤]` works. The other is
   explicit: the tensor cube of the stably finite embedding `φ`. So form (iv) is firewalled on every depth-monotone
   configuration, even though the depth-monotone models themselves kill `D`.

**Notation.** As in `research/artifacts/depth-monotone-leavitt-firewall-2026-09-12.md`:
- `R = L_K(1,2)`, `t_i s_j = δ_ij`, `s_0 t_0 + s_1 t_1 = 1`, `s_μ = s_(μ_1)...s_(μ_k)`, `t_μ = t_(μ_k)...t_(μ_1)`;
- `π` is the faithful action on the locally constant functions `C` on `{0,1}^N`, with `(π(s_μ t_ν) f)(μξ) = f(νξ)`
  and `0` off `[μ]`;
- `ω(0) = a`, `ω(1) = b` are positive weights; `R^ω_≤` is spanned by the `s_μ t_ν` with `ω(μ) <= ω(ν)`, and
  `H^ω_≤ = (R^ω_≤)^x`; mirror notation for `≥`; `F_r ⊆ C` are the finite-dimensional spaces of Lemma 1.2 there;
- `φ : R^ω_≤ -> Q = ∏_k End(F_k) / ⊕_k End(F_k)` is the stably finite embedding of Theorem 1 there;
- `T_(σ,κ)(λ) = 1 + λ s_σ t_κ` for incomparable words `σ, κ` and `λ in K`, with `λ = 1` if omitted;
- `G = L_(F_3)(1,2)^x`, `z = -1`, `ε_- = 2(1 - [z])`, and `S_- = ε_- F_3[G]`;
- three-leaf code `(0, 10, 11)`: `x_12(1) = 1 + s_0 t_10`, `x_23(1) = 1 + s_10 t_11`, `N_ab = ρ(x_ab(1)) - 1` and
  `D_ρ = N_23 N_12`, as in Theorem 2 of `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`;
- for a subgroup `Γ_0 <= R^x`, `A(Γ_0)` is the `K`-span of `Γ_0` in `R`, a unital subalgebra.

## 1. S4 escapes every depth-monotone unit group

**Theorem 1.1.** For every field `K`, `A(<S4>)` contains
`x = s_00 t_0 + s_1 t_1` and `y = s_0 t_00 + s_1 t_1`, with `yx = 1` and `xy = 1 - s_01 t_01 != 1`.
So for every unit `u` and every weight `ω`, neither `u<S4>u^(-1) <= H^ω_≤` nor `u<S4>u^(-1) <= H^ω_≥`.

*Proof.*
1. `A(<S4>)` contains `A = s_0 t_1`, `A' = s_1 t_0`, `B = s_1 t_00` and `B' = s_00 t_1`, the four transvections
   minus `1`.
2. `B'A' = s_00 t_1 s_1 t_0 = s_00 t_0`, `A'A = s_1 t_0 s_0 t_1 = s_1 t_1` and `AB = s_0 t_1 s_1 t_00 = s_0 t_00`.
   So `x = B'A' + A'A` and `y = AB + A'A` lie in `A(<S4>)`.
3. `yx = s_0 t_00 s_00 t_0 + s_0 t_00 s_1 t_1 + s_1 t_1 s_00 t_0 + s_1 t_1 = s_0 t_0 + 0 + 0 + s_1 t_1 = 1`.
4. `xy = s_00 t_0 s_0 t_00 + s_1 t_1 = s_00 t_00 + s_1 t_1 = 1 - s_01 t_01`, and `s_01 t_01 != 0`.
5. If `u<S4>u^(-1) <= (R^ω_≤)^x`, then `u A(<S4>) u^(-1) <= R^ω_≤`, because the latter is a subalgebra. Then
   `(u y u^(-1))(u x u^(-1)) = 1 != (u x u^(-1))(u y u^(-1))` inside `R^ω_≤`, contradicting Theorem 1 of the firewall
   artifact. The `≥` side is the same. QED

**Remark 1.2 (minimality).** Every three-element subset of `S4` lies in a depth-monotone unit group without
conjugation:
- `{T_(0,1), T_(1,0), T_(1,00)}` in `H^ω_≤` with `a = b`;
- `{T_(0,1), T_(1,0), T_(00,1)}` in `H^ω_≥` with `a = b`;
- `{T_(0,1), T_(1,00), T_(00,1)}` in `H^ω_≤` with `b = 2a`;
- `{T_(1,0), T_(1,00), T_(00,1)}` in `H^ω_≥` with `b = 2a`.
Each check is a comparison of `ω(σ)` with `ω(κ)`; for example `b = 2a` gives `ω(00) = ω(1)`. So `S4` is a minimal
escaping set of transvections, and the obstruction is exactly the failure of direct finiteness in Theorem 1.1. This
supplies the conjugation invariant that the `w6-mismatch-c3` Attempts entry says is missing.

**Proposition 1.3 (local finiteness).** If `u g u^(-1) in R^ω_≤` for some unit `u`, then `π(g)` is locally finite
on `C`: every `f in C` lies in a finite-dimensional `π(g)`-invariant subspace. If `u g u^(-1) in R^ω_≥`, then
`π(g*)` is locally finite, where `*` is the involution with `s_i* = t_i`.

*Proof.* Let `h = u g u^(-1) in R^ω_≤`. By Lemma 1.2 of the firewall artifact, `π(h)` preserves `F_r` for every `r`
beyond the largest `ω(μ)` in its terms, and `C = ∪_r F_r`. So `π(h)` is locally finite, and so is
`π(g) = π(u)^(-1) π(h) π(u)`. On the `≥` side, `*` maps `R^ω_≥` onto `R^ω_≤`, and
`(u g u^(-1))* = (u*)^(-1) g* u*`. QED

**Corollary 1.4 (x_0).** Let `x_0 = s_0 t_00 + s_10 t_01 + s_11 t_1 in V`. Then `π(x_0) 1_[1^n] = 1_[1^(n+1)]`, so
`π(x_0)` is not locally finite. Also `x_0* = x_0^(-1)`, and an invertible operator is locally finite iff its inverse
is. So no conjugate of `x_0`, and no conjugate of any group containing `x_0`, lies in any `H^ω_≤` or `H^ω_≥`. In
particular `<x_0, T_(σ,κ)(λ)>` escapes for every transvection. The same argument applies to every `g in V` that
maps some cylinder `[w]` onto a proper subcylinder `[wv]` by `wξ -> wvξ`. The other convention for `x_0` is this
element's inverse.

## 2. S4 lives in EL_2 of the ternary Jacobson algebra

Let `Φ : R -> M_2(R)` be the code-`(0,1)` isomorphism `Φ(x) = (t_i x s_j)_(i,j in {0,1})`, with inverse
`(x_ij) -> Σ s_i x_ij t_j`, and let `E_ij(c) = 1 + c e_ij`. For incomparable `σ = σ_1σ'` and `κ = κ_1κ'`,
`Φ(s_σ t_κ) = s_(σ') t_(κ') e_(σ_1 κ_1)`. So `Φ` of a transvection is `1` plus one monomial entry.

**Theorem 2.1.**
- (a) `Φ(S4) = {E_01(1), E_10(1), E_10(t_0), E_01(s_0)}` and `Φ(A(<S4>)) = M_2(T)`, where `T = K<s_0, t_0> <= R`.
  The map `S -> s_0`, `T -> t_0` is an isomorphism from the Jacobson algebra `J_K = K<S, T | TS = 1>` onto `T`.
- (b) Over `F_3`, `z in <S4>`. So `Γ_4 := <S4, z> = <S4>`, and `Φ(Γ_4) <= EL_2(J_(F_3))`.
- (c) The symbol `σ : T -> F_3[ζ, ζ^(-1)]`, `s_0 -> ζ`, `t_0 -> ζ^(-1)`, has kernel the socle
  `span{s_0^a s_1 t_1 t_0^b} ≅ M_∞(F_3)`, and `σ(Φ(Γ_4)) = SL_2(F_3[ζ, ζ^(-1)])`.
- (d) `q = σ∘Φ : Γ_4 -> GL_2(F_3(ζ))` is a weakly finite representation with `q(z) = -1`. So `ε_- F_3[Γ_4]` has a
  nonzero weakly finite image, and no certificate for `ternary-anti-central-summand-has-no-weakly-finite-image` has all
  its group elements in a conjugate of `Γ_4`.

*Proof.*
- (a) The entries follow from the formula above. `A(<S4>)` is generated by `e_01`, `e_10`, `t_0 e_10` and `s_0 e_01`.
  It contains `e_00 = e_01 e_10` and `e_11`, hence `t_0 e_00 = e_01 (t_0 e_10)`, `t_0 e_11 = (t_0 e_10) e_01`, and the
  same for `s_0`. So it contains `M_2(K)`, `s_0·1` and `t_0·1`, and equals `M_2(T)`. The normal-form basis of `L_K(1,2)`
  (monomials `s_μ t_ν` where `μ` and `ν` do not both end in `1`; Alahmedi–Alsulami–Jain–Zelmanov) contains the
  distinct monomials `s_0^a t_0^b`. They are the images of the basis `S^a T^b` of `J_K`, so the map is injective.
- (b) `SL_2(F_3) = <E_01(1), E_10(1)>` contains `-I = Φ(z)`. All four generators are elementary.
- (c) With `Q = 1 - s_0 t_0 = s_1 t_1`, the `s_0^a Q t_0^b` multiply as matrix units, since `Q t_0^b s_0^c Q = δ_bc Q`.
  The quotient by their span is spanned by commuting inverse images of `s_0`, `t_0`, and it is `F_3[ζ, ζ^(-1)]`
  (Jacobson). For the image, `σΦ(Γ_4)` contains `E_01(1)`, `E_10(1)`, `E_10(ζ^(-1))` and `E_01(ζ)`, hence
  `w = E_01(1) E_10(-1) E_01(1)` and `w(ζ) = E_01(ζ) E_10(-ζ^(-1)) E_01(ζ) = [[0, ζ], [-ζ^(-1), 0]]`, and
  `h = w^(-1) w(ζ) = diag(ζ^(-1), ζ)`. Conjugation by `h^n` gives `E_01(ζ^(-2n))` and `E_01(ζ^(1-2n))`, so all of
  `E_01(F_3[ζ, ζ^(-1)])`. Conjugation by `w` gives the `E_10`. `F_3[ζ, ζ^(-1)]` is Euclidean, so `E_2 = SL_2`.
- (d) `M_2(F_3(ζ))` is weakly finite, and the linear extension `F_3[Γ_4] -> M_2(F_3(ζ))` sends `ε_-` to `1`. For a
  conjugate `uΓ_4u^(-1)`, compose with conjugation by `u`. QED

**Lemma 2.2 (algebra firewall).** Let `z in Γ_0 <= G`. If `A(Γ_0)` has a unital homomorphism into a nonzero weakly
finite `F_3`-algebra `W`, then `ε_- F_3[Γ_0]` has a nonzero weakly finite image. The hypothesis is invariant under
conjugation.

*Proof.* `F_3[Γ_0] -> A(Γ_0) -> W` is unital and sends `[z]` to `-1` and `ε_-` to `1 != 0`. QED

The depth-monotone firewall is the case `A(uΓ_0u^(-1)) <= R^ω_≤` with `W = Q`, and Theorem 2.1(d) is the case
`W = M_2(F_3(ζ))`.

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

**Remark 4.4 (answer to question 2).** On these groups no obstruction to combining exists. Algebra-level models kill
`D` (Lemma 3.1), but the models of Theorems 4.1 and 4.3 are not additive and keep `z -> -1` with `D != 0`. Which
other non-additive models combine the two is not decided. So form (iv) is firewalled on every depth-monotone
unit group that contains the standard frame, that is on `H^ω_≤` with `ω(0) <= ω(1)`. Theorem 4.1 gives the same for
every sofic subgroup of `G` containing `z` and the standard frame. The anti-involution `g -> (g*)^(-1)` carries this
to `H^ω_≥`, with the frame replaced by its image.

## 5. Where it stops

**Proved here, on paper, and re-derived by `w4-vf-gate` (Section 36, PASS).**
- `S4` escapes conjugation into every weighted unit group, and `x_0` escapes by local finiteness (Section 1).
- `<S4>` sits in `EL_2(J_(F_3))`, contains `z`, and has a weakly finite symbol model with `z -> -1`. Every
  five-transvection set `S4 ∪ {T}` has a character model (Sections 2 and 3).
- Algebra-level models kill `D` (Lemma 3.1).
- Sofic subgroups containing `z` and the standard frame, in particular `H^ω_≤` with `ω(0) <= ω(1)`, have weakly
  finite models with `z -> -1` and `D != 0`; the tensor cube gives one explicitly (Section 4).

**Open.**
1. **Γ_5 and the defect** (`four-transvections-and-x23-force-defect-vanishing`). Every homomorphism
   `ρ : Γ_5 -> W^x` into a weakly finite `F_3`-algebra with `ρ(z) = -1` has `D_ρ = 0`.
   - **Why it is a candidate input.** With `weakly-finite-leavitt-representations-killing-defect-are-trivial` it gives
     `ternary-anti-central-summand-has-no-weakly-finite-image`. A unital `ψ : S_- -> W` with `W != 0` weakly finite
     gives `ρ(g) = ψ(ε_- g)` on `G` with `ρ(z) = -1`. Its restriction to `Γ_5` has `D = 0`, so `ρ` is trivial, so
     `-1 = 1` in `W` and `W = 0`.
   - **What it forces on Γ_5.** `Γ_5` is not sofic (Theorem 4.1), and no finite quotient of `Γ_5` separates the eight
     elements `z^e x_23(1)^a x_12(1)^b` with `e, a, b in {0,1}`.
   - **What is already firewalled.** Form (iii) on `Γ_5`. Every algebra-level model and each of its tensor powers kills
     `N_23`, and so does every model through `Γ_5 -> SL_2(F_3[ζ, ζ^(-1)])` (Corollary 3.4).
   - **What refutes it.** Soficity of `Γ_5`; a finite quotient separating those eight elements; any weakly finite
     model with `z -> -1` and `D != 0`.
2. **Soficity of <S4>.** `<S4>` is locally finite by linear
   (`jacobson-elementary-subgroups-are-locally-finite-by-linear`). Amenable-by-sofic is not known to be sofic; this
   is the same shape as `w7-el3j-sofic` (`research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md`). LEF and
   residual finiteness are not decided.
   - `<S4>` maps onto `SL_2(F_3[ζ, ζ^(-1)])`, which is finitely generated, linear and not virtually solvable. By the
     Tits alternative it contains a free group.
   - So `<S4>` is not amenable and lies in no amenable subgroup of `G`. Over `F_2` the same argument, with image
     `SL_2(F_2[ζ, ζ^(-1)])`, keeps it out of the amenable groups `U_< ⋊ P` of
     `lex-decreasing-units-with-order-preserving-letters-are-amenable`.
   - `graphs-of-locally-finite-groups-carry-regular-rank-models` needs a splitting of `<S4>` or `Γ_5` as a graph of
     locally finite groups, and none is known. Such a splitting would make the group sofic (sofic vertex groups,
     amenable edge groups), so for `Γ_5` this firewall is one case of the soficity refuter in item 1.
3. **<S6> and G.** `A(<S6>) = R`, so no algebra-level firewall applies to `<S6>` or to any group containing it.
   Whether `<S6> = G` is not decided.
4. **Other frames.** Whether a conjugate frame lies in `<S4>` is not decided (Proposition 3.2(c)). Five-transvection
   sets other than `Γ_5` do not contain the standard frame and are not classified for form (iv).

**Peer lanes (wave 7).**
- `w7-sub-multiletter` (37bafd8f3) landed `split-cylinder-data-cannot-force-defect-submultiplicativity` and
  `lex-decreasing-units-with-order-preserving-letters-are-amenable`. Both are rank-function statements about cylinder
  copies with swaps, and about `U_< ⋊ P`. `S4` has no swap letters, and it maps onto a nonamenable group. Nothing here
  repeats them.
- `w7-v-cycle-c3` (2e8bf4f44) landed `p-cycle-tree-invariance-cannot-force-order-char-law`, which is about rank models
  on `V`. There is no overlap.
- `w7-k2-unstable` has no claim node on main at c609c3bab, only the plan note 73770d983. There is no overlap.

**Nodes.**
- `four-transvection-set-escapes-depth-monotone-units` (Section 1), route `four-transvection-escape-proof`.
- `four-transvection-units-have-a-weakly-finite-symbol-image` (Sections 2 and 3), route
  `four-transvection-symbol-firewall-proof`.
- `depth-monotone-units-carry-weakly-finite-nonzero-defect` (Section 4), route `depth-monotone-tensor-cube-defect-proof`.
- `four-transvections-and-x23-force-defect-vanishing` (OPEN), route `summand-obstruction-from-four-transvection-defect`
  into `ternary-anti-central-summand-has-no-weakly-finite-image`.
