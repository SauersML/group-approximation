# The four-transvection set: depth-monotone escape, algebra firewalls, and the combined defect firewall

Lane `w7-escape-set`, 2026-09-12. Verifier `w4-vf-gate` (re-derivation requested). Questions from `w6-mismatch-c3`
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
