---
rg: 2
id: nekrashevych-completions-contain-their-coefficients-proof
kind: route
title: Represent the completion in a skew Laurent ring over the dilated direct limit of the matrix core
target: nekrashevych-completions-contain-their-coefficients
requires: []
artifacts:
  - research/artifacts/bh-steinberg-hosts-2026-09-12.md
---

The full proof is Section 1 of the artifact. The steps:

1. **Finite presentation.** `Ψ(b) = Σ s_i psi(b)_(ij) s_j*` is a unital
   homomorphism `B -> O`: it is `psi`, followed by the matrix-unit isomorphism
   `M_d(O) -> O`. The set where `Ψ` agrees with the inclusion is a subalgebra,
   so the relation on generators implies it everywhere.
2. **Core and corner map.**
   - `B_n = M_(d^n)(B)`, indexed by words, with `φ_n(x)_(uw,vz) = psi(x_(uv))_(wz)`,
     injective and unital.
   - `α_n(x)_(1u,1v) = x_(uv)`, other entries `0`, satisfies
     `φ_(n+1) α_n = α_(n+1) φ_n`.
   - So `α` is an isomorphism of `B_inf` onto the corner `p B_inf p`,
     `p = E_(11)`.
3. **Dilation.**
   - `A = lim(B_inf --α--> B_inf --α--> ...)`, with the shift automorphism
     `σ[a]_k = [a]_(k+1)`, so `σ^-1[a]_0 = [α a]_0`.
   - `R = A[t, t^-1; σ^-1]`, `p_0 = [1]_0`, `Q = p_0 R p_0`.
   - `t_+ = t p_0`, `t_- = p_0 t^-1`, with `t_- t_+ = p_0`, `t_+ t_- = [p]_0` and
     `t_+ a = α(a) t_+`.
4. **Relations hold.** `b |-> [b]_0`, `s_i |-> E_(i1) t_+`,
   `s_i* |-> t_- E_(1i)`. Then:
   - `s_i* s_j |-> δ_(ij) (t_- t_+)^2 = δ_(ij) p_0`;
   - `Σ s_i s_i* |-> Σ E_(ii) = p_0`;
   - `t_+ c t_- = α(c)`, so `Σ s_i psi(b)_(ij) s_j* |-> psi(b) = [b]_0`.

   `B -> Q` is injective because `α` is, which gives (2).
5. **Core embedding.** `x |-> Σ s_u x_(uv) s_v*` is a homomorphism
   `B_inf -> O_psi` onto degree zero, by normal forms. Its composite with the
   map of step 4 is `x |-> [x]_0`, by induction on `n`, using `psi(1) = I`. That
   is injective, which gives (3).
6. **Strong grading.** `1 = Σ s_i s_i*` lies in `O_1 O_(-1)` and `1 = s_1* s_1` in
   `O_(-1) O_1`.
