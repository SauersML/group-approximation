---
rg: 2
id: solvable-polynomial-automata-chief-series-peeling-proof
kind: route
title: Split the alphabet along an abelian chief factor, make the data layer a certificate-affine family, invert its constant fibre by direct finiteness, spread invertibility by the fibre dichotomy, and force the quotient automaton injective by collision
target: solvable-polynomial-automata-reduce-to-kaplansky
requires:
  - nonlinear-certificate-fibers-are-all-surjective-or-all-strict
  - homomorphic-group-alphabet-ca-reduce-to-stable-finiteness
  - stable-finiteness-failure-refutes-surjunctivity
  - higman-group-algebras-embed-in-division-rings
---

**Imported inputs.**
- **(D) Fibre dichotomy** (`nonlinear-certificate-fibers-are-all-surjective-or-all-strict`).
  - Setting: `A` and `B` are finite alphabets, and `E(x,c) = (T_c x, c)` is an injective cellular automaton on
    `(A x B)^G` with local dependence on data and certificate.
  - Conclusion: either every `T_c` is bijective, or every `T_c` is injective and nonsurjective.
- **(L) Linear surjunctivity** (`homomorphic-group-alphabet-ca-reduce-to-stable-finiteness`, item 1). Every
  injective `F_p`-linear cellular automaton on `(F_p^n)^G` is surjective if and only if `M_n(F_p[G])` is
  directly finite.
- **(S) Strict linear automata** (`stable-finiteness-failure-refutes-surjunctivity`). If `k[G]` is not directly
  finite (`k` a finite field), then there is an injective nonsurjective `k`-linear cellular automaton on `k^G`
  with finite memory.
- **(H) Higman's group** (`higman-group-algebras-embed-in-division-rings`). `M_n(F_p[H])` is directly finite for
  all `n` and `p`. Used only in Step 9.
- The shift is `(h.x)(g) = x(h^-1 g)`. A cellular automaton is a shift-equivariant map with a finite local rule.

**Step 0 (automata).**
- A `Q`-polynomial automaton is `tau(x)(g) = w(x(g m_1), ..., x(g m_k))`, with `w` a word in letters from `Q`
  and `x_j^(+1)`, `x_j^(-1)`.
- For a normal subgroup `N`, write `wbar` for `w` with constants reduced mod `N`. The **shadow** of `tau` over
  `Q/N` is the `(Q/N)`-polynomial automaton with the same memory and rule `wbar`.
- The quotient map `Q^G -> (Q/N)^G` intertwines `tau` with its shadow.

**Step 1 (coordinates along an abelian minimal normal subgroup).**

Let `A` be abelian minimal normal in `Q`. It is characteristically simple and abelian, hence `A = F_p^d`;
write it additively. Put `B = Q/A`.
- Choose a set section `q: B -> Q` with `q(1) = 1`. Every `x in Q` is uniquely `x = a q(b)`, with `a in A`
  and `b in B`.
- Let `rho(b)a = q(b) a q(b)^-1`. This is well defined on `B`, since `A` is abelian.
- Define `f(b,b')` and `f~(b)` in `A` by `q(b) q(b') = f(b,b') q(bb')` and `q(b)^-1 = f~(b) q(b^-1)`.

Then:

    (a q(b)) (a' q(b')) = (a + rho(b)a' + f(b,b')) q(bb'),
    (a q(b))^-1         = (-rho(b)^-1 a + f~(b)) q(b^-1).

For the second formula: `q(b)^-1 (-a) = (q(b)^-1 (-a) q(b)) q(b)^-1 = (-rho(b)^-1 a) q(b)^-1`.

**Lemma 1.1.** Let `w = y_1 ... y_n` and `x_j = a_j q(b_j)`. Let `beta_i in B` be the image of the prefix
`y_1 ... y_i`; it depends only on `b = (b_1, ..., b_k)`. Then

    w(x) = ( sum_j C_j(b) a_j + D(b) ) q(wbar(b)),
    C_j(b) = sum_{i : y_i = x_j} rho(beta_(i-1)) - sum_{i : y_i = x_j^-1} rho(beta_(i-1)) rho(b_j)^-1,

where `D(b) in A` depends only on `b`. In particular `C_j(b)` lies in `E = span_(F_p) rho(B)`, inside
`End(A) = M_d(F_p)`.

*Proof.* Induct on `n`. Write the prefix value as `alpha_i q(beta_i)`, and the next letter as `a' q(b')`.
- The product formula gives `alpha_(i+1) = alpha_i + rho(beta_i) a' + f(beta_i, b')`.
- For `y = x_j`, `a' = a_j`.
- For `y = x_j^-1`, `a' = -rho(b_j)^-1 a_j + f~(b_j)`.
- For a constant, `a'` is fixed.

So the `a`-linear part grows exactly by the displayed terms, and everything else depends on `b` only. The
`B`-component multiplies as in `B`. ∎

**Configurations.** Let `Phi: Q^G -> A^G x B^G`, `x(g) = a(g) q(b(g))`. It is a shift-equivariant
homeomorphism. By Lemma 1.1,

    Phi tau Phi^-1 (a, b) = (L_b a + d_b, taubar(b)),
    (L_b a)(g) = sum_j C_j(b(g m_1), ..., b(g m_k)) a(g m_j),
    d_b(g)     = D(b(g m_1), ..., b(g m_k)),

where `taubar` is the shadow over `B`. Each `L_b` is `F_p`-linear. The family is equivariant:
`L_(h.b)(h.a) = h.(L_b a)` and `d_(h.b) = h.d_b`. This proves Theorem 1.1.

**Step 2 (the certificate-preserving shadow).** Assume `tau` is injective. Fix `b`. The affine map
`a -> L_b a + d_b` is injective, so `L_b` is injective. Put `E(a,b) = (L_b a, b)`.
- `E` is a cellular automaton on `(A x B)^G`. Its local rule at `g` reads `(a,b)` on `g{m_j}`, and it is
  equivariant by Step 1.
- `E` is injective, because every `L_b` is.
- The fibres `T_b = L_b` depend locally on data and certificate, with the uniform memory `{m_j}`.

So (D) applies with data alphabet `A` and certificate alphabet `B`.

**Step 3 (one constant fibre is invertible).** Fix `beta in B`, and let `c_beta` be the constant certificate.
Then `(L_(c_beta) a)(g) = sum_j C_j(beta, ..., beta) a(g m_j)`. This is an injective `F_p`-linear cellular
automaton on `(F_p^d)^G`, with matrix coefficients in `E`. If `M_d(F_p[G])` is directly finite, (L) makes it
surjective.

**Step 4 (every fibre is invertible).**
- By Step 2, `E` is injective.
- By Step 3, the fibre `T_(c_beta)` is surjective, so the second alternative of (D) fails.
- Hence every `L_b` is bijective.

**Step 5 (collision forces the shadow injective).** Suppose `taubar(b) = taubar(b')` with `b != b'`.
- Put `y = d_b`. Since `L_(b')` is bijective, there is `a'` with `L_(b') a' + d_(b') = y`.
- Then `tau Phi^-1(0, b) = Phi^-1(y, taubar b) = tau Phi^-1(a', b')`.
- The inputs differ, since `b != b'`. This contradicts injectivity of `tau`.

So `taubar` is injective. This proves Theorem 1.2.

**Step 6 (surjectivity transfer).**
- If `tau` is surjective, so is `taubar`, by projection.
- Conversely, suppose `taubar` is surjective, and take a target `Phi^-1(y, v)`. Pick `b` with `taubar(b) = v`,
  and put `a = L_b^-1 (y - d_b)`, using Step 4. Then `tau Phi^-1(a, b) = Phi^-1(y, v)`.

This proves Theorem 1.3.

**Step 7 (Theorem 2, induction on the solvable radical).**
- **Existence of the chain.** Refine `1 <= Sol(Q) <= Q` to a chief series of `Q`. Each factor
  `Q_i/Q_(i-1)` below `Sol(Q)` is minimal normal in `Q/Q_(i-1)` and lies in a solvable group, so it is abelian,
  hence `F_(p_i)^(d_i)`.
- **Induction.** Induct on `r`; for `r = 0` there is nothing to prove. Apply Theorem 1 with `A = Q_1`. If
  `tau` is injective, its shadow over `Q/Q_1` is injective, and `tau` is surjective iff that shadow is.
  - `Sol(Q/Q_1) = Sol(Q)/Q_1`, because `Q_1` is solvable.
  - The factors `Q_i/Q_1` form a chain of length `r - 1` of the same kind, with the same `(p_i, d_i)`.
  - The shadow of the shadow is the shadow over `Q/Sol(Q)`.
  - So an injective `tau` is surjective iff its shadow over `Q/Sol(Q)` is, and that shadow is injective. This is
    the first bullet of Theorem 2, and the second follows.
- **Solvable `Q`.** `Q/Sol(Q) = 1`, and the automaton on a one-point alphabet is bijective.
- **Supersolvable `Q`.** Its chief factors have prime order, so every `d_i = 1` and only `F_p[G]` enters, for
  `p | |Q|`.
- **Nilpotent `Q`.** Nilpotent groups are supersolvable, which reproduces part 3 of
  `nilpotent-polynomial-automata-reduce-to-kaplansky`.

**Step 8 (Theorem 3 for `S_3`).**

`S_3 = <t> x| <r>` with `r t r = t^-1`. Use the section `q(s) = r^s`, so `x = t^a r^s` with `a in F_3` and
`s in F_2`.

*Direction "direct finiteness implies surjunctivity".* The chief series is `1 < <t> < S_3`, with factors `F_3`
and `F_2`, both `d = 1`. Apply Theorem 2.

*Word identities.*
- **`p(x) = x^3 r x r x` equals `r^s`.**
  - If `s = 0`, then `x = t^a`, `x^3 = 1`, and `r t^a r t^a = t^-a t^a = 1`.
  - If `s = 1`, then `x` is an involution, so `x^3 = x`. Then `x r = t^a`, `t^a x = t^(2a) r`,
    `t^(2a) r r = t^(2a)`, and `t^(2a) x = t^(3a) r = r`.
- **`v(x) = x p(x)` equals `t^a`.** `v(x) = t^a r^s r^s = t^a`.

*Direction "surjunctivity implies direct finiteness".*
- **`F_3[G]` not directly finite.** (S) gives an injective nonsurjective `lambda` on `F_3^G`, with
  `(lambda a)(g) = sum_(h in M) lambda_h a(g h)`, `M` finite and `lambda_h in {0,1,2}`. Every
  shift-equivariant local `F_3`-linear map has this form.
  - Let `tau_lambda` have memory `M ∪ {1}` and rule `prod_(h in M) v(x_h)^(lambda_h) p(x_1)`.
  - Since the `t`-powers commute, `tau_lambda(x)(g) = t^((lambda a)(g)) r^(s(g))`.
  - So `Phi tau_lambda Phi^-1 = lambda x id` is injective and not surjective.
- **`F_2[G]` not directly finite.** (S) gives a strict `sigma`, with `(sigma s)(g) = sum_(h in M) beta_h s(gh)`.
  - Let `tau_beta` have rule `v(x_1) prod_(h in M) p(x_h)^(beta_h)`.
  - Then `tau_beta(x)(g) = t^(a(g)) r^((sigma s)(g))`.
  - So `Phi tau_beta Phi^-1 = id x sigma` is strict.

∎

**Step 9 (corollaries).**
- **Unique-product `G`.** `F_p[G]` is a domain. A domain is directly finite: if `ab = 1`, then `ba` is
  idempotent; if `ba = 0`, then `1 = (ab)(ab) = a(ba)b = 0`, a contradiction. So `ba = 1`. Apply Theorem 2 for
  supersolvable `Q`.
- **Higman's group `H`.** By (H) every hypothesis of Theorem 2 holds for every `Q`.
  - For solvable `Q`, injective implies bijective.
  - For arbitrary `Q`, an injective nonsurjective `Q`-polynomial automaton has an injective nonsurjective shadow
    over `Q/Sol(Q)`, by the first bullet of Theorem 2.

**Remarks.**
- **No crossed products.** The fibres `L_b` are the operators of the certificate-controlled algebra
  `C(B^G, E) x| G`. Nothing about direct finiteness of that algebra is used, only (D) and the constant
  certificate.
- **`A_4`.** The chief factors are `F_2^2`, with `E = F_4` inside `M_2(F_2)`, and `F_3`. So the hypotheses are
  direct finiteness of `M_2(F_2[G])` and of `F_3[G]`. A refinement to direct finiteness of `F_4[G]` is expected
  from Step 3 but is not claimed.
- **Brute force.** The artifacts check Lemma 1.1 and the exact finite-host form of Steps 4–6: "bijective iff the
  shadow and all fibres are bijective". They also check the words `p` and `v` and both realizers.
