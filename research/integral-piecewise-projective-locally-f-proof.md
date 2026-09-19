---
rg: 2
id: integral-piecewise-projective-locally-f-proof
kind: route
title: Minkowski's question mark turns PSL_2(Z) pieces into dyadic affine pieces with rational breakpoints, the odd part of the breakpoint denominators filters the group, and multiplication by an odd M carries each filtration step into F
target: integral-piecewise-projective-groups-are-locally-subgroups-of-f
requires:
  - thompson-f-co-amenable-hosts-have-integral-end-germs
  - f-overgroups-with-a-non-integral-rational-piece-are-nonamenable
---

**Uses.**
- The model of `F`, quoted verbatim from Lodha–Moore (arXiv:1308.4250, `vN_fp.tex`) in
  `thompson-f-co-amenable-hosts-have-integral-end-germs-proof`:
  - l.132–134: "by an unpublished result of Thurston, $a(t)$ and $b(t)$ generate the subgroup
    $P(\Zbb) \leq H$, consisting of those homeomorphisms which are $C^1$ and piecewise
    $\PSL_2(\Zbb)$";
  - l.271–272: "the elements of $F$ correspond exactly to those homeomorphisms $f$ of $\Rbb$ which
    are piecewise $\PSL_2(\Zbb)$ and which have continuous derivatives."
  - "Piecewise" means finitely many pieces, as recorded under "Implicit assumption" in that route.
- The theorem (parts 1–4 and C1, C2) uses nothing else. C3 and C4 also use part 1 of
  `f-overgroups-with-a-non-integral-rational-piece-are-nonamenable`.

**Notation.**
- A *Farey interval* is `I = [p/q, r/s]` with `q, s ≥ 1` and `rq − ps = 1`. Its vectors are
  `u_I = (p,q)` and `v_I = (r,s)`. Its *mediant* is `(p+r)/(q+s)`, and its *children* are the two
  halves at the mediant, which are again Farey intervals.
- The *Stern–Brocot tree* of `[n, n+1]` is the set of intervals obtained from `[n, n+1]` by
  repeatedly taking children. The depth of `[n,n+1]` is `0`.
- A *standard dyadic interval* is `[j 2^{-k}, (j+1) 2^{-k}]` with `j ∈ Z` and `k ≥ 0`.
- `Φ` is Minkowski's `?` on `[0,1]`, extended by `Φ(x+n) = Φ(x) + n`. Classically, `Φ` is the
  increasing homeomorphism of `R` that sends each Stern–Brocot interval of depth `k` below
  `[n,n+1]` onto the standard dyadic interval of length `2^{-k}` at the same address, and sends
  mediants to midpoints. So `Φ(Q) = Z[1/2]`. `Φ` sends real quadratic irrationals, whose continued
  fractions are eventually periodic, to non-dyadic rationals, whose binary expansions are
  eventually periodic and do not terminate. This is the only property of `Φ` used, and it can be
  taken as its definition, since the Stern–Brocot endpoints are dense.

**Lemma 0 (every Farey interval is Stern–Brocot).** Induct on `q + s`.
- If `q = s`, then `q(r − p) = 1`, so `q = s = 1` and `I = [p, p+1]`.
- If `q > s`, then `I' = [(p−r)/(q−s), r/s]` has `r(q−s) − (p−r)s = rq − ps = 1` and denominators
  `q − s, s ≥ 1`, with a smaller sum. Its mediant is `p/q`. So `I` is the right child of `I'`,
  which is Stern–Brocot by induction.
- The case `s > q` is symmetric: `I` is the left child of `[p/q, (r−p)/(s−q)]`. ∎

**Lemma A (PSL_2(Z) pieces become dyadic affine).** Let `I` be a Farey interval. Let `γ ∈ SL_2(Z)`
have its pole `γ^{-1}(∞)` outside `I`, and suppose `γ` is increasing on `I`. Then:
- `γI` is a Farey interval;
- `ΦγΦ^{-1}` restricted to `ΦI` is the increasing affine map `ΦI → Φ(γI)`, of the form
  `s ↦ 2^{k−k'} s + d` with `d ∈ Z[1/2]`, where `k` and `k'` are the depths of `I` and `γI`.

*Proof.*
- The denominator `c t + d` of `γ` has constant sign on `I`, as the pole is off `I`. After replacing
  `γ` by `−γ` if needed, it is positive. Then `γu_I` and `γv_I` have positive second coordinates.
- `det(γv_I, γu_I) = det(v_I, u_I) = 1`, and `γ` preserves the order because it is increasing.
  So `γI = [γu_I, γv_I]` is Farey, and it is Stern–Brocot by Lemma 0.
- `γ` is linear on vectors, so it sends mediants of `I` to mediants of `γI`. By induction it sends
  the subtree below `I` to the subtree below `γI`, address to address.
- `Φ` sends both subtrees to the dyadic subtrees below `ΦI` and `Φ(γI)`, address to address. The
  affine map `ΦI → Φ(γI)` also preserves dyadic addresses.
- So `ΦγΦ^{-1}` and that affine map agree on the dense set of subtree endpoints of `ΦI`. Both are
  continuous, so they agree on `ΦI`.
- The lengths are `2^{-k}` and `2^{-k'}`, and the endpoints are dyadic, so `d ∈ Z[1/2]`. ∎

**Lemma B (converse).** Let `D` and `D'` be standard dyadic intervals and `α : D → D'` the
increasing affine map. Then `Φ^{-1}αΦ` restricted to `Φ^{-1}D` is an element of `PSL_2(Z)`.

*Proof.*
- `I = Φ^{-1}D` and `I' = Φ^{-1}D'` are Stern–Brocot intervals.
- `γ = [v_{I'} u_{I'}][v_I u_I]^{-1}` is in `SL_2(Z)`, since both matrices have determinant `1`. It
  maps `u_I ↦ u_{I'}` and `v_I ↦ v_{I'}`, so `γI = I'`.
- Its pole is off `I`, since `γ` sends the positive cone spanned by `u_I` and `v_I` into the positive
  half plane. It is increasing on `I`.
- By Lemma A, `ΦγΦ^{-1}` is the increasing affine map `D → D'`, which is `α`. ∎

Checks 1 and 2 of `question_mark_localization.py` test Lemmas A and B in exact arithmetic.

**Step 1 (`ΦG_ZΦ^{-1} ⊆ P`).** Let `g ∈ G_Z` and `h = ΦgΦ^{-1}`. Fix `x ∈ R` and let `γ_−, γ_+` be
the pieces of `g` just left and right of `x`. They are defined, with no pole, on some
`[x − δ, x + δ]`, because `g` is finite and continuous there.
- *`x` rational.* Deep Stern–Brocot intervals `I_− = [x', x]` and `I_+ = [x, x'']` inside
  `[x−δ, x+δ]` exist: `x` is an endpoint at every depth after it appears. By Lemma A, `h` is dyadic
  affine on `ΦI_−` and on `ΦI_+`, which are one-sided neighbourhoods of the dyadic point `Φx`.
- *`x` irrational.* Some Stern–Brocot interval `I ⊂ (x−δ, x+δ)` contains `x` in its interior. By
  Lemma A applied to `γ_−` and to `γ_+` on `I`, `h` agrees with the dyadic affine map
  `Φγ_∓Φ^{-1}|_{ΦI}` on the left and right parts of the neighbourhood `ΦI` of `Φx`.
- *Ends.* Near `±∞`, `g(t) = t + n` with `n ∈ Z`, and `Φ(t+n) = Φ(t) + n`. So `h(s) = s + n` near
  `±∞`.
- *Conclusion.* Every point of `R` has a neighbourhood on which `h` has at most two dyadic affine
  pieces. By compactness of `[−N, N]` and the ends, `h` has finitely many pieces, each of the form
  `s ↦ 2^k s + d` with `d ∈ Z[1/2]`. An affine piece is determined by its restriction to any
  subinterval. So `h ∈ P`.

**Step 2 (`Φ^{-1}PΦ ⊆ G_Z`).** Let `h ∈ P`, `g = Φ^{-1}hΦ`, and `y ∈ R`. Let
`α_∓(s) = 2^{k_∓}s + d_∓` be the pieces of `h` left and right of `y`, valid on `[y−ε, y+ε]`.
- For `n` large, `α_∓` maps every standard dyadic interval of length `2^{-n}` inside `[y−ε,y+ε]`
  onto a standard dyadic interval. The image `[2^{k}j2^{-n} + d, 2^k(j+1)2^{-n} + d]` has length
  `2^{k−n}`, and its left end lies in `2^{k−n}Z` once `n ≥ k` and `d ∈ 2^{k−n}Z`.
- If `y` is dyadic, take the two standard intervals of length `2^{-n}` with endpoint `y`.
  Otherwise take the one containing `y` in its interior.
- By Lemma B, `g` agrees with a `PSL_2(Z)` element on each side of `Φ^{-1}y`. At the ends,
  `h = s + n` gives `g = t + n`. By compactness, `g ∈ G_Z`.
- Steps 1 and 2 give `ΦG_ZΦ^{-1} = P`. This is part 1 of the theorem, apart from the last bullet.

**Step 2′ (breakpoints are rational).** At a breakpoint `y` of `h ∈ P`, the map
`α_−^{-1}α_+ : s ↦ 2^c s + e` is nontrivial and fixes `y`.
- If `c = 0`, then `e ≠ 0` and there is no fixed point, which is impossible.
- So `y = e/(1 − 2^c) ∈ Q`.

**Step 2″ (matching of breakpoints; `ΦFΦ^{-1} = P_1`).**
- *Irrational `x`.* The argument of Step 1 shows that `g` is a single `γ` near `x` iff `h` is a
  single affine map near `Φx`. The direction (⇐) uses Lemma B on a standard dyadic interval
  containing `Φx` in its interior; this is possible because `Φx` is not dyadic. So the irrational
  breakpoints of `g` correspond exactly to the non-dyadic breakpoints of `h`.
- *Rational breakpoints are `C^1`.* At a rational breakpoint `x` of `g`, `η = γ_−^{-1}γ_+ ≠ 1`
  fixes `x`. An element `(a b; c d)` of `SL_2(Z)` with `|a+d| > 2` has fixed points solving a
  quadratic with discriminant `(a+d)^2 − 4`. This is never a square: `(|a+d| − m)(|a+d| + m) = 4`
  forces both factors to equal `2`, so `m = 0`. So `η` is parabolic, and `η'(x) = 1`. Hence `g` is
  `C^1` at `x`.
- *Irrational breakpoints are not `C^1`.* At an irrational breakpoint `x`, `η` is hyperbolic.
  At a fixed point `x = η(x)` of `η`, `η'(x) = (cx+d)^{-2}`, and `cx + d` is an eigenvalue of `η`
  with modulus `≠ 1`. So `g'(x+)/g'(x−) = η'(x) ≠ 1`, and `g` is not `C^1` at `x`.
- So `g ∈ G_Z` is `C^1` iff all its breakpoints are rational, iff (by the matching) all
  breakpoints of `h` are dyadic. By l.271–272, `F` is the set of `C^1` elements of `G_Z`. Hence
  `ΦFΦ^{-1} = P_1`.

**Step 3 (odd filtration, part 2).** Let `M` be odd and `A_M = (1/M)Z[1/2]`. Write `Br(h)` for the
finite breakpoint set of `h`.
- Every `h ∈ P` maps `A_M` into itself, since each piece `2^k s + d` does.
- `Br(h_1h_2) ⊆ Br(h_2) ∪ h_2^{-1}Br(h_1)` and `Br(h^{-1}) = h(Br(h))`. So `P_M` is closed under
  products and inverses.
- Every rational lies in some `A_M`, with `M` the odd part of its denominator. `A_M ∪ A_{M'} ⊆
  A_{lcm(M,M')}`.
- So `P = ⋃_M P_M` is directed. A finitely generated subgroup has finitely many generator
  breakpoints, all rational by Step 2′, so it lies in `P_M` for the lcm `M` of their odd parts.

**Step 4 (rescaling, part 3).** For `h ∈ P_M`, `σ_M h σ_M^{-1}(s) = M h(s/M)`.
- Its pieces are `2^k s + Md`, with `Md ∈ Z[1/2]`.
- Its breakpoints are `M·Br(h) ⊆ M A_M = Z[1/2]`.
- Near `±∞` it is `s + Mn`, a translation by an integer.
- So it lies in `P_1`.

**Step 5 (part 4).** Let `G_M = Φ^{-1}P_MΦ`. Then:
- `ψ_M G_M ψ_M^{-1} = Φ^{-1}σ_M P_M σ_M^{-1}Φ ⊆ Φ^{-1}P_1Φ = F`, by Steps 4 and 2″.
- By Step 1, `G_Z = Φ^{-1}PΦ = ⋃_M G_M` is directed, and every finitely generated `H ≤ G_Z` lies
  in some `G_M`.
- By Step 2″, `g ∈ G_M` iff `Φ` maps every irrational breakpoint of `g` into `A_M`. The dyadic
  breakpoints of `h` lie in `A_M` anyway.
- `G_1 = Φ^{-1}P_1Φ = F`. ∎

**Corollaries.**
- *C1.* If `F` is amenable, every `ψ_M G_M ψ_M^{-1} ≤ F` is amenable, hence so is `G_M ≅ ψ_M G_M
  ψ_M^{-1}`. A directed union of amenable groups is amenable. The converse holds because
  `F ≤ G_Z` and subgroups of amenable groups are amenable. `G_Z` is countable, since there are
  countably many finite lists of pieces and breakpoints. The same argument works for any property
  that is closed under subgroups and countable directed unions.
- *C2.* A subgroup `K ≤ H(R)` with all pieces in `PSL_2(Z)` is contained in `G_Z`. Its elements are
  homeomorphisms of `R` fixing `∞`, with finitely many pieces, as in Monod's definition. Apply C1.
  Conversely, `F ≤ H(R)` by l.132–134.
- *C3, C4.* Let `F ≤ G`, where `G` consists of finitely-piecewise `PGL_2^+(Q)` homeomorphisms of `R`.
  Such maps preserve Lebesgue null sets. If some element has a non-integral piece, part 1 of
  `f-overgroups-with-a-non-integral-rational-piece-are-nonamenable` applies: `G` is nonamenable, and
  no subgroup of `F` is co-amenable in `G`. Otherwise every element is finitely-piecewise
  `PSL_2(Z)`, so `G ≤ G_Z`, and C1 applies.

**Checks.** `experiments/thompson-f-overgroups-2026-09-17/question_mark_localization.py` prints
`OK 1`–`OK 4`:
- Lemma A on 300 Farey intervals;
- Lemma B on 200 dyadic pairs;
- Steps 3–4 on 60 random words in bumps with breakpoints in `(1/15)Z[1/2]`;
- the pullback `?^{-1}(1/3) = (3−√5)/2`, with the `t ↦ 3t` conjugate dyadic.

**Gaps and scope.**
- The properties of `Φ` in Notation are classical (Minkowski; Salem 1943). They were not re-read at
  source. The script checks them on the dyadic tree.
- The phrase "piecewise" in Lodha–Moore is read as "finitely many pieces", as in the imported route.
- No priority is claimed. The Minkowski conjugacy of `PPSL_2(Z)` with dyadic PL maps is classical
  for Thompson's `T`, and the extension to quadratic irrational breakpoints and the odd rescaling
  may be folklore.
