# sk-open-3 plan: the Fibonacci group as a usable object (2026-09-13)

Lane sk-open-3 (open explorer, lens: the object itself). Nothing here is reviewed.

**Target.** Make G_Fib = EL_3(LC(X_Fib, F_2) ⋊ Z) concrete enough that a reader can compute with it. Put at most a
short "Example" paragraph, with complete proofs, into the note `simple_kazhdan_sofic_group.tex`.
X_Fib is the Fibonacci subshift of σ: 0 → 01, 1 → 0. Put f_n = σ^n(0), so |f_n| is a Fibonacci number F.

**Prior in the repo, built on here and not repeated:**
- main's b965d63ba version of the note: Remark [the Fibonacci subshift], l.497-512 (return word abaab, first model
  SL_15(F_p)), and l.150-154, 831;
- `pestov-9-1-writeup-2026-09-13-part1.md` §2.4 (explicit generators);
- `pestov91-four-regular-expanders-and-limits-2026-09-13.md` (spectral gap from a Kazhdan constant).

The new content is the whole Fibonacci model sequence with sharp radius bounds, numerical constants, and the relation
presentation.

**1. Explicit finite models (main item).**
- Claim to prove: the periodic word f_n^∞ has exactly the same words of length L as X_Fib for every L ≤ |f_n| − 1.
  All of its words up to some length L_sub(n) lie in L(X_Fib); expected L_sub(n) ≈ (2+φ)|f_n|, the critical exponent.
- Consequence to prove. Take the generating set of the note: the involutions e_ij(s), s ∈ {1, u, u^{-1}, e_0}. The
  r-ball of G_Fib maps injectively into SL_{3N}(F_2), N = |f_n|, preserving every product that stays in the ball, as
  soon as N ≥ 2r+2 if L_sub is as expected (otherwise N ≥ 4r+1).
- Sharpness: circular-word models need N ≥ 2r+2. Compute the least N(r) over all circular words.
- The first model is SL_15(F_2) (N = 5).

**2. Explicit Kazhdan constant.** From the quantitative theorems of Ershov–Jaikin-Zapirain (Invent. Math. 2010) and
Ershov–Jaikin-Zapirain–Kassabov (Mem. AMS 2017), quoted verbatim from arXiv:0809.4095 and arXiv:1102.0031. It
transfers through the surjection EL_3(Z⟨x_1, x_2, x_3⟩) → G_Fib with the image generating set. This gives a numerical
lower bound for κ(G_Fib, S) and a uniform spectral gap for the Cayley graphs of the finite models. I only supply the
numbers; sk-expanders-limits owns the expander statement.

**3. The ring by generators and relations.**
- R_Fib = F_2⟨u^{±1}, p⟩ modulo: p² = p; p commutes with u^j p u^{-j}; the products of translates spelling each
  minimal forbidden word of Fibonacci vanish (lengths 2, 3, 5, 8, …; e.g. p · u^{-1}pu = 0 because 11 is forbidden).
- Proof sketch: Stone duality plus normal forms Σ f_j u^j.
- Decide by reader merits whether it earns a sentence.

**4. Machine check (MSI, small).**
- Compute L_sub(n), the equality range, and N(r) combinatorially.
- Build the ball B(r) exactly (r ≤ 2, possibly 3) as 3×3 matrices over R_Fib, with window tables on L(X_Fib).
- Verify injectivity and partial multiplicativity of the model at the predicted N, and failure below it.
- A computation is evidence, not proof: every statement proposed for the note gets a written proof.

**Why useful.** The theorem is abstract. One example with explicit numbers makes it checkable and quotable: models
along Fibonacci numbers, the first model SL_15(F_2), a numerical Kazhdan constant. The expected cost is about 5–8
lines of the note.

**Not duplicated:**
- sk-generators: minimal numbers of generators, three involutions. I use the note's fixed generating set only.
- sk-lef-growth: growth asymptotics against the recurrence function. I give exact constants for one subshift.
- sk-expanders-limits: the expander theorem. I supply constants only.
- sk-lef-short: the general LEF proof.

**Outputs.**
- `research/artifacts/sk-open-3-fibonacci-*-2026-09-13.md`.
- Cairn nodes on the Fibonacci models (wired to `infinite-simple-kazhdan-hyperlinear-group`).
- `research/artifacts/sk-open-3-proposal-2026-09-13.md`.
