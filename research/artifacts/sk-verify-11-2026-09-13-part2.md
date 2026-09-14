# sk-verify-11 part 2: the time-complexity host obstruction, checked at source, and rev4's printed item (d)

Lane sk-verify-11, 2026-09-13 ~22:05 CDT. Part 1 (5b71e3c10c) passed host-b Lemma A and Theorems B–D, host-a Lemma A with A1 and A2, and sk-wp-host Theorem B. This part covers:
- sk-wp-host Theorem A;
- the KMS source check;
- line-by-line verdicts on sk-editor-4's draft text of item 71(d), `sk/drafts/rev4-partC.tex` as of 21:40, l.16–138.

## 1. `no-decidable-group-contains-every-fp-rf-group` (sk-wp-host Theorem A): PASS
**Route.** `no-decidable-group-contains-every-fp-rf-group-proof` → `uniform-wp-bound-excludes-bh-universal-targets` → `kms-arbitrarily-hard-fp-rf-groups`. Re-derived:
- **Host bound.** `t(n)` is the maximum running time over words of length at most `n`. It is recursive and non-decreasing, and `WP(U) ∈ F(t)`.
- **Step 1 (diagonal).** Reserved inputs `x_(i,c)` and a clocked simulation for `B = c·g(c|x|) + c|x| + c` steps, with the answer inverted. So `X` is recursive and `X ∉ F(g)`.
- **Step 2.** Theorem 4.21 gives a f.p. RF `G` with `WP(G)` as hard as `X`. If `WP(G) ∈ F(g)`, then `X ∈ F(g)`, since `F(g)` is closed under `T ↦ C·T(Cn) + Cn + C` for non-decreasing `g`.
  - **Nit:** the constant `C_2 = C·C_1 + C + C_1` in `kms-arbitrarily-hard-fp-rf-groups-citation` misses the term `C²C_1 n`. `C_2 = C²C_1 + C·C_1 + C + C_1` works. No effect on the conclusion.
- **Step 3.** Substituting fixed words `w_s` for the generators of `G`: the word problem of `G` is decidable in time `T(Ln) + O(Ln)`, which again lies in `F(g)`.

**Source check** (my own fetches on MSI, 2026-09-13): the journal PDF of KMS, Bull. Math. Sci. 7 (2017) 309–352, `https://link.springer.com/content/pdf/10.1007/s13373-017-0103-z.pdf` (open access, text extracted with ghostscript). Crossref confirms 7(2), 309–352.
- §1.3, the pseudo-order: "For two functions f, g we write f ≼ g (f is smaller than g) i[f] there exists a constant C such that for any n, f(n) ≤ Cg(Cn) + Cn + C."
- Definition 2.2(a), p. 319: "We say that an algorithmic problem A is as hard as an algorithmic problem B if for any decision algorithm for A which solves the problem in time T_A there exists an algorithm for B that solves it in time ≼ T_A." The relation glyph is lost in extraction and fixed by §1.3.
- Theorem 4.21, p. 345: "For every recursive set of natural numbers X and every recursive function g(n) there exists a finitely presented residually finite solvable of class 3 group G such that the word problem in G is as hard as the membership problem in X and polynomially reduces to it; the Dehn function G is bigger than g(n)."
- Theorem 4.22, p. 346: "For every recursive function f and a recursive set X of natural numbers, one can construct two residually finite finitely presented solvable of class 3 groups G1,G2. Both groups have depth functions greater than f. …"
- **Numbering.** Journal 4.21/4.22 correspond to arXiv v5 Theorems 4.18/4.19 (`t:rfg`, `t:rhog` in `KMS-322.tex`). Main's time-complexity import cites journal numbering and is correct. sk-wp-host's "Theorem 4.19" is the arXiv numbering. Any locator in the note, whose bibitem is the journal, must be 4.21 or 4.22.
- **Caution.** arXiv v5 has no quantitative Definition 2.2. It defines only polynomial reductions of machines (l.467–479). The ≼-form hardness is a journal addition, so the quantitative import rests on the journal version, which I read.

**Model tests.**
- The hypothesis "contains every f.p. RF group" is satisfiable: the host of `simple-kazhdan-lef-host-for-recursive-lef-groups`.
- Finite or trivial `U`: vacuous and consistent.
- Higman's universal f.p. group contains every recursively presented group and has unsolvable WP. Consistent.
- A `G_Y` with recursive language has solvable WP, so by Theorem A it misses some f.p. RF group. Consistent: the universal host is a different group.
- Simplicity plays no role in A or B, and neither needs the host to be LEF, except B(a), which needs LEF growth.

## 2. Rev4 printed text of item (d): `sk/drafts/rev4-partC.tex` l.16–138
**Corollary `cor:host`, l.16–22: PASS.**
- "Such a group" is the host of `cor:lef`.
- The iff for sets of f.g. groups is exactly `simple-kazhdan-lef-host-iff-lef-and-countably-many-types`. The last sentence is the countability of recursive presentations and of f.g. linear groups.

**Proof, l.25–26 (⇐ and subgroups): PASS.**

**Proof, l.26–52 (isolation): PASS-WITH-FIXES (unclear; 0 net lines).**
- The mathematics is §1 of part 1.
- "preserve the products that stay in this set" is the weaker partial-model form. It suffices, because for fixed `γ, γ′` the product `γγ′` lies in `{1, γ_1, …, γ_k}` for large `k`.
- The sentence at l.46–50 asserts "embeds" without its one-line reason. Verbatim fix:

Before (l.46–50):
```latex
$\prod_\omega\mathrm{Sym}(\Sigma_k)$, sending $\gamma$ to the class of the
permutations acting by $\pi_k(\gamma)$ on the level $0$ and trivially on
the other levels embeds $\Gamma$ in the group $\Delta$ generated by
$a=(a_k)_k$ and $b=(b_k)_k$. Since $w_j(a,b)$ is the image of $\gamma_j$,
we get $\Gamma\le[\Delta,\Delta]$. Finitely many products and inequalities
```
After:
```latex
$\prod_\omega\mathrm{Sym}(\Sigma_k)$, sending $\gamma$ to the class of the
permutations acting by $\pi_k(\gamma)$ on the level $0$ and trivially on
the other levels is a homomorphism, injective as $\pi_k(\gamma)\ne1$ for
$\gamma\ne1$ and large $k$. It sends $\gamma_j$ to $w_j(a,b)$, where
$a=(a_k)_k$ and $b=(b_k)_k$, so $\Gamma\le[\Delta,\Delta]$ for the group
$\Delta$ generated by $a$ and $b$. Finitely many products and inequalities
```

**Proof, l.54–76 (the lamplighter host; shared with `cor:lef`): PASS on the parts I re-derived.**
- Λ is the affine group, generated by Δ and `z`, since `δzδ⁻¹` adds `1_δ`.
- Minimality: orbits contain `x + ⊕F_2`.
- Topological freeness:
  - translations have no fixed point;
  - for `δ ≠ e` and `h ∉ W ∪ δW ∪ supp f`, we get `(δx+f)(h) = x(δ⁻¹h) ≠ x(h)`, and both coordinates are free inside the cylinder.
- Generation of `R_Δ` by `u_s^{±1}` and `χ`.
- The simplicity transfer is rev3's text, which both rev3 referees passed.

**Proof, l.78–105 (finite models without a base point; new in rev4; `cor:lef` scope, sk-verify-9 and sk-verify-8): no error found in a spot check.**
- The affine permutations of `Y_n = F_2^{Q′_n}` compose as in Λ for large `n`. Checked: `(δ_1,f_1)(δ_2,f_2) ↦ y ↦ σ(δ_1)σ(δ_2)y + Σ_{f_2} 1_{σ(δ_1)σ(h)} + Σ_{f_1} 1_{σ(h)}`, which agrees with `(δ_1δ_2, δ_1f_2 + f_1)` once `σ_n` is injective and multiplicative on the relevant finite set, including the F_2 cancellation.
- The covariance display holds uniformly in `y`.
- Column `y` of `Φ_n(r)` is `Σ_ξ f_ξ(ξx) e_{ξy}` with `x = y∘σ_n`, so the nonvanishing argument is correct.
- Point indicators and translations `1_q` generate `M_{2^{|Q′_n|}}(F_2)`.

Not reviewed in depth, because it is outside this lane's items.

**Proof, l.107–122 (Whitehead): PASS.** Both displays re-derived over F_2 (part 1 §4). `ξ ↦ diag(u_ξ,1,1)` is used only as a homomorphism into `GL_3`, and `[Λ,Λ]` lands in `G_Δ`.

**Proof, l.124–131 (second statement): PASS-WITH-FIXES (optional; +0 lines).** "which is a countable LEF group" gives no reason. Optional:
```latex
which is a countable LEF group, as finite subsets lie in finite products.
```

**l.134–138 (unsolvable word problem): PASS-WITH-FIXES (+1 line).** The mathematics is §1. Two fixes:
- (i) "The group" suggests uniqueness, but the argument applies to every f.g. group containing all f.p. RF groups.
- (ii) "these can be arbitrarily hard~\cite{KMS}" paraphrases what KMS do not print. They print "as hard as the membership problem in X" for every recursive X (Theorem 4.21, in the ≼ sense of their Definition 2.2(a)). "Arbitrarily hard" then follows from the time hierarchy. Use their wording and the verified journal locator.

Before (l.134–138):
```latex
The group in the last statement of Corollary~\ref{cor:host} has
unsolvable word problem: a recursive bound on the running time of an
algorithm for it would bound, up to a linear change of word length, the
time complexity of the word problems of all finitely presented residually
finite groups, and these can be arbitrarily hard~\cite{KMS}.
```
After:
```latex
Every group as in the last statement of Corollary~\ref{cor:host} has
unsolvable word problem: a recursive bound on the running time of an
algorithm for it would bound, up to a linear change of word length, the
time complexity of the word problems of all finitely presented residually
finite groups, and these can be as hard as the membership problem of any
recursive set~\cite[Theorem~4.21]{KMS}.
```
The bibitem (partD l.121–125) matches Crossref: Bull. Math. Sci. 7(2) (2017) 309–352, doi 10.1007/s13373-017-0103-z.

**Abstract (partA l.37–43) and introduction (l.85–96): PASS for item (d).** "one such group contains every finitely generated linear group and every recursively presented finitely generated group that is locally embeddable into finite groups" is exactly `cor:host`.

**Boone–Higman sentence (partC l.4–6): PASS.** The standard statement. The bibitem matches Crossref: J. Austral. Math. Soc. 18(1) (1974) 41–53, doi 10.1017/S1446788700019108.

## 3. Summary of verdicts
- PASS:
  - `countable-lef-groups-embed-in-two-generator-lef-groups` (both presentations, and `ι(Γ) ≤ [Δ,Δ]`);
  - `countable-lef-groups-embed-in-simple-kazhdan-lef-groups`;
  - `simple-kazhdan-lef-host-for-recursive-lef-groups`;
  - `no-countable-group-contains-all-fg-lef-groups`;
  - `simple-kazhdan-lef-host-iff-lef-and-countably-many-types`;
  - the route `lef-groups-embed-via-two-generator-lef-envelope`;
  - `recursive-lef-growth-hosts-miss-some-fp-rf-group`, unconditional now that journal Theorem 4.22 is checked at source;
  - `no-decidable-group-contains-every-fp-rf-group`, unconditional now that journal Definition 2.2(a) and Theorem 4.21 are checked at source.
- Rev4 item (d) text: PASS-WITH-FIXES. The two verbatim fixes above are the "embeds" sentence and the unsolvable-word-problem sentence, plus one optional clause.
- No FAIL.
