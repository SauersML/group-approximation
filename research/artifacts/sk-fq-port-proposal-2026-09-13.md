# sk-fq-port: every finite field, ported to the rev4 architecture (2026-09-13)

This is lane sk-fq-port, wave 11, a proposal artifact with no new claims.

- **Target:** the landed rev4, `simple_kazhdan_sofic_group.tex` on main at c8b6021ca9, md5 9144d8536cdca9073d50ffb64b826c00, 771 lines. Line numbers below refer to that file.
- **Source:** the subsection in `research/artifacts/sk-general-statement-proposal-2026-09-13.md` (d7ef2a68fd), with the fixes G1–G3 from `research/artifacts/sk-verify-13-2026-09-13-part4.md`.
- **Why a port was needed:** that subsection was written against the pre-S1 draft. Its step "central iff scalar image" used the nonvanishing lemma, which rev4 removed. Rev4 proves simplicity first and gets marked convergence from injectivity into ∏_ω for every ω (l.228–236). The new third change below works in that architecture.
- **Scope:** n ≥ 3 only. Rank two stays out (decision 96).

## (a) Current text (l.294–297)
```latex
$e_{ij}(s)$ with $s\ne1$ also give expanders.\qed

% rev4.1 SLOT (gated on sk-verify-13 PASS of the LaTeX): every finite field,
% n>=3 variant of sk-general-statement (d7ef2a68fd).
```

## (b) Replacement for l.296–297: 16 source lines, verbatim
```latex
\subsection*{Other finite fields}
Theorems~\ref{thm:main} and~\ref{thm:general} hold over any finite field $\F_q$, with $S$ containing a
generator $\alpha$ of $\F_q$ and $\F_q$-linear $\varphi_k$, in this form: for $n\ge3$, $G=\EL_n(R)$ is Kazhdan,
its centre $Z$ consists of scalar matrices, and $G/Z$ is infinite, finitely generated, simple, and the
limit of the groups $\PSL_{nN_k}(\F_q)$, whose Cayley graphs form expanders. The proofs change in three
places. For $g\in K\setminus Z$, with $c_\xi$ nonzero on $U$, commuting with every $e_{ij}(e_V)$ gives
$g=cI_n$ with $c$ a unit of $\LC(Z,\F_q)$, and commuting also with the $e_{ij}(e_Vu_s)$ makes $c$ invariant,
so constant by minimality; so some such $h$ does not commute with $g$. With $w+1$ for $w$ in the small
sets and the $\epsilon_{ab}$, the matrices $k-I_n=(ghg^{-1}-h)h^{-1}$ and $k^{-1}-I_n=h(gh^{-1}g^{-1}-h^{-1})$
lie in $M_n(A_V)$ with no entry $\epsilon_{ab}$ for $a\notin B_w$, so $k$ is not scalar in $H_V\cong\GL_d(\F_q)$.
Only the copy $S_V$ of $\SL_d(\F_q)$ lies in $G$; it is perfect and its proper normal subgroups are
central, so the $[k,x]\in K$ with $x\in S_V$ give $S_V\subseteq K$, as otherwise $k$ would centralize $S_V$.
The kernel of $G\to\prod_\omega\SL_{nN_k}(\F_q)$ misses $e_{12}(1)$, so it lies in $Z$. If a word $x$ has scalar
image in infinitely many approximants, then for suitable $\omega$ its commutators with $G$ lie in this
kernel, so $xZ$ is central in $G/Z$ and $x\in Z$. With $F$ over $\F_q$ and $e_{ij}(\alpha)$ added to the
Kazhdan set of $\EL_n(F)$, the rest is unchanged.
```

## (c) Length and compile
- **Length:** +16 source lines replace 2 comment lines, a net +14. No new bibitem.
- **Compile:** rev4 plus this subsection (md5 7f5940cfa3a8ae610d035220492a260c, 785 lines) on MSI at `/scratch.global/sauer354/sk/fq-port`, texlive/2025, 3 passes, md5 identical on both ends.
  - 0 errors, 0 overfull, 0 undefined.
  - 1 underfull: the Champetier bibitem, the same as in rev4.
  - **9 pages**, against rev4's 8.
- So this does not fit the 8-page budget unless rev4.1's cuts (referee (c) K1–K5, −10 lines) make room. Main decides.

## (d) Trade-off (reader)
Theorems 1 and 2 stop depending on the choice of F_2, at the cost of one new fact the reader must trust: SL_d(F_q) is perfect with only central proper normal subgroups, for d ≥ 3 (classical). The headline stays binary, where the group itself is simple.

## (e) Status
- **Unreviewed:** this LaTeX and the new third change. Queued with sk-verify-13 (served by sk-verify-15, lines 35+).
- **Mathematics it rests on, already reviewed on main:**
  - simplicity modulo the centre over every F_q, `subshift-elementary-group-is-simple-modulo-centre` (ex-review-groups part1);
  - the non-scalar commutator, `root-localization-commutator-is-never-scalar` (sk-review-1 part4);
  - the F_q marked limit with expanders for n ≥ 3, `finite-simple-groups-converge-to-simple-kazhdan-group` (corrected forward; sk-review-2 part2);
  - sk-verify-13 part4's review of the earlier subsection (PASS-WITH-FIXES G1–G3; G1 and G2 are built in here).
- **The general-Λ form** (Theorem 2 over F_q) is re-derived below. It is a straight generalization of the Z-case nodes; there is no separate node.

## (f) Derivation check against rev4 l.132–294

### Hypotheses
- **F_q-linear φ_k.**
  - The ring-homomorphism step (l.226–228, "φ_k∘π = ρ_k on the finitely many such entries") needs π and ρ_k to be F_q-algebra maps out of the free F_q-algebra F. Linearity over the prime field is automatic; over F_q it is not.
  - Without it, φ_k(α) could be a matrix whose eigenvalues are Galois conjugates of α. Then a scalar word αI would map to a non-scalar matrix, and change 3 would fail.
  - Both instances satisfy it: the periodic models D_ℓ(f) (l.279–283) and the configuration models D_n(f) (l.379–382) are F_q-linear in f.
- **S ∋ α.** EL_n(F) over the free F_q-algebra is generated by e_ij(1), e_ij(α) and e_ij(τ_s).
  - By (1) (l.146), [e_il(α^{t−1}), e_lj(α)] = e_ij(α^t) and sums give e_ij(F_q), then e_ij(c·monomial) = [e_il(c), e_lj(monomial)].
  - F_q-linearity gives φ_k(α) = αI, so in both quotients e_ij(α) and e_ij(τ_α) have the same image. The marking by e_ij(s), s ∈ S, therefore contains the images of the whole Kazhdan set.
  - (T) of EL_n(F) comes from EJZ (F is a ring generated by α and the τ_s).
- **Theorem 1 over F_q** (l.263–291): S = {1, α, u^{±1}} ∪ {e_a}. The matrix units come from P and the D_ℓ(e_a) as before (a characteristic-free argument), and αI = φ_ℓ(α). So φ_ℓ(S) generates M_{N_ℓ}(F_q). The expander transfer e_ij(1) = image of ∏_a e_ij(τ_a) (l.292–294) is unchanged.

### Change 1: noncommuting root (l.164–177)
- **Characteristic-free parts:** the commuting criterion (l.165–166) and the detection ce_V ≠ 0 or e_Vc ≠ 0, where "equals 1 on U" becomes "nonzero on U". Diagonality, the vanishing of the u_ξ-coefficients (ξ ≠ e), and agreement of the constant coefficients on small sets are unchanged. So g = cI_n with c ∈ LC(Z,F_q), and the constant coefficient of cc^{-1} = 1 makes c nowhere zero.
- **Over F_2** the argument ended with c = 1. **Over F_q:**
  - if g also commutes with e_ij(e_V u_s) for small V and each generator s of Λ, then c e_V u_s = e_V u_s c = e_V (c∘s^{-1}) u_s, so c = c∘s^{-1} on every small V;
  - small sets are dense (l.160–162) and c is locally constant, so c∘s^{-1} = c;
  - so c is Λ-invariant, hence constant by minimality, and g ∈ F_q^×I_n is central.
- **Contrapositive:** g ∉ Z gives a small V and h ∈ {e_ij(e_V), e_ij(e_V u_s)} not commuting with g.
- **Model test** (the extra roots are necessary): c = 1 + (α−1)e_U with ∅ ≠ U ≠ Z clopen is a nonconstant unit. cI_n commutes with every e_ij(e_V) but not with e_ij(u_s) when sU ≠ U. So it is not central, and change 1 detects it.
- **Centre:** this also shows Z ⊆ F_q^×I_n ∩ G, and every scalar in G is central, so Z = G ∩ F_q^×I_n. That is "consists of scalar matrices" (F5-compliant).

### Change 2: tower step (l.179–204)
- **Margins.**
  - Small: V ∩ ξV = ∅ for ξ ∈ B_{2w+2}∖{e}, and f∘ξ constant on V for ξ ∈ B_{w+1} and f a coefficient of g or g^{-1}.
  - ε_ab = e_{aV}u_{ab^{-1}} for a, b ∈ B_{w+1}, so A_V ≅ M_{|B_{w+1}|}(F_q) and d = n|B_{w+1}| ≥ 3.
  - The product rule at l.181–183 needs b^{-1}a′ ∈ B_{2w+2}, which the margin gives.
- **Product formula with u_s.** An entry of g(h−I)g^{-1} is a sum of f u_a e_V u_s f′ u_b = f e_{aV} (f′∘(as)^{-1}) u_{asb}, with a, b ∈ B_w.
  - f is constant on aV because f∘a is constant on V (a ∈ B_w).
  - f′∘(as)^{-1} is constant on aV because f′∘s^{-1} is constant on V (s^{-1} ∈ B_1 ⊆ B_{w+1}).
  - So the entry lies in {0, ε_{a,(sb)^{-1}}}, with first index a ∈ B_w and (sb)^{-1} ∈ B_{w+1}.
  - Also h − I_n = ε_{e,s^{-1}}E_ij, with first index e ∈ B_w.
- **Inverse formulas (G2).**
  - Over F_q, h^{-1} = I_n − ε_{e,s^{-1}}E_ij ≠ h in general, so l.199's "h^{-1} = h" is replaced.
  - k − I_n = ghg^{-1}h^{-1} − hh^{-1} = (ghg^{-1} − h)h^{-1}.
  - k^{-1} − I_n = hgh^{-1}g^{-1} − hh^{-1} = h(gh^{-1}g^{-1} − h^{-1}).
  - Both lie in M_n(A_V), because ghg^{-1} − h = g(h−I)g^{-1} − (h−I) and h^{±1} ∈ I_n + M_n(A_V). With yy′ = y′y = eI_n as at l.200–201, k ∈ H_V ≅ GL_d(F_q).
- **Not scalar.**
  - Right multiplication by h^{-1} keeps first indices: ε_{ab}ε_{e,s^{-1}} = δ_{be}ε_{a,s^{-1}}. So every entry of k − I_n involves only ε_ab with a ∈ B_w, and the rows of k at the levels aV with a ∈ B_{w+1}∖B_w are identity rows. That set of levels is nonempty because Λ is infinite.
  - A scalar (1−e)I_n + μeI_n has those rows equal to μ times identity rows, so μ = 1 and k = I_n. But k ≠ 1 because g and h do not commute. So k is not scalar.
- **G1.** Transvections e_pq(ε_ab) generate only the copy S_V ≅ SL_d(F_q) = EL_d(F_q) in G, since GL_d(F_q) ≠ SL_d(F_q) for q > 2. This replaces l.187–189's "H_V lies in G".
- **Normal subgroup.** For x ∈ S_V: [k,x] = k·(xk^{-1}x^{-1}) ∈ K, and det[k,x] = 1, so [k,x] ∈ K ∩ S_V, which is normal in S_V.
  - Suppose K ∩ S_V ⊆ Z(S_V). Then [k,xy] = [k,x]·x[k,y]x^{-1} = [k,x][k,y], so x ↦ [k,x] is a homomorphism to an abelian group. It is trivial because SL_d(F_q) is perfect for d ≥ 3.
  - So k centralizes S_V, and the centralizer of SL_d(F_q) in GL_d(F_q) is the scalars. That contradicts "not scalar".
  - So K ∩ S_V is a noncentral normal subgroup of the quasisimple SL_d(F_q) (d ≥ 3), so S_V ⊆ K and e_pq(e_V) = e_pq(ε_ee) ∈ K. This replaces l.202–204's "GL_d(F_2) = PSL_d(F_2) simple".
- **Level ideal** (l.206–212): characteristic-free, unchanged. So every normal K ⊄ Z equals G, and G/Z is simple. It is infinite because Z is finite and G is infinite (l.151–152).

### Change 3: marked limit without the nonvanishing lemma (l.214–238)
- **Ultraproduct map.** For every nonprincipal ω, the φ_k give a unital F_q-algebra homomorphism R → ∏_ω M_{N_k}(F_q) and a group homomorphism G → ∏_ω SL_{nN_k}(F_q) (l.228–232).
  - Its kernel is normal and misses e_12(1), whose image e_12(I) ≠ I. By simplicity of G/Z, the kernel lies in Z. This replaces "so it is trivial" at l.233.
- **Words in Z.** If x ∈ Z, then x = μI_n with μ ∈ F_q^×. The entries of x − μI_n vanish in R, and φ_k∘π = ρ_k on these finitely many entries for large k (F_q-linearity gives φ_k(μ) = μI). So the image of x in SL_{nN_k}(F_q) is μI for large k, and x is trivial in PSL_{nN_k}(F_q).
- **Words not in Z.**
  - Suppose infinitely many approximants give x a scalar image μ_kI. Take ω containing those k along which μ_k is constant, possible as F_q^× is finite. Then x maps to a central element of ∏_ω SL_{nN_k}(F_q).
  - So [x,y] lies in the kernel ⊆ Z for every y ∈ G, and xZ is central in G/Z.
  - G/Z is infinite and simple, hence nonabelian with trivial centre, so x ∈ Z. Contradiction.
  - So each word not in Z is nontrivial in PSL_{nN_k}(F_q) for all but finitely many k.
- **Conclusions.**
  - With the words in Z, this is marked convergence of the PSL_{nN_k}(F_q), marked by the images of e_ij(s), to G/Z.
  - N_k → ∞ because G/Z is infinite.
  - (T) of EL_n(F) gives expanders for the SL_{nN_k}(F_q) on the images of the Kazhdan set (e_ij(1), e_ij(α), e_ij(τ_s)), which lie in the marking. Quotient graphs of expanders are expanders, so the PSL approximants expand too.
  - PSL_{nN_k}(F_q) is simple because nN_k ≥ 3.

### Model tests
- **q = 2:** α = 1, Z = 1, SL = GL = PSL, and each change collapses to the rev4 text (the extra roots are harmless).
- **Non-minimal Z:** a closed invariant proper subset gives a proper level ideal. The covering step fails, as it should.
- **Noncentral scalar-like units:** see the change 1 model test.
- **n = 2:** excluded. EJZ and the level-ideal step (l ∉ {p,q}) both need n ≥ 3.
- **Non-F_q-linear models:** a Frobenius-twisted φ_k(α) = α^pI breaks "words in Z have scalar image μI" (the image is μ^pI in some coordinates, still scalar). A mixed twist diag(α, α^p) is non-scalar, which is why F_q-linearity is a hypothesis.

## Not done
- No new Cairn node: the Z-case mathematics is already on main, and the general-Λ form is this derivation.
- No journal locator for "SL_d(F_q) is perfect and quasisimple for d ≥ 3" (Jordan–Dickson; classical). The note would print it without citation, as rev4 does for GL_d(F_2) = PSL_d(F_2).
