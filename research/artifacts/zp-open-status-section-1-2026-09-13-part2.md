# Open status of Zaremsky's Section 1 problems, part 2 (2026-09-13)

Continuation of `zp-open-status-section-1-2026-09-13-part1.md`, which has the source list,
the search bounds, the verification levels (HTML / abstract / snippet) and the summary
table. This part has the details for Problems 1.11–1.25.

## Details, 1.11–1.25

### 1.11 — a finitely presented (or F_∞), infinite, torsion group
- **Status:** open.
- **Button–Thillaisundaram**, *Applications of p-deficiency and p-largeness*,
  arXiv:1007.2845 (abstract):
  - a group with a finite presentation of p-deficiency greater than 1 is large;
  - so Schlage-Puchta's infinite finitely generated p-groups are not finitely presented.
- This rules out one family of finitely presented candidates. Golod–Shafarevich and free
  Burnside groups give finitely generated infinite torsion groups that are not finitely
  presented.
- No 2025–2026 answer found (1 search).

### 1.12 — an amenable, non-elementary amenable group of type F_∞
- **Status:** open.
- **Grigorchuk**, *An example of a finitely presented amenable group not belonging to the
  class EG* (Sb. Math. 1998, snippet): an HNN extension of the first Grigorchuk group. It
  is finitely presented, amenable and not elementary amenable. Type F_∞ is not known.
- **Fisher**, *Improved algebraic fibrings*, arXiv:2112.00397, §1 (HTML): "it is not known
  whether there are examples of amenable groups of finite cohomological dimension that are
  not elementary amenable". That is the finite-cd version, which covers the type F
  strengthening of 1.12.
- Known sources of non-elementary amenable groups: groups acting on rooted trees and
  topological full groups (snippet, arXiv:1504.00610).
- No 2025–2026 answer found (3 searches).

### 1.13 — must Σ^∞(G) be open?
- **Status:** open; no answer found (1 search).
- **Computed Σ^∞ to test against:**
  - pure braid groups: Σ^∞(P_n) = Σ^{n−2}(P_n) (arXiv:1507.08597);
  - the golden-mean Thompson group F_τ: Σ^∞ = Σ² = Σ¹ minus a family of classes
    (arXiv:2309.12213, snippet);
  - Lodha–Moore groups (arXiv:2007.12518);
  - Houghton groups (arXiv:1808.00634).
  In each of these the invariants stabilize at a finite m, so Σ^∞ is open there.
- **Dense-or-empty results:**
  - Ershov–Zaremsky, *Dense and empty BNSR-invariants of the McCool groups*,
    arXiv:2505.18826 (v1 2025-05-24, final 2026-02-10, abstract): every Σ^m of a McCool
    group is dense or empty, with a characterization of which occurs.
  - Ardaiz Galé–Escartín Ferrer–Martínez Pérez, arXiv:2606.26033 (2026-06-24, abstract):
    for actions on contractible complexes with a contractible strong fundamental domain
    (and suitable stabilizers), the homological Σ invariants are empty or dense.
- **Observation (this lane, unreviewed):** a group of type F_∞ whose Σ^m are all dense but
  do not stabilize has a dense G_δ as Σ^∞, by Baire. Families of that kind are the natural
  place to look for a non-open Σ^∞.

### 1.14 — BNSR invariants of Röver–Nekrashevych groups
- **Status:** open; no computation found (2 searches).
- **Background (snippet level, from Zaremsky arXiv:2405.09722):**
  - for self-similar G ≤ Aut(T_d), the commutator subgroup V_d(G)′ is simple;
  - many RN groups have finite abelianization or are virtually simple, and then Σ is
    vacuous: the character sphere is empty.
- So the problem has content exactly for RN groups with infinite abelianization.
- **Finiteness properties of RN groups:** Skipper–Witzel–Zaremsky arXiv:1712.05361
  (simple groups separated by finiteness properties); Llosa Isenrich–Schesler–Wu
  arXiv:2510.01952.

### 1.16 — finitely presented simple groups with arbitrarily large (recursive) Dehn function
- **Status:** open; partial result known.
- **Zaremsky**, *Finitely presented simple groups with at least exponential Dehn function*,
  arXiv:2305.15176 (v2 2024-07-11, forthcoming in Michigan Math. J., abstract): the first
  finitely presented simple groups with at least exponential Dehn function. They are
  Röver–Nekrashevych groups built from self-similar representations of Baumslag–Solitar
  groups.
- **Repo region:**
  - Root `fp-simple-groups-with-arbitrarily-complex-word-problem` (open).
  - Route `arbitrarily-complex-fp-simple-via-hard-self-similar-groups` requires the open
    claim `fp-self-similar-groups-with-arbitrarily-hard-word-problem` and the imported
    Zaremsky arXiv:2405.09722 Theorem 1.1.
- **Link to Dehn functions:** a finitely presented group with Dehn function δ has word
  problem decidable within a recursive bound in δ (enumerate van Kampen diagrams of area at
  most δ(n)). So word problems beyond every recursive bound force Dehn functions beyond
  every recursive bound, and closing that route answers 1.16. The owner lane should write
  out the precise time bound before relying on this.
- **Kharlampovich–Myasnikov–Sapir**, arXiv:1204.6506 (snippet): finitely presented
  residually finite groups with arbitrarily large recursive Dehn function.

### 1.17 — Dehn function from cocompact action data (vague)
- **Status:** partly answered after the list's date.
- **Llosa Isenrich–Weis**, *A Brown Theorem for Dehn functions of graphs of groups*,
  arXiv:2608.07191 (2026-08-07, abstract; the HTML page returned 404):
  - G acts cellularly, cocompactly and without inversions on a simply connected CW
    complex X;
  - they bound the Dehn function of G above in terms of the vertex stabilizers' Dehn
    functions, the Dehn function of X, and the distortion of the edge stabilizers;
  - hypothesis: X is a tree, or each 2-cell stabilizer has finite index in the stabilizer
    of every edge of its boundary;
  - the abstract says this is "an answer to a question of Zaremsky in these cases".
- **Still open:** general X, and matching lower bounds. Theorem numbers not verified.

### 1.18 — a group of type F_∞ with Σ¹ ⊋ Σ² ⊋ Σ³ ⊋ ⋯
- **Status:** open; no example found (1 search).
- **Finite chains known:** P_n has n−3 proper inclusions and then stabilizes
  (arXiv:1507.08597). Thompson's F has Σ² = Σ^∞ (Bieri–Geoghegan–Kochloukova; Morse-theory
  proof by Zaremsky arXiv:1501.06682, snippet). F_τ has Σ^∞ = Σ² (arXiv:2309.12213,
  snippet).
- **Houghton groups:** H_n is of type F_{n−1} but not F_n (Lee arXiv:1212.0257), so not a
  candidate. Surface Houghton groups: arXiv:2403.04941.
- **Candidates to examine:** the McCool groups (arXiv:2505.18826, dense-or-empty
  characterization) and infinite-dimensional Thompson-like groups of type F_∞.

### 1.19 — RAAG virtual-kernel conjecture
- **Status:** open; no answer found (1 search).
- **Background:**
  - for χ: A_Γ → Z, the kernel is of type F_n iff [χ] and [−χ] lie in Σ^n(A_Γ);
  - Σ^n of right-angled Artin groups: Meier–Meinert–VanWyk (and Bux–Gonzalez);
  - Bestvina–Brady.
- **Roy**, *Finitely presented kernels of right-angled Artin groups with abelian quotients*,
  arXiv:2607.08900 (2026-07-09, abstract): finite generation and finite presentation of
  kernels with abelian quotients, explicit presentations (generalizing Casals–Kazachkov–Roy
  and Dicks–Leary). This is related, not an answer: it treats kernels on A_Γ itself, not on
  finite-index subgroups.

### 1.20 — uncountably many simple groups of type FP_2? of type FP?
- **Status:** open; no answer found (3 searches).
- **Uncountable families, not simple:**
  - Leary, *Uncountably many groups of type FP*, arXiv:1512.06609 (Proc. LMS 2018);
  - Kropholler–Leary–Soroko, arXiv:1712.05826 (uncountably many quasi-isometry classes);
  - Brown–Leary, arXiv:2004.04550 (graphical small cancellation).
- **Llosa Isenrich–Schesler–Wu**, *Infinitely presented simple groups separated by
  homological finiteness properties*, arXiv:2510.01952 (2025-10-02, HTML):
  - Theorem 1.1: for every finite graph Γ there is a simple group G_Γ whose finiteness
    properties (F_n, FP_n(R), F_∞, FP_∞(R)) match the connectivity of the flag complex;
  - Theorem 1.4: every finitely generated H ≤ GL_n(Q) is a subgroup of a simple group with
    the same finiteness properties that quasi-retracts onto H;
  - this answers Zaremsky's Question 1.6 (Thompson-like non-finitely-presentable groups of
    type FP_2(Z)).
- These give countably many simple groups; an uncountable simple family was not found.

### 1.21 — G × Z of type F ⇒ G of type F?
- **Status:** open; no answer found (1 search).
- **Reduction (this lane, standard ingredients, unreviewed):**
  1. If G × Z is of type F, then G is a retract of it. So G is finitely presented, of type
     FP_∞, and has finite cohomological dimension; hence G is of type FP.
  2. By Wall, a finitely presented group of type FP has a finitely dominated K(G,1), with
     Wall obstruction σ(G) ∈ K̃_0(ZG).
  3. Conversely, for every such G, Mather's trick (Gersten's product formula
     σ(X × S¹) = 0) makes K(G,1) × S¹ homotopy finite, so G × Z is of type F.
  4. So 1.21 ⟺ every finitely presented group of type FP is of type F ⟺ σ(G) = 0 for all
     such G.
- **Consequences:**
  - The answer is yes whenever K̃_0(ZG) = 0. For torsion-free G that is Hsiang's
    conjecture, implied by the K-theoretic Farrell–Jones conjecture. It therefore holds
    for every class where that conjecture is known.
  - A counterexample needs a torsion-free group with K̃_0(ZG) ≠ 0.
- **Ferry–Ranicki**, *A survey of Wall's finiteness obstruction*, arXiv:math/0008070, §2
  (HTML): "At present, no example is known of a torsion-free infinite group π with
  K̃_0(Z[π]) ≠ 0". Hsiang conjectured K̃_0(Z[π]) = 0 for torsion-free π.
- Related: Section 4, Problems 4.06 and 4.07 (Rips complexes), which would imply a
  positive answer.

### 1.22 — a left-orderable simple group of type F
- **Status:** open.
- **Hyde–Lodha**, *Finitely presented simple left-orderable groups in the landscape of
  Richard Thompson's groups*, arXiv:2302.04805 (final 2023-12-23, to appear in Ann. Sci.
  ENS, abstract):
  - the first finitely presented simple groups of orientation-preserving homeomorphisms of
    R;
  - they are of type F_∞ and have infinite geometric dimension, so they are not of type F.
- **Burger–Mozes groups:** they are finitely presented, simple and torsion-free, and it is
  unknown whether they act nontrivially on R (snippet from the same paper). A yes would
  answer 1.22, as the list says.
- No 2025–2026 answer found (2 searches).

### 1.23 — is the Dehn function of BB_Γ a lower bound for all finitely presented kernels onto Z?
- **Status:** open.
- **Chang–García-Mejía–Migliorini**, *Complete classification of the Dehn functions of
  Bestvina–Brady groups*, arXiv:2507.07566 (v1 2025-07-10, revised 2025-12-30, abstract):
  - the Dehn functions of finitely presented BB groups are linear, quadratic, cubic or
    quartic;
  - explicit criteria on the defining graph decide the degree;
  - they also obstruct CAT(0) structures.
- **Dison**, arXiv:0705.4220: quartic upper bound for finitely presented BB groups.
- **Roy**, arXiv:2607.08900 (above): presentations of other kernels.
- The comparison between other kernels and BB_Γ was not found in these abstracts.

### 1.24 — Dehn function of Houghton's group H_n (n ≥ 3): polynomial? quadratic?
- **Status:** open; no answer found (3 searches).
- **Lee**, *Geometry of Houghton's groups*, arXiv:1212.0257 (abstract):
  - H_n is of type FP_{n−1} but not FP_n;
  - H_n acts on an n-dimensional CAT(0) cube complex;
  - finite presentations for n > 3;
  - exponential isoperimetric inequalities for n > 2.
- No polynomial upper bound or super-polynomial lower bound found.
- **Repo:** `houghton-carmichael-sections-have-unbounded-edge-area` proves divergent
  filling area for one family of conjugacy sections. The owner lane should check whether
  it implies any lower bound on the Dehn function; it is not obviously one.

### 1.25 — does every countable group embed in a simple group of type FP_2?
- **Status:** open.
- **Source of the question:** Llosa Isenrich–Schesler–Wu, arXiv:2510.01952, Question 1.12
  (HTML): "Does every countable group embed in a simple group of type FP_2(Z)?". Their
  Questions 1.10 and 1.11 ask the GL_n(C) version of Theorem 1.4 and whether every
  finitely generated linear group embeds in a finitely generated self-similar group.
- **Partial:** Theorem 1.4 there embeds every finitely generated subgroup of GL_n(Q) in a
  simple group with the same finiteness properties.
- **Leary** (arXiv:1610.05813): every countable group embeds in a group of type FP_2, not
  simple.
- **Possible tool:** Fournier-Facio–Wu–Zaremsky, *Abstract twisted Brin–Thompson groups*,
  arXiv:2603.24687 (snippet): every finitely presented simple group embeds in a finitely
  presented abstract twisted Brin–Thompson group.
- No 2026 answer found (2 searches).
