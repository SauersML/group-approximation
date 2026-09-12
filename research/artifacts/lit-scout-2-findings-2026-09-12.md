# Literature check for hyperbolic RF, Rokhlin entropy, percolation and Baum–Connes (lit-scout-2, 2026-09-12)

Scope: four requests from the coordinator, forwarded to the lanes named in each section.
- Items marked **[PDF]** were read from text extracted on MSI (`/scratch.global/sauer354/lit2/`).
- Items marked **[abstract]** were read only from the arXiv abstract page.
- Nothing here is imported into Cairn; lanes add -citation routes when they use a statement.

**Priority threats: none found.** No 2025–26 preprint settles any of these:
- CSP for an Sp(n,1) lattice;
- (∀G POS);
- p_c < p_u in new generality;
- Baum–Connes or Kadison–Kaplansky for Leavitt-type unit groups.

## (a) Hyperbolic residual finiteness and CSP (lanes `hyperbolic-rf`, `hyperbolic-rf-csp`)

**Lubotzky**, *Some more non-arithmetic rigid groups*, Contemp. Math. 387 (2005) 237–244, arXiv:1105.4785 **[PDF]**, §4:

> Remark 4.2. If there is one such uniform lattice L satisfying CSP, then there exists a hyperbolic group
> without any finite index subgroup and in particular, a non-residually-finite hyperbolic group.

> The question whether L satisfies the congruence subgroup property (CSP, for short) is still open.
> [...] As of now, the answer is not known for any single such L.

Here L is a uniform lattice in Sp(n,1), n ≥ 2, or in F_4^(−20).
- The proof uses, for "many" g, hyperbolicity of L/⟨⟨g⟩⟩, and the lemma from Remark 4.1:

  > for L being an arithmetic subgroup of a simple algebraic group, the intersection of any infinite
  > collection of normal congruence subgroups must be finite and central.

- Contrapositive: if every hyperbolic group is residually finite, no uniform Sp(n,1) or F_4^(−20) lattice has CSP.
- **Credit note:** the route `non-rf-hyperbolic-via-sp21-congruence-property` re-proves this implication for Sp(2,1) and does not cite Lubotzky 2005.

**Tholozan–Tsouvalas**, arXiv:2207.14356v1 **[PDF]**, introduction:

> residual finiteness of Kapovich's examples is related to the congruence subgroup conjecture for
> quaternionic lattices, see [Lub05, §4].

**Tang**, arXiv:2305.15650v2 **[abstract]**: "If there is a non-residually finite hyperbolic group, then there is a non-residually finite rigid hyperbolic group."

**Sisto–Wilton**, arXiv:2410.00556v2 **[abstract]**, verbatim: "Assuming that every hyperbolic group is residually finite, we prove the congruence subgroup property for mapping class groups of hyperbolic surfaces of finite type. Under the same assumption, it follows that profinitely equivalent hyperbolic 3-manifolds are commensurable." A grep of the PDF found no Sp(n,1) statement.

**Bounded-rank almost-congruence** for quotients of Sp(n,1) lattices: no published statement found. The search was bounded, so novelty is unchecked.

## (b) Rokhlin entropy (lanes `rokhlin-entropy`, `gottschalk-positive-host`)

**Seward**, *Krieger's finite generator theorem for actions of countable groups II*, arXiv:1501.03367v4 **[PDF]**, introduction:

> POS: There is a free ergodic p.m.p. action G y (X,µ) with h^Rok_G(X,µ) > 0.
> INF: h^Rok_sup(G) = ∞.
> Both statements are known to be true when G is a countably infinite sofic group since sofic entropy is
> a lower bound to Rokhlin entropy. We do not know whether POS implies INF (see the discussion following
> Corollary 7.7).

> Theorem 1.11. Let P be a countable group containing arbitrarily large finite subgroups. If G is any
> countably infinite group with h^Rok_sup(G) < ∞ then h^Rok_sup(P × G) = 0.
> Thus (∀G POS)⇒(∀G INF).

> INF⇒RBS⇒INV+CPE+GOT+KAP
> (∀G POS)⇒(∀G INF).

Other sources:
- **Seward**, arXiv:1804.05269v3 **[abstract]**: "if a free ergodic action of a countably infinite group has positive Rokhlin entropy (or, less generally, positive sofic entropy) then it factors onto all Bernoulli shifts of lesser or equal entropy."
- **Alpeev–Seward**, *Krieger III*, arXiv:1705.09707v3 **[abstract]**: a non-ergodic finite generator theorem; sub-additivity and semicontinuity of Rokhlin entropy; ergodic decomposition and inverse limit formulas.
- **Hu–Xu–Zhang**, arXiv:2607.11549 (13 Jul 2026) **[abstract]**: positive Rokhlin entropy implies infinite L¹-orbit multiplicity, for countably infinite amenable groups only.

Not found:
- any post-2019 lower bound for Rokhlin entropy over a nonsofic group;
- any source proving POS for groups containing F_2.

Already cited on main: Seward's Theorems 6.6 and 7.6 and Corollary 4.1 (`infinite-rokhlin-supremum-forces-surjunctivity-citation`).

## (c) p_c < p_u and locality (lanes `bs-pc-pu`, `bs-pc-pu-2`)

- **Easo–Hutchcroft**, arXiv:2310.10983 (v1 17 Oct 2023) **[abstract]**. Schramm's locality conjecture for Bernoulli bond percolation on transitive graphs: if G_n → G locally and p_c(G_n) ≠ 1 for all n, then p_c(G_n) → p_c(G). It also gives a new proof that p_c < 1 for non-one-dimensional transitive graphs.
- **Tran–Nguyen**, arXiv:2609.07026 (7 Sep 2026) **[abstract]**. Locality of p_c for Bernoulli site percolation on infinite, connected, locally finite vertex-transitive graphs.
- **Terlov–Timár**, arXiv:2502.02560 (4 Feb 2025, rev. 14 Sep 2025) **[abstract]**. Weighted-amenability is equivalent to all finite unions of levels inducing amenable graphs. It proves a relaxed version of Hutchcroft's conjecture relating p_h and p_u on weighted-nonamenable graphs.
- **Hutchcroft–Pan**, arXiv:2409.12283 **[abstract]**, already cited in Cairn. Non-uniqueness at p_u for groups with an amenable wq-normal subgroup of exponential growth; co-heredity of strong non-uniqueness.

No 2025–26 preprint proving p_c < p_u beyond the known classes was found.

## (d) Baum–Connes and Kadison–Kaplansky (lanes `baum-connes-leavitt`, `kadison-kaplansky-tf`)

- **Meyer**, arXiv:2508.05726, Münster J. Math. 18 (2025) 245–247 **[abstract]**: "This note provides a counterexample showing that the assumptions that Chabert and Echterhoff have imposed in their permanence property of the Baum-Connes conjecture for group extensions cannot be simplified."
- **Lajoinie-Dodel**, arXiv:2512.21169 (24 Dec 2025) **[abstract]**. Baum–Connes for relatively hyperbolic groups with CAT(0) or virtually abelian parabolics satisfying rapid decay, via strongly bolic metrics.
- **arXiv:2501.07646** (13 Jan 2025, rev. 8 Sep 2025) **[abstract]**. Zero-divisors and units in group rings of torsion-free CAT(0) groups; about Kaplansky's zero-divisor and unit conjectures, not idempotents in C*_r.
- **Known and already cited:** V, and the Higman–Thompson and FSS groups, have the Haagerup property (Farley; Hughes, arXiv:0804.0610). Baum–Connes with coefficients then follows by Higson–Kasparov.
  - L_{F_2}(1,2)^× contains Kazhdan subgroups, so that route is closed there.
  - The known failures are of Baum–Connes with coefficients, for Gromov monsters (Higson–Lafforgue–Skandalis). No counterexample to plain Baum–Connes is known.

No 2025–26 result on Baum–Connes or Kadison–Kaplansky for Thompson-like, Leavitt-type or Kazhdan-with-expanders groups was found.
