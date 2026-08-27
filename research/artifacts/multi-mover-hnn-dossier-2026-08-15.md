# Full proof dossier: multi-mover collapse, matrix metrics, ascending-HNN compression, soficity, and exact approximation radicals

**Date:** 2026-08-15  
**Purpose:** turn the mathematical ideas in Francesco Fournier-Facio's message into a proof-level research note, audit the proposed removal of condition (iii), explain the operator/rank/Hilbert--Schmidt metric switching, and push the ascending-HNN/soficity route past the point reached in the message.

---

## 0. Executive verdict

The complete proof audit now reaches twenty distinct finish lines.

1. **The three matrix metrics have separate, necessary jobs.**  Operator norm controls the size of the algebraic/covariance error where it occurs; rank controls how much of the matrix space can carry that error; Frobenius/Hilbert--Schmidt norm turns those two controls into Hilbert-space energy, which is the geometry on which property \((T)\) acts.  The bridge is
   \[
   \|D\|_F^2\le \operatorname{rank}(D)\,\|D\|_{\mathrm{op}}^2,
   \]
   together with the exact commuting-involution identity
   \[
   \|u-v\|_F^2=4\operatorname{rank}(u-v).
   \]
   Section 32 shows that the *same cocycle defect* has one factorization suited to operator norm and another suited to rank, after which Hilbert--Schmidt control follows automatically.

2. **Francesco's max-displacement modification is correct at the estimate level, but the ordinary norm corona requires care.**  Replacing a distinguished mover by
   \[
   k_n=\max_i d_n(x_0,\gamma_i x_0)
   \]
   preserves the word estimate and gives an argmax mover of normalized mass one.  In a norm ultraproduct a finite pigeonhole argument can select a mover on an ultrafilter-large set.  In the ordinary matrix corona \(\prod M_{d_n}/\bigoplus M_{d_n}\), however, vanishing on a subsequence does not mean vanishing in the original corona.  Sections 6--7 repair this by finite block amplification: the finite-mover argument still proves **non-MF-ness**, but by itself does not force one predetermined mover defect into the MF radical.

3. **The current compression theorem is stronger and removes that historical limitation altogether.**  The repository's present involutive/projection/torsion collapse theorem says that if a property-\((T)\) subgroup is one-sidedly compressed and a finite-order witness centralizes the compressed copy while its conjugation orbit commutes, then **every fixed commutator** with that witness lies in the MF radical.  Sections 33 and 36 reconstruct the proof: exact commuting involution microstates, rank normalization, the Hilbert almost-cocycle, boundedness/circumcenter, Kazhdan spectral capture, one-sided compression, equal-rank reversal, projection collapse, and Fourier reduction for arbitrary torsion.

4. **A non-co-Hopfian property-\((T)\) group is enough for a finitely generated non-MF group, with any nontrivial finite lamp group.**  For
   \[
   G=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma)\rangle,
   \qquad
   X=G/\Gamma,
   \]
   the correct witness site is \(x_0=t\Gamma\).  Its stabilizer inside \(\Gamma\) is exactly \(\alpha(\Gamma)\), so every \(\gamma\notin\alpha(\Gamma)\) gives a nontrivial lamp defect which torsion collapse puts in the MF radical.  No finite-index, residual-finiteness, or soficity hypothesis is needed for this **non-MF** conclusion.

5. **The sofic branch is closed under two broad hypotheses.**  The HNN coset action \(G\curvearrowright G/\Gamma\) is amenable in complete generality.  It is sofic if \([\Gamma:\alpha(\Gamma)]<\infty\), by the finite-orbit telescope proof of Section 13; more generally it is sofic for arbitrary injective \(\alpha\) whenever \(\Gamma\) is universally action-sofic, in particular LERA or LERF, by Sections 30--31.  Section 29 proves from first principles the generalized-wreath permanence theorem needed to conclude that the corresponding finite-lamp wreath group is sofic.

6. **The collapse iterates through the entire HNN telescope and, in an MF skeleton, computes the radical exactly.**  With
   \[
   N=\bigcup_{n\ge0}t^{-n}\Gamma t^n,
   \qquad G/N\cong\mathbb Z,
   \]
   Section 37 constructs a canonical quotient
   \[
   \Phi_\infty:
   K^{(G/\Gamma)}\rtimes G
   \longrightarrow
   K_{\mathrm{ab}}^{(G/N)}\rtimes G
   \cong K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG
   \]
   and proves
   \[
   \ker\Phi_\infty\le\operatorname{Rad}_{\mathrm{MF}}.
   \]
   If the HNN skeleton \(G\) is MF, the target is MF as a subgroup of
   \(G\times(K_{\mathrm{ab}}\wr\mathbb Z)\), so
   \[
   \operatorname{Rad}_{\mathrm{MF}}=\ker\Phi_\infty.
   \]
   Thus the universal MF quotient is explicitly determined.

7. **The repository contains a complete formal-source chain for the core collapse endpoint.**  The current Lean chain in `InvolutionCollapseEndpoint.lean` imports exact involution lifts, rank/profile/cocycle modules, sequence-level circumcenters, and scaled Kazhdan transport and culminates in the unconditional theorem `actualCoronaMFInvisible_of_involutiveWitness`.  A static audit of the relevant collapse modules finds no `sorry` and no declared `axiom`.  GitHub exposes no hosted CI result for the audited head and this session did not rerun Lean, so this dossier deliberately says **formal proof source present and premise-free** rather than claiming an independently observed kernel/CI pass.

8. **In the concrete affine family, one quotient controls five approximation theories at once.**  Sections 42 and 46 prove that the explicit telescope quotient
   \[
   P=K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG_*
   \]
   is simultaneously the universal quotient seen by norm-matrix coronas, finite-dimensional complex unitary representations, finite-dimensional linear representations over **all fields**, finite quotients/profinite completion, and compact-group representations/Bohr compactification.  Every such map out of the original wreath group factors uniquely through `\Phi_\infty`.  For perfect finite lamps, `P=G_*`, so all five theories forget the entire lamp subgroup.

9. **The examples are nonlinear in the strongest finite-dimensional sense.**  Section 46 proves from the finite-residue-field argument that every finitely generated linear group over any field is residually finite.  Since the explicit wreath groups have a nontrivial finite residual, they are not linear over any field; a finite-extension argument shows they are not even virtually linear.  Their MF, finite-dimensional-unitary, all-fields-linear, Bohr, and finite residuals are all the same explicit telescope kernel.

10. **Perfect lamps produce explicit profinite twins with opposite MF behavior.**  Section 48 proves that for a nontrivial finite perfect lamp group (for example \(A_5\)), the sofic non-MF group \(W_K\) and the residually finite MF skeleton \(G_*\) have the same profinite completion, the same finite-index subgroup lattice with the same indices, the same category of finite actions, and the same finite-dimensional representation categories over every field via precomposition with the quotient.  Thus MF is not determined by profinite completion among finitely generated groups unless one imposes additional hypotheses such as residual finiteness on both groups.

11. **The approximation failure is finite-index hereditary.**  Section 49 proves the general finite-index induction formula
   
   \[\operatorname{Rad}_{\mathrm{MF}}(H)=H\cap\operatorname{Rad}_{\mathrm{MF}}(G)\]
   
   for every finite-index inclusion \(H\le G\), by inducing an arbitrary corona representation of \(H\) to a block-monomial corona representation of \(G\).  The same proof works for finite-dimensional and all-fields linear residuals, while the finite residual is handled by the finite-index core.  Consequently **every finite-index subgroup** of every concrete \(W_K\) is again non-MF, non-residually-finite, nonlinear over every field, and non-MAP, with exactly the same explicit residual \(R_K\).

12. **The telescope kernel is fully invariant.**  Since it equals the finite residual, every homomorphism \(W_K\to W_L\) sends \(R_K\) into \(R_L\).  Thus every endomorphism preserves the approximation-invisible kernel and descends canonically to the visible quotient; for perfect lamps the entire lamp subgroup is fully invariant, not merely normal or characteristic.

13. **For simple lamps, one torsion relation generates the whole invisible kernel.**  If \(S\) is finite nonabelian simple, then
   
   \[R_S=S^{(G_*/\Gamma_*)}=\langle\!\langle r\rangle\!\rangle\]
   
   for any nontrivial one-site lamp \(r\).  With \(S=A_5\), \(r\) can be chosen to be an involution.  Adding the single relation \(r=1\) gives the split quotient \(G_*\), changes the group from non-MF to MF, and nevertheless changes none of the finite/profinite/compact/finite-dimensional-linear/norm-corona target functors computed in the dossier.

14. **There is an infinite approximation-indistinguishable family.**  Section 52 proves from first principles that \(A_n\) is simple for every \(n\ge5\) and shows that
   
   \[W_n=A_n^{(G_*/\Gamma_*)}\rtimes G_*\]
   
   are pairwise **noncommensurable** (hence pairwise nonisomorphic) finitely generated sofic non-MF groups.  All of them have the same profinite and Bohr completions, the same finite-index subgroup lattice data, the same finite-action category, the same finite-dimensional representation categories over every field, and the same homomorphism sets into every norm matrix corona.  Their different simple types live entirely inside the fully invariant invisible radicals.

15. **One four-dimensional rational map realizes the entire hidden kernel for perfect lamps.**  Composing the split quotient with the explicit embedding \(G_*\hookrightarrow\mathrm{GL}_4(\mathbb Q)\) gives a single representation whose kernel is simultaneously the MF, finite-dimensional-unitary, all-fields-linear, Bohr, and finite residual.  The image is the same fixed subgroup of \(\mathrm{GL}_4(\mathbb Q)\) for the whole infinite family.

16. **MF is commensurability-invariant but not split-extension-closed.**  Finite-index induction proves MF is preserved in both directions across finite-index inclusions.  In sharp contrast, the concrete \(C_2\)-lamp group is a split extension of an elementary abelian, locally finite, residually finite, amenable MF group by the residually finite linear MF group \(G_*\), while the total semidirect product is sofic and non-MF.  The same split extension is neither residually finite nor MAP nor linear over any field.

17. **The quotient and the canonical section are both invisible to every target class tested here.**  For a perfect lamp, restriction along the proper retract \(G_*\hookrightarrow W_K\) and inflation along the noninjective split quotient \(W_K\twoheadrightarrow G_*\) are inverse bijections on Hom-sets into finite groups, residually finite groups, countable MF groups, compact groups, finite-dimensional linear groups over every field, and norm matrix coronas.  Thus the entire restricted target family is not jointly conservative.

18. **The twin phenomenon is hereditary at every finite index.**  Every finite-index subgroup \(H\le W_K\) for perfect \(K\) has the form \(R_K\rtimes J\) for a unique finite-index \(J\le G_*\).  The split quotient \(H\twoheadrightarrow J\) is invisible to all the same target classes, while \(H\) is non-MF and \(J\) is MF.  Hence the finite-index lattice is paired node-by-node across opposite MF behavior.

19. **Finite-index heredity is sharp: arbitrary normal-subgroup heredity fails maximally.**  The common radical \(R_K\) is itself locally finite, amenable, residually finite, MF, MAP, and has trivial intrinsic MF/finite-dimensional/linear/Bohr/finite residuals, even though inside \(W_K\) it is exactly all five ambient residuals.  Thus the formula of Section 49 cannot be extended from finite-index subgroups to arbitrary subgroups, not even to normal amenable residually finite ones.

20. **The wreath examples are provably not finitely presented.**  The height map separates the double cosets \(\Gamma_*t^n\Gamma_*\), giving infinitely many diagonal orbits on \((G_*/\Gamma_*)^2\).  A self-contained graph-product argument proves that a finitely presented transitive permutational wreath product with finitely generated stabilizer could have only finitely many such pair-orbits.  Therefore every \(W_K\) with \(1\ne K\) finite is finitely generated but not finitely presented; no finite-index subgroup is finitely presented, and no \(W_K\) is commensurable with a finitely presented group.

Finally, Section 39 replaces the abstract non-co-Hopfian input by the repository's concrete affine matrix group.  Conjugation by
\(D=\operatorname{diag}(2,2,2,1)\) gives a proper injective endomorphism of index \(8\); the resulting HNN skeleton embeds in \(\mathrm{GL}_4(\mathbb Z[1/2])\), hence is residually finite and MF.  For that concrete family, both **sofic non-MF-ness and the exact MF radical computation are unconditional at the mathematical theorem level** once the premise-free property-\((T)\) theorem supplied by the formal source is used.  Sections 41--54 sharpen this all the way to a single explicit telescope kernel which is simultaneously the MF radical, finite-dimensional unitary residual, finite residual, all-fields linear residual, and Bohr kernel; the same quotient controls the profinite and Bohr compactifications and forces nonlinearity over every field.  The final strengthening additionally proves finite-index heredity, full invariance, MF commensurability invariance, single-relation generation for simple lamps, an infinite pairwise noncommensurable family whose entire visible approximation theory is fixed while the hidden finite-simple radical varies, hereditary targetwise twin pairs at every finite index, failure of MF under split extensions even with an elementary abelian locally finite kernel, sharp failure of arbitrary-subgroup radical heredity, and a complete proof that every finite-lamp wreath example is not finitely presented.

### 0.1 Reader roadmap and precedence of later checkpoints

This dossier grew by successive proof-strengthening passes.  Several earlier sections therefore carry titles such as “final answer”, “proof-status ledger”, or “consolidated endpoint”; they are retained because they document the logical evolution and the repairs that were needed, but **Section 54 is the terminal theorem package**: Theorem 54.1 is the master structural statement and Theorems/Corollaries 54.2--54.6 record the final closure, heredity, and presentation consequences.  If an earlier status summary is weaker than a later one, the later statement supersedes the summary while the earlier proofs remain available as dependencies.

A practical reading order is:

- **Sections 1--8:** definitions, the three matrix metrics, the historical max-mover argument, and the norm-corona repair;
- **Sections 9--19:** ascending HNN structure, amenability, soficity, and comparison with the cited literature;
- **Sections 20--27:** the first proof checkpoint;
- **Sections 28--38:** the current involutive/projection/torsion collapse theorem and its full ascending-HNN consequences;
- **Sections 39--48:** the concrete affine matrix family, exact radical, universal quotient, linear/Bohr/profinite consequences, and profinite twins;
- **Sections 49--54:** the terminal strengthening: finite-index heredity, full invariance, a single invisible relation, the infinite alternating-lamp family, the four-dimensional rational envelope, restricted-target equivalence, split-extension failure, sharp radical non-heredity, exact non-finite-presentability, and the master theorem;
- **Appendix A:** referee and mechanical audit.

Thus a reader interested only in the strongest endpoint may read Sections 0, 39, 41--54, and Appendix A, consulting earlier sections when a proof dependency is cited.

---

## 1. Scope and source audit

The message refers historically to a circulated “Caleb” proof and an older “Theorem 4.1”.  I have not identified that historical proof as a separate artifact.  However, a deeper archive audit shows that the uploaded repository **does contain the current manuscript source** `non_mf_groups_exist.tex` (and a matching PDF), whose present involutive-compression theorem is strictly stronger for the ascending-HNN lamp application.  Thus this dossier keeps the historical mover argument separate, but Sections 28 onward also prove the current compression theorem and use it to remove the historical conditionality in the HNN application.  The earlier layers that can be proved completely are:

- every metric lemma and conversion used by the proposed modification;
- the max-displacement word estimate;
- the finite-mover pigeonhole mechanism;
- the corona-versus-ultraproduct distinction;
- a repaired non-MF argument in the norm-corona setting;
- all ascending-HNN structural statements;
- explicit Følner sets;
- group soficity of the ascending HNN extension when \(\Gamma\) is sofic;
- a finite-index theorem proving soficity of the coset action;
- the application to generalized wreath products via the published GKEP wreath-product theorem.

For the **historical action-form Theorem 4.1**, the multi-mover discussion below is intentionally conditional on the email's description of where (iii) entered.  This caveat disappears for the **current involutive-compression theorem** proved in Sections 32--34: in the ascending-HNN permutational-wreath application it gives a fixed, universal MF-radical defect and therefore bypasses (iii) altogether.

### Primary sources used

- Nicolas Monod and Sorin Popa, **On co-amenability for groups and von Neumann algebras**, arXiv:math/0301348: <https://arxiv.org/abs/math/0301348>.
- David Gao, Srivatsav Kunnawalkam Elayavalli, Gregory Patchell, **Soficity for group actions on sets and applications**, arXiv:2401.04945, current arXiv version v3 (2025-08-27), published in *Research in the Mathematical Sciences*: <https://arxiv.org/abs/2401.04945>.
- David Gao, **All actions of LERF groups on sets are sofic**, arXiv:2402.17150, current arXiv version v2 (2024-07-13): <https://arxiv.org/abs/2402.17150>.
- Javier Brude and Román Sasyk, **Metric approximations of unrestricted wreath products when the acting group is amenable**, arXiv:2004.05735: <https://arxiv.org/abs/2004.05735>.
- Yves de Cornulier, **Finitely presented wreath products and double coset decompositions**, arXiv:math/0509090: <https://arxiv.org/abs/math/0509090>.  Section 54.3 reproves the necessity direction needed here in the special transitive setting.
- Gabor Kun and Andreas Thom, **Nonsofic wreath products of residually finite groups**, arXiv:2608.06222, submitted 2026-08-06: <https://arxiv.org/abs/2608.06222>.

### Repository snapshot audited through GitHub

Repository: `SauersML/group-approximation`.  The initial research-card audit used commit
`fb434d2b28b899f16aa7166589ce8493b6936de3`.  The present referee pass resynchronized the manuscript, formal endpoints, and concrete affine files against the current audited `main` head
`7df16bbaa925c55a95b39996e9938b3b91311ac1` (2026-08-15 23:16:50 UTC).

Especially relevant:

- `research/multi-mover-collapse-criterion.md`
- `research/artifacts/multi-mover-verification-2026-08-15.md`
- `research/ascending-hnn-coset-action-sofic.md`
- `GroupApproximation/Sofic/LiteralBaseDoublingIndex.lean`
- `GroupApproximation/Sofic/CommutingLampCollapse.lean`
- `GroupApproximation/Sofic/CommutingLampQuotientSofic.lean`
- `non_mf_groups_exist.tex`

Exact current-source links used in the continuation audit:

- current manuscript at commit `7df16b...`: <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/non_mf_groups_exist.tex>
- explicit affine matrix model: <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Monsters/ExplicitLinearModel.lean>
- literal property-\((T)\) / collapse endpoint: <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/CommutingLampCollapse.lean>
- finite-index doubling argument: <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/LiteralBaseDoublingIndex.lean>
- exact P13 Hodge/property-\((T)\) certificate: <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean>
- premise-free transfer of property \((T)\) to the literal affine base: <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/LiteralBaseP13PropertyTBridge.lean>

The Lean file `CommutingLampQuotientSofic.lean` defines
\[
\operatorname{ModTwoLamp}(X)=X\to_0\mathbb Z/2\mathbb Z
\]
(in multiplicative notation), identifies the sign-free quotient with the corresponding semidirect product over the vertical ascending-HNN group, and contains the literal theorem
`literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF`.

No GitHub CI status or workflow run was returned for the audited commit, so this note does **not** claim that a hosted CI run passed.  Separately, a static audit of the checked-out source for the involutive-collapse chain (`InvolutionCollapse*.lean`, `ScaledKazhdanTransport.lean`, `ProjectionCompressionCollapse.lean`, and `TorsionSpectralCollapse.lean`) found no `sorry` and no declared `axiom`.  Thus the precise claim here is **a complete, assumption-free Lean proof chain is present at source level; hosted CI status was not available and the Lean kernel was not independently rerun in this session**.

---

## 2. Basic definitions

### 2.1 The norm matrix corona and MF groups

Let \(d_n\ge1\).  Put
\[
\ell^\infty(\mathbf M_{\mathbf d})
 =\prod_{n=1}^\infty M_{d_n}(\mathbb C),
\qquad
c_0(\mathbf M_{\mathbf d})
 =\left\{(x_n):\|x_n\|_{\rm op}\to0\right\}.
\]
The **norm matrix corona** is
\[
\mathcal Q_{\mathbf d}
 =\ell^\infty(\mathbf M_{\mathbf d})/c_0(\mathbf M_{\mathbf d}).
\]
A countable group \(G\) is operator-MF in the sense relevant here if it admits an injective homomorphism
\[
G\longrightarrow \mathcal U(\mathcal Q_{\mathbf d})
\]
for some sequence \(d_n\), equivalently an operator-norm asymptotic representation separating every nonidentity element.

For a bounded sequence \(x=(x_n)\),
\[
\|[x]\|_{\mathcal Q_{\mathbf d}}=\limsup_{n\to\infty}\|x_n\|_{\rm op}.
\]

#### Proof
Let \(L=\limsup\|x_n\|\).  If \(y_n\to0\), then
\[
\limsup\|x_n+y_n\|\ge
\limsup(\|x_n\|-\|y_n\|)=L,
\]
so the quotient norm is at least \(L\).  Conversely, for every \(\varepsilon>0\), there is \(N\) such that \(\|x_n\|\le L+\varepsilon\) for all \(n\ge N\).  Define \(y_n=-x_n\) for \(n<N\) and \(y_n=0\) for \(n\ge N\).  Then \(y\in c_0\) and
\(\sup_n\|x_n+y_n\|\le L+\varepsilon\).  Let \(\varepsilon\downarrow0\). ∎

Consequently,
\[
[x_n]=0\quad\Longleftrightarrow\quad \|x_n\|\to0.
\]
Vanishing merely along a subsequence is insufficient.  This elementary point becomes load-bearing in Section 7.

### 2.2 Rank distance

For matrices of size \(d\), define
\[
d_{\rm rk}(A,B)=\frac1d\operatorname{rank}(A-B).
\]
Unnormalized rank will also be used when the natural scale is an integer.

### 2.3 Normalized Hilbert--Schmidt norm

For \(D\in M_d(\mathbb C)\),
\[
\|D\|_{2,d}
 =\left(\frac1d\operatorname{Tr}(D^*D)\right)^{1/2}.
\]
The unnormalized Frobenius norm is
\[
\|D\|_{\rm F}=\sqrt{\operatorname{Tr}(D^*D)}=\sqrt d\,\|D\|_{2,d}.
\]

### 2.4 Sofic actions on sets

For an action \(G\curvearrowright X\), Gao--Kunnawalkam Elayavalli--Patchell call the action **sofic** if for every finite \(F\subset G\), finite \(E\subset X\), and \(\varepsilon>0\), there exist a finite set \(A\), a unital map
\[
\varphi:G\to\operatorname{Sym}(A)
\]
which is \((F,\varepsilon)\)-multiplicative, a finite set \(B\), a subset \(S\subset A\) with \(|S|>(1-\varepsilon)|A|\), and injective charts
\[
\pi_s:E\hookrightarrow B\qquad(s\in S)
\]
satisfying
\[
\pi_{\varphi(g)s}(x)=\pi_s(g^{-1}x)
\]
whenever both sides are required by the finite test.  See Definition 2.1 of arXiv:2401.04945.

Notice that **the map \(\varphi\) need not be free**.  Thus a group can have a sofic action even if the group itself is not known to be sofic.

### 2.5 Generalized wreath products

For a group \(K\), an action \(G\curvearrowright X\), and
\(K^{(X)}=\bigoplus_X K\), the generalized wreath product is
\[
K\wr_XG=K^{(X)}\rtimes G,
\]
where \(G\) permutes the coordinates according to its action on \(X\).

Gao--Kunnawalkam Elayavalli--Patchell prove:

> **GKEP Theorem 3.6.** If \(K\) and \(G\) are sofic groups and the action \(G\curvearrowright X\) is sofic, then \(K\wr_XG\) is sofic.

That theorem is a substantial published wreath-product approximation theorem; it is treated below as an imported theorem, not silently reproved.

---

## 3. Why three matrix metrics appear

The most useful conceptual summary is:

> **Operator norm controls how far; rank controls how much; Hilbert--Schmidt norm is the total quadratic energy.**

More precisely, singular values \(s_1(D),\dots,s_d(D)\) give
\[
\|D\|_{\rm op}=\max_j s_j(D),
\qquad
\operatorname{rank}D=\#\{j:s_j(D)>0\},
\qquad
\|D\|_{2,d}^2=\frac1d\sum_j s_j(D)^2.
\]
Thus operator norm is an \(L^\infty\)-type amplitude, normalized rank is an \(L^0\)-type support size, and Hilbert--Schmidt squared is an \(L^2\)-energy.

### Lemma 3.1 — the rank/operator-to-HS bridge

For every \(D\in M_d(\mathbb C)\),
\[
\boxed{
\|D\|_{2,d}^{2}
\le
\frac{\operatorname{rank}D}{d}\,\|D\|_{\rm op}^{2}.}
\]
Equivalently,
\[
\|D\|_{\rm F}^{2}
\le
\operatorname{rank}D\,\|D\|_{\rm op}^{2}.
\]

#### Proof
Let \(r=\operatorname{rank}D\).  Exactly \(r\) singular values are nonzero, and each is at most \(\|D\|_{\rm op}\).  Hence
\[
\operatorname{Tr}(D^*D)
 =\sum_{j=1}^d s_j(D)^2
 \le r\|D\|_{\rm op}^2.
\]
Divide by \(d\). ∎

This is the principal mechanism by which an error that has **small operator norm** and is supported on only \(O(k_n)\) dimensions becomes \(o(k_n)\) in Frobenius energy.

### Lemma 3.2 — nearby projections have equal rank

If \(p,q\in M_d(\mathbb C)\) are orthogonal projections and
\[
\|p-q\|_{\rm op}<1,
\]
then
\[
\operatorname{rank}p=\operatorname{rank}q.
\]

#### Proof
Suppose \(\operatorname{rank}p>\operatorname{rank}q\).  Since
\(\dim\operatorname{ran}p>\dim\operatorname{ran}q\), there is a unit vector
\[
v\in\operatorname{ran}p\cap(\operatorname{ran}q)^\perp.
\]
Then \(pv=v\) and \(qv=0\), so
\[
\|(p-q)v\|=1,
\]
contradicting \(\|p-q\|<1\).  Interchanging \(p,q\) excludes the reverse strict inequality. ∎

This explains why operator-norm covariance errors can yield **exact rank invariance** at sufficiently late stages.

### Lemma 3.3 — the exact commuting-involution identity

Let \(u,v\in M_d(\mathbb C)\) be commuting self-adjoint involutions:
\[
u=u^*,\quad v=v^*,\quad u^2=v^2=1,\quad uv=vu.
\]
Put \(T=u-v\).  Then
\[
T^2=2(1-uv),
\qquad
T^3=4T,
\]
\[
p:=\frac{T^2}{4}=\frac{1-uv}{2}
\]
is an orthogonal projection, and
\[
\operatorname{rank}T=\operatorname{rank}p.
\]
Consequently
\[
\boxed{
\operatorname{Tr}|u-v|^2=4\operatorname{rank}(u-v),}
\]
and
\[
\boxed{
\|u-v\|_{2,d}^{2}=4d_{\rm rk}(u,v).}
\]

#### Proof
Since \(u,v\) commute,
\[
T^2=(u-v)^2=u^2+v^2-uv-vu=2-2uv=2(1-uv).
\]
The product \(uv\) is self-adjoint and
\((uv)^2=u^2v^2=1\), so \(uv\) is an involution.  Therefore
\[
p=\frac{1-uv}{2}
\]
is its \((-1)\)-spectral projection, hence an orthogonal projection.  Since \(T^2=4p\),
\[
T^3=4Tp.
\]
But
\[
Tp=(u-v)\frac{1-uv}{2}
 =\frac{u-v-u^2v+uv^2}{2}
 =\frac{u-v-v+u}{2}=u-v=T,
\]
so \(T^3=4T\).

For any matrix \(T\), \(\ker T=\ker T^*T\); here \(T=T^*\), so
\[
\ker T=\ker T^2=\ker p.
\]
Thus \(\operatorname{rank}T=\operatorname{rank}p\).  Finally,
\[
\operatorname{Tr}|T|^2=\operatorname{Tr}(T^2)
 =4\operatorname{Tr}p=4\operatorname{rank}p
 =4\operatorname{rank}T.
\]
Divide by \(d\). ∎

### The conceptual pipeline

In the collapse proof the three metrics therefore have sharply different jobs.

1. **Operator norm:** the group homomorphism is represented by coordinate unitaries whose multiplication/conjugacy errors tend to zero in operator norm.  Operator norm is stable under multiplication by unitaries and supports spectral correction: an almost involution can be rounded to an exact involution, and nearly invariant projections eventually have the same rank.

2. **Rank:** after commuting involutions have been corrected exactly, their difference has a projection-valued support.  Rank counts that support *discretely*.  This produces an integer-valued displacement metric that is insensitive to tiny changes of eigenvalues and does not get diluted merely because the ambient dimension is huge.

3. **Hilbert--Schmidt:** property (T) is fundamentally Hilbertian.  The difference matrices are rescaled by the rank scale and regarded as vectors in Hilbert spaces.  The rank identity gives a controlled nonzero generator energy, while Lemma 3.1 makes covariance defects negligible in that energy.  Property (T) then forces an almost-cocycle to have an almost primitive/fixed center, contradicting the normalized generator mass.

The switching is therefore a designed chain
\[
\boxed{
\text{operator-norm algebra}
\longrightarrow
\text{rank support}
\longrightarrow
\text{Hilbert--Schmidt energy}
\longrightarrow
\text{property (T)}.}
\]

---

## 4. Property (T) gives finite generation

The email uses the fact that a discrete property-(T) group is finitely generated.  Here is a proof.

### Proposition 4.1
Every discrete group \(\Gamma\) with property (T) is finitely generated.

#### Proof
For a discrete group, a compact Kazhdan set is finite.  Let \(Q\subset\Gamma\) be a finite Kazhdan set and put
\[
H=\langle Q\rangle.
\]
Consider the quasi-regular representation of \(\Gamma\) on
\[
\ell^2(\Gamma/H).
\]
The vector \(\delta_H\) is fixed by every element of \(H\), hence by every element of \(Q\).  In particular it is a \((Q,0)\)-almost invariant unit vector.  By the Kazhdan property, the representation has a nonzero \(\Gamma\)-invariant vector.

A \(\Gamma\)-invariant vector on the transitive set \(\Gamma/H\) is constant.  A nonzero constant function belongs to \(\ell^2(\Gamma/H)\) only if \(\Gamma/H\) is finite.  Therefore
\[
[\Gamma:H]<\infty.
\]
Choose a finite set \(R\subset\Gamma\) of coset representatives.  Every \(g\in\Gamma\) can be written \(g=rh\) with \(r\in R\), \(h\in H\), so
\[
\Gamma=\langle Q\cup R\rangle.
\]
Thus \(\Gamma\) is finitely generated. ∎

### Corollary 4.2 — finitely many movers

Let \(\Gamma\curvearrowright X\), fix \(x_0\in X\), and put
\[
K=\operatorname{Stab}_\Gamma(x_0).
\]
Then there are finitely many \(\gamma_1,\dots,\gamma_m\in\Gamma\setminus K\) such that
\[
\Gamma=\langle K,\gamma_1,\dots,\gamma_m\rangle.
\]

#### Proof
Take a finite generating set \(S\) for \(\Gamma\).  Let
\[
S_{\rm mov}=\{s\in S:sx_0\ne x_0\}.
\]
Every generator in \(S\setminus S_{\rm mov}\) lies in \(K\), so \(K\cup S_{\rm mov}\) generates \(\Gamma\).  Enumerate the finite set \(S_{\rm mov}\). ∎

This formulation avoids an unnecessary subtlety: if a subgroup called \(H\) in the original theorem is smaller than the full stabilizer, one does **not** have to enlarge \(H\) merely for the displacement estimate.  One may use the full stabilizer \(K\) only as a bookkeeping set of zero-displacement letters.  If the original theorem already has \(H=\operatorname{Stab}_\Gamma(x_0)\), then of course \(K=H\).

---

## 5. The max-displacement lemma

We now isolate exactly what the proposed modification needs.

Let \(d_n\) be pseudometrics on the relevant finite-stage orbit models.  Write
\[
\delta_n(g)=d_n(x_0,gx_0).
\]
Suppose that for each fixed finite collection of group elements the pseudometrics are asymptotically left-invariant at an error \(e_n\):
\[
\big|d_n(gx,gy)-d_n(x,y)\big|\le e_n
\]
for the finitely many triples used in a fixed word.  In the exact rank model obtained after spectral correction, one can often take \(e_n=0\) eventually; allowing \(e_n\) makes the estimate robust.

Choose finitely many moving generators \(\gamma_1,\dots,\gamma_m\) as above.  From now on assume \(m\ge1\), which is exactly the nontrivial case in which a mover defect exists; if \(m=0\), then \(\Gamma\) fixes \(x_0\) and this max-mover branch of the collapse argument is vacuous.  Define
\[
\boxed{k_n=\max_{1\le i\le m}d_n(x_0,\gamma_i x_0).}
\]

### Lemma 5.1 — inverses cost the same scale

For every \(i\),
\[
d_n(x_0,\gamma_i^{-1}x_0)
\le k_n+e_n.
\]
In the exactly invariant case it equals
\(d_n(x_0,\gamma_i x_0)\).

#### Proof
By symmetry and left invariance,
\[
d_n(x_0,\gamma_i^{-1}x_0)
=d_n(\gamma_i x_0,x_0)
=d_n(x_0,\gamma_i x_0).
\]
With approximate invariance, insert the corresponding error. ∎

### Lemma 5.2 — word-length bound

For every fixed \(g\in\Gamma\) there is a constant \(C_g<\infty\) such that
\[
\boxed{\delta_n(g)\le C_g(k_n+e_n)}
\]
for all sufficiently late \(n\).  In particular, if \(e_n=o(k_n)\), then
\[
\delta_n(g)\le (C_g+o(1))k_n.
\]

#### Proof
Write \(g=s_1\cdots s_r\), where every \(s_j\) is either in the stabilizer \(K\) or is one of \(\gamma_i^{\pm1}\).  Set
\(g_j=s_1\cdots s_j\), with \(g_0=1\).  By the triangle inequality,
\[
\delta_n(g)
=d_n(x_0,g_rx_0)
\le\sum_{j=1}^r d_n(g_{j-1}x_0,g_jx_0).
\]
Approximate left invariance gives
\[
d_n(g_{j-1}x_0,g_{j-1}s_jx_0)
\le d_n(x_0,s_jx_0)+e_n.
\]
If \(s_j\in K\), then \(s_jx_0=x_0\), so the first term is zero.  If \(s_j=\gamma_i^{\pm1}\), Lemma 5.1 bounds it by \(k_n+e_n\).  Hence every letter contributes at most \(k_n+O(e_n)\), and
\[
\delta_n(g)\le r k_n+O(r e_n).
\]
Take \(C_g\) larger than the word length constant. ∎

This is precisely the place where a single distinguished mover had previously made the proof look special.  The maximum restores the same estimate.

### Lemma 5.3 — a top-scale mover always exists

For every \(n\), choose the least index \(i(n)\) satisfying
\[
d_n(x_0,\gamma_{i(n)}x_0)=k_n.
\]
Then the normalized displacement of that mover is exactly one:
\[
\frac{d_n(x_0,\gamma_{i(n)}x_0)}{k_n}=1
\]
whenever \(k_n>0\).

Since \(i(n)\) takes only finitely many values, some \(i_*\) occurs on an infinite subsequence.  In a norm ultraproduct along an ultrafilter \(\mathcal U\), exactly one of the sets
\[
\{n:i(n)=i\}
\]
is \(\mathcal U\)-large.

The crucial warning is that these two observations have different consequences in a norm ultraproduct and in a \(c_0\)-corona.  We turn to that now.

---

## 6. Ultrafilter pigeonholes versus norm-corona subsequences

### Proposition 6.1 — the subsequence implication is false in a norm corona

Let
\[
\mathcal Q=\prod_n M_{d_n}/\bigoplus_n M_{d_n}.
\]
From
\[
\|x_{n_j}\|\to0
\]
along one infinite subsequence, one cannot conclude \([x_n]=0\in\mathcal Q\).

#### Proof
Take scalar matrices
\[
x_n=\begin{cases}
0,&n\text{ even},\\
1,&n\text{ odd}.
\end{cases}
\]
Then \(x_{2j}=0\) for every \(j\), while
\[
\|[x_n]\|=\limsup_n|x_n|=1.
\]
So the corona class is nonzero. ∎

Therefore the sentence

> “pass to a subsequence on which the same \(\gamma_i\) is maximal; the corresponding lamp difference dies”

is literally valid only if the target uses that subsequence as the defining ultrafilter/quotient, or if one has some additional uniformity.  It is **not** by itself a proof that the element is killed by the original map to the standard norm matrix corona.

This is the main correction to the repository's `multi-mover-verification` memo, whose “the ultrafilter is the pigeonhole” sentence conflates the norm corona with a norm ultraproduct.  The non-MF application can nevertheless be repaired completely.

---

## 7. The finite-block amplification repair

The right non-MF statement is weaker than “every corona morphism kills one fixed candidate” but still exactly what is needed to rule out injective corona representations.

### Lemma 7.1 — simultaneous separation amplification

Let \(L\) be a countable group and
\[
\Theta:L\to\mathcal U(\mathcal Q_{\mathbf d})
\]
a homomorphism into a norm matrix corona.  Let
\[
B=\{b_1,\dots,b_m\}\subset L
\]
be finite and suppose
\[
\Theta(b_i)\ne1
\qquad(1\le i\le m).
\]
Then there exist dimensions \(e_k\) and a homomorphism
\[
\widetilde\Theta:L\to\mathcal U(\mathcal Q_{\mathbf e})
\]
with coordinate unitary lifts \(\widetilde U_{g,k}\) such that for every \(i\) there is \(\eta_i>0\) with
\[
\boxed{
\|\widetilde U_{b_i,k}-1\|_{\rm op}\ge\eta_i
\quad\text{for every sufficiently large }k.}
\]
In words: every member of the finite set is separated **at every stage**, not merely in limsup.

#### Proof
Choose coordinate unitary lifts \(U_{g,n}\) for every \(g\in L\).  Since \(\Theta\) is a homomorphism,
\[
\|U_{gh,n}-U_{g,n}U_{h,n}\|_{\rm op}\to0
\]
for each fixed pair \(g,h\).

Since \(\Theta(b_i)\ne1\), the corona norm formula gives
\[
c_i:=\limsup_n\|U_{b_i,n}-1\|_{\rm op}>0.
\]
Set \(\eta_i=c_i/2\).  Enumerate \(L=\{g_1,g_2,\dots\}\).  For each \(i\) and each \(k\), choose an integer \(n_i(k)\) so large that

1. \(\|U_{b_i,n_i(k)}-1\|\ge\eta_i\);
2. for every \(p,q\le k\),
   \[
   \|U_{g_pg_q,n_i(k)}-U_{g_p,n_i(k)}U_{g_q,n_i(k)}\|<1/k.
   \]

This is possible because the separation condition holds on an infinite set of indices, while all finitely many multiplication defects tend to zero on the whole tail.

Define
\[
e_k=\sum_{i=1}^m d_{n_i(k)}
\]
and
\[
\widetilde U_{g,k}
 =\bigoplus_{i=1}^m U_{g,n_i(k)}.
\]
For \(p,q\le k\),
\[
\|\widetilde U_{g_pg_q,k}
 -\widetilde U_{g_p,k}\widetilde U_{g_q,k}\|_{\rm op}
 =\max_i
 \|U_{g_pg_q,n_i(k)}-U_{g_p,n_i(k)}U_{g_q,n_i(k)}\|
 <1/k.
\]
Thus the block sequence defines a homomorphism \(\widetilde\Theta\) to the new corona.

For a fixed \(b_i\), the \(i\)-th diagonal block of
\(\widetilde U_{b_i,k}-1\) is
\(U_{b_i,n_i(k)}-1\), so
\[
\|\widetilde U_{b_i,k}-1\|_{\rm op}
\ge\|U_{b_i,n_i(k)}-1\|_{\rm op}
\ge\eta_i.
\]
This proves simultaneous stagewise separation. ∎

### Theorem 7.2 — corrected multi-mover removal of condition (iii)

Assume the analytic core of the circulated collapse theorem has the following property:

- for a finite-stage almost representation, once a normalization scale \(k_n\) has
  1. \(\delta_n(g)\le C_g k_n+o(k_n)\) for every fixed \(g\in\Gamma\), and
  2. one designated mover has displacement exactly \(k_n\),

  the property-(T)/rank/HS argument contradicts a uniform positive operator-norm separation of the corresponding lamp difference; and
- the zero-scale branch has the standard consequence used in the circulated proof: if \(k_n=0\) along arbitrarily late stages, then every corrected mover lamp difference is asymptotically the identity along those stages.

Assume all other hypotheses (the email's conditions (i) and (ii)) remain unchanged.

Let \(\Lambda\) denote the **full ambient group** to which the circulated collapse criterion is applied; in the permutational-wreath application this is the semidirect product containing both the lamp subgroup and the acting group.  Then the single-mover generation hypothesis
\[
\Gamma=\langle H,\gamma\rangle
\]
is unnecessary for the conclusion that \(\Lambda\) is **not MF**.

#### Proof
Choose finitely many moving generators \(\gamma_1,\dots,\gamma_m\) and put
\[
b_i=a_{\gamma_i x_0}a_{x_0}^{-1}
\]
(or \(a_{\gamma_i x_0}a_{x_0}\) in the involutive-lamp case).  Because
\(\gamma_i x_0\ne x_0\), each \(b_i\) is nontrivial in the direct-sum lamp group.

Suppose, toward a contradiction, that the ambient group \(\Lambda\) admits an injective homomorphism \(\Theta\) into a norm matrix corona.  Then
\[
\Theta(b_i)\ne1
\]
for every \(i\).  Apply Lemma 7.1 to obtain a new corona model in which every \(b_i\) is uniformly operator-norm separated from the identity at every sufficiently late stage.

In that amplified model define
\[
k_n=\max_i d_n(x_0,\gamma_i x_0).
\]
By Lemma 5.2, the required word estimate holds for every fixed \(g\in\Gamma\).  The scale is positive at every sufficiently late stage: otherwise the zero-scale branch would force all mover defects toward the identity along arbitrarily late stages, contradicting the simultaneous lower bounds supplied by Lemma 7.1.  We may therefore normalize by \(k_n\) from some point onward.

Choose an argmax index \(i(n)\).  Passing to an infinite subsequence, fix \(i_*\) with \(i(n)=i_*\) throughout the subsequence.  On this subsequence,
\[
d_n(x_0,\gamma_{i_*}x_0)=k_n,
\]
so the designated mover has normalized displacement exactly one.  Hence the unchanged analytic core forces
\[
\|\widetilde U_{b_{i_*},n}-1\|_{\rm op}\to0
\]
along that subsequence.

But Lemma 7.1 gives a uniform lower bound
\[
\|\widetilde U_{b_{i_*},n}-1\|_{\rm op}\ge\eta_{i_*}>0
\]
at **every** sufficiently late stage, hence on every subsequence.  Contradiction.

Therefore no injective corona representation of \(\Lambda\) exists; the ambient group is not MF. ∎

### What Theorem 7.2 does and does not say

It proves the statement needed for non-MF-ness:

\[
\boxed{\text{no injective matrix-corona representation exists}.}
\]

It does **not** prove that there is a single \(i\) such that every corona representation kills \(b_i\).  The bad index may vary from representation to representation, and in the standard \(c_0\)-corona it may even vary by coordinate in a way that prevents any one \(b_i\) from vanishing globally.

Thus:

- the historical max-mover replacement removes (iii) at the estimate layer, while the current compression theorem later removes the need for (iii) entirely in the ascending-HNN lamp application;
- **condition (iii) can still matter for MF-radical membership of a predetermined element**;
- a genuine norm-ultraproduct formulation does permit the finite-ultrafilter pigeonhole, but that is a different quotient from the ordinary norm matrix corona.

This sharpens the conclusion suggested in the email and corrects the subsequence issue.

---

## 8. Why the rank/HS part of the collapse argument works

The historical action-form proof is not separately identified in the archive, but the repository contains the same analytic architecture in its current compression-form proof.  Here is the mathematical core in abstract form; Sections 32--34 later give the stronger current proof in detail.

Suppose \(V_n(\gamma)\) are exact pairwise-commuting self-adjoint involutions indexed by \(\gamma\in\Gamma\), with asymptotic covariance under coordinate unitaries \(U_{g,n}\):
\[
\|U_{g,n}V_n(\gamma)U_{g,n}^*-V_n(g\gamma)\|_{\rm op}\to0.
\]
Define
\[
d_n(\gamma,\mu)
 =\operatorname{rank}(V_n(\gamma)-V_n(\mu)).
\]

### 8.1 \(d_n\) is a pseudometric

Symmetry and \(d_n(\gamma,\gamma)=0\) are immediate.  For the triangle inequality,
\[
V_n(\gamma)-V_n(\nu)
=(V_n(\gamma)-V_n(\mu))+(V_n(\mu)-V_n(\nu)),
\]
and
\[
\operatorname{rank}(A+B)
\le\operatorname{rank}A+\operatorname{rank}B.
\]
Hence
\[
d_n(\gamma,\nu)
\le d_n(\gamma,\mu)+d_n(\mu,\nu).
\]
It may be a pseudometric rather than a metric because two indices can yield the same corrected involution.

### 8.2 Covariance makes rank translation-invariant

Fix \(g,\gamma,\mu\).  Put
\[
p_n=\frac{(V_n(\gamma)-V_n(\mu))^2}{4},
\qquad
q_n=\frac{(V_n(g\gamma)-V_n(g\mu))^2}{4}.
\]
By Lemma 3.3 these are projections and
\[
\operatorname{rank}p_n=d_n(\gamma,\mu),
\qquad
\operatorname{rank}q_n=d_n(g\gamma,g\mu).
\]
Asymptotic covariance implies
\[
\|U_{g,n}p_nU_{g,n}^*-q_n\|_{\rm op}\to0.
\]
For large \(n\) this norm is below \(1\), so Lemma 3.2 gives
\[
\operatorname{rank}p_n=\operatorname{rank}q_n.
\]
Therefore
\[
\boxed{d_n(g\gamma,g\mu)=d_n(\gamma,\mu)}
\]
eventually for every fixed triple.

### 8.3 Rank normalization produces Hilbert energy

Let \(S\) be a finite symmetric generating set and set, for example,
\[
k_n=\sum_{s\in S}d_n(1,s)
\]
or, in the multi-mover version, use the relevant maximum scale.  Define the matrix-valued displacement
\[
b_n(\gamma)
 =k_n^{-1/2}\bigl(V_n(\gamma)-V_n(1)\bigr).
\]
Lemma 3.3 gives
\[
\|b_n(\gamma)\|_{\rm F}^{2}
 =\frac{4d_n(1,\gamma)}{k_n}.
\]
For the sum normalization,
\[
\sum_{s\in S}\|b_n(s)\|_{\rm F}^2=4.
\]
Thus one has a **nonvanishing normalized generator energy**.

On the other hand, covariance and the rank/operator estimate show that the cocycle defect is negligible.  Schematically,
\[
D_n(g,\gamma)
=b_n(g\gamma)-b_n(g)-\operatorname{Ad}(U_{g,n})b_n(\gamma)
\]
is a finite sum of terms whose operator norms tend to zero and whose ranks are \(O(k_n)\).  Hence Lemma 3.1 gives
\[
\|D_n(g,\gamma)\|_{\rm F}^2
\le O(k_n)\cdot o(1)^2/k_n=o(1).
\]
Thus \(b_n\) is an asymptotic affine 1-cocycle in Hilbert spaces.

Property (T), equivalently the fixed-point property for affine isometric Hilbert actions (Delorme--Guichardet), forbids a nontrivial limiting affine cocycle of this normalized sort: after taking the appropriate limiting Hilbert space, the affine action has a fixed point, so the cocycle is a coboundary.  The compression/fixed-subgroup geometry then transports the primitive and forces the generator displacements to have vanishing energy, contradicting the normalized mass equal to \(4\).

That is the conceptual reason the proof *must* enter Hilbert--Schmidt geometry after rank normalization.

---

## 9. Ascending HNN extensions: normal form and semidirect structure

Let \(\Gamma\) be a group and \(\alpha:\Gamma\to\Gamma\) an injective endomorphism.  Define
\[
G=\operatorname{HNN}(\Gamma,\alpha)
=\left\langle \Gamma,t\;\middle|\;
 t\gamma t^{-1}=\alpha(\gamma),\ \gamma\in\Gamma
\right\rangle.
\]
Assume \(\alpha(\Gamma)\ne\Gamma\) when discussing properness.

For every integer \(j\), put
\[
\Gamma_j=t^{-j}\Gamma t^j.
\]
Since
\[
t\Gamma t^{-1}=\alpha(\Gamma)\le\Gamma,
\]
we have
\[
\boxed{\Gamma_j\le\Gamma_{j+1}\quad(j\in\mathbb Z).}
\]

### Lemma 9.1 — ascending normal form

Every element of \(G\) can be written
\[
\boxed{g=t^{-p}\gamma t^q}
\]
with \(p,q\ge0\) and \(\gamma\in\Gamma\).

#### Proof
Use the relations
\[
t\gamma=\alpha(\gamma)t
\]
and, equivalently,
\[
\gamma t^{-1}=t^{-1}\alpha(\gamma).
\]
In any word in \(\Gamma\cup\{t,t^{-1}\}\), repeatedly move every positive \(t\) to the right across \(\Gamma\)-letters and every negative \(t^{-1}\) to the left.  Adjacent \(t t^{-1}\) or \(t^{-1}t\) cancel.  What remains has all negative powers on the left, one \(\Gamma\)-letter in the middle, and all positive powers on the right. ∎

Define the **height homomorphism**
\[
\chi:G\to\mathbb Z,
\qquad
\chi(\gamma)=0\ (\gamma\in\Gamma),
\qquad
\chi(t)=1.
\]
The defining relation has height zero on both sides, so \(\chi\) is well defined.

### Proposition 9.2 — the kernel is the telescope union

Let
\[
N=\bigcup_{k\ge0}\Gamma_k
 =\bigcup_{k\ge0}t^{-k}\Gamma t^k.
\]
Then
\[
\boxed{N=\ker\chi.}
\]
In particular \(N\triangleleft G\).

#### Proof
Every \(\Gamma_k\) has height zero, so \(N\subseteq\ker\chi\).
Conversely, write \(g=t^{-p}\gamma t^q\) by Lemma 9.1.  If \(\chi(g)=0\), then \(-p+q=0\), hence \(p=q\), and
\[
g=t^{-p}\gamma t^p\in\Gamma_p\subseteq N.
\]
Thus \(\ker\chi=N\).  Kernels are normal. ∎

### Proposition 9.3 — semidirect product decomposition

Conjugation by \(t\) defines an automorphism of \(N\), and
\[
\boxed{G=N\rtimes\langle t\rangle\cong N\rtimes\mathbb Z.}
\]

#### Proof
Since \(N=\ker\chi\), it is normal, so conjugation by \(t\) preserves it.  The group \(G\) is generated by \(\Gamma\subset N\) and \(t\), hence by \(N\) and \(t\).  Finally,
\[
N\cap\langle t\rangle=\{1\},
\]
because \(t^q\in N=\ker\chi\) implies \(q=\chi(t^q)=0\).  Therefore the product is semidirect. ∎

### Corollary 9.4 — the ascending HNN extension is not property (T)

If \(G\) is nontrivial as above, then \(G\) surjects onto \(\mathbb Z\), so \(G\) does not have property (T).

#### Proof
Property (T) passes to quotients: a unitary representation of a quotient pulls back to one of the original group, preserving almost-invariant and invariant vectors.

The group \(\mathbb Z\) does not have property (T).  Indeed, for \(m\ge1\) let
\[
\rho_m(k)=e^{ik/m}
\]
be a nontrivial one-dimensional unitary representation.  For any finite \(F\subset\mathbb Z\),
\[
\max_{k\in F}|\rho_m(k)-1|\to0,
\]
so the unit vector in \(\mathbb C\) is arbitrarily close to invariant on \(F\); but a nontrivial one-dimensional character has no nonzero invariant vector.  Hence \(\mathbb Z\) fails property (T), and so does any group surjecting onto it. ∎

This makes the contrast with the Kun--Thom property-(T) ambient examples completely genuine: the lean ascending-HNN skeleton is as far from property (T) as having an infinite cyclic quotient.

---

## 10. Explicit Følner sets for \(G\curvearrowright G/\Gamma\)

Monod--Popa Proposition 2 proves co-amenability of \(\Gamma\) in precisely this ascending-HNN situation.  Their proof uses invariant means.  Here is a concrete Følner proof.

Let
\[
X=G/\Gamma,
\qquad
x_k=t^{-k}\Gamma\quad(k\ge0).
\]
These points are distinct because their heights differ: if
\(t^{-k}\Gamma=t^{-\ell}\Gamma\), then
\(t^{\ell-k}\in\Gamma\subset\ker\chi\), hence \(k=\ell\).

### Lemma 10.1 — deep telescope elements fix the tail

If \(n\in\Gamma_M\), then \(n\) fixes \(x_k\) for every \(k\ge M\).

#### Proof
The stabilizer of \(x_k=t^{-k}\Gamma\) is
\[
\operatorname{Stab}_G(x_k)
=t^{-k}\Gamma t^k=\Gamma_k.
\]
Since the levels increase and \(M\le k\),
\[
\Gamma_M\le\Gamma_k.
\]
Thus \(n\in\operatorname{Stab}(x_k)\). ∎

### Lemma 10.2 — every group element is eventually a translation of the ray

Write \(g=n t^q\) with \(n\in N\), \(q\in\mathbb Z\).  There is \(M_g\) such that for every \(k\) with \(k-q\ge M_g\),
\[
\boxed{g x_k=x_{k-q}.}
\]

#### Proof
Choose \(M_g\) with \(n\in\Gamma_{M_g}\).  Then
\[
g x_k
=n t^q t^{-k}\Gamma
=n t^{-(k-q)}\Gamma
=n x_{k-q}.
\]
If \(k-q\ge M_g\), Lemma 10.1 says \(n\) fixes \(x_{k-q}\). ∎

### Theorem 10.3 — explicit Følner sequence

The action \(G\curvearrowright X\) is amenable.  More precisely, for every finite \(F\subset G\) and every \(\varepsilon>0\), there are integers \(R,L\) such that
\[
A_{R,L}=\{x_R,x_{R+1},\dots,x_{R+L-1}\}
\]
satisfies
\[
\frac{|gA_{R,L}\triangle A_{R,L}|}{|A_{R,L}|}<\varepsilon
\qquad(g\in F).
\]

#### Proof
Write
\[
g=n_g t^{q_g}
\]
for each \(g\in F\).  Choose \(M\) so that every \(n_g\in\Gamma_M\), and put
\[
Q=\max_{g\in F}|q_g|.
\]
Choose \(R\ge M+Q\).  Then for every \(k\in[R,R+L-1]\) and every \(g\in F\),
\[
k-q_g\ge R-Q\ge M,
\]
so Lemma 10.2 gives
\[
g x_k=x_{k-q_g}.
\]
Therefore \(gA_{R,L}\) is the interval of ray points shifted by \(-q_g\), and, when \(L>|q_g|\),
\[
|gA_{R,L}\triangle A_{R,L}|=2|q_g|\le2Q.
\]
Hence
\[
\frac{|gA_{R,L}\triangle A_{R,L}|}{L}
\le\frac{2Q}{L}.
\]
Choose \(L>2Q/\varepsilon\). ∎

Thus the co-amenability observed by Monod--Popa is particularly transparent here: asymptotically, the action on the far end of the ray forgets the entire telescope group \(N\) and sees only the \(\mathbb Z\)-height translation.

---

## 11. If \(\Gamma\) is sofic, then the ascending HNN group \(G\) is sofic

This can be proved without invoking a large extension theorem.

### Lemma 11.1 — directed unions of sofic groups are sofic

If
\[
H_0\le H_1\le H_2\le\cdots
\]
are sofic and \(H=\bigcup_jH_j\), then \(H\) is sofic.

#### Proof
Let \(F\subset H\) be finite and \(\varepsilon>0\).  Choose \(j\) with
\(F\cup F^2\subset H_j\).  Take a sofic \((F,\varepsilon)\)-approximation of \(H_j\).  Extend the approximating map arbitrarily to all of \(H\) (for example by the identity outside \(H_j\)).  Every multiplicativity and freeness condition tested on \(F\) is unchanged. ∎

Hence, if \(\Gamma\) is sofic, every \(\Gamma_j\cong\Gamma\) is sofic and
\[
N=\bigcup_{j\ge0}\Gamma_j
\]
is sofic.

### Lemma 11.2 — a sofic group extended by a cyclic automorphism is sofic

Let \(N\) be sofic, let \(\beta\in\operatorname{Aut}(N)\), and set
\[
G=N\rtimes_\beta\mathbb Z.
\]
Then \(G\) is sofic.

#### Proof
Let \(t\) denote the generator of the \(\mathbb Z\)-factor, so
\[
tnt^{-1}=\beta(n).
\]
Fix a finite symmetric \(F\subset G\), containing \(1\), and \(\varepsilon>0\).  Write
\[
g=n_g t^{q_g}\quad(g\in F\cup F^2)
\]
and choose
\[
Q=\max_{g\in F\cup F^2}|q_g|.
\]
Choose a large integer \(L\gg Q/\varepsilon\).  For each block index
\(j\in\{0,\dots,L-1\}\), the finite multiplication checks will involve only finitely many elements of the form
\[
\beta^{-j}(n_g),
\qquad
\beta^{-(j+q_g)}(n_h),
\qquad
\beta^{-j}(n_{gh}).
\]
Let \(M\subset N\) be the finite set of all such elements needed for
\(g,h\in F\) and all \(j\in\{0,\dots,L-1\}\).  Take a sufficiently accurate sofic map
\[
\psi:N\to\operatorname{Sym}(A_0)
\]
on \(M\).

Put
\[
A=(\mathbb Z/L\mathbb Z)\times A_0.
\]
Let
\[
T(j,a)=(j+1,a).
\]
For \(n\in N\), define a block-diagonal permutation
\[
P(n)(j,a)=\bigl(j,\psi(\beta^{-j}(n))a\bigr),
\]
where \(j\) is represented by \(0,\dots,L-1\).  Finally set
\[
\Phi(nt^q)=P(n)T^q.
\]

Consider \(g=n_gt^q\) and \(h=n_ht^r\) in \(F\).  Their product is
\[
gh=n_g\beta^q(n_h)t^{q+r}.
\]
On a block \(j\) for which the shifts by \(r\), \(q\), and \(q+r\) do not wrap around the cyclic boundary, the fiber part of
\(\Phi(g)\Phi(h)\) is
\[
\psi(\beta^{-(j+q+r)}n_g)
\psi(\beta^{-(j+r)}n_h),
\]
while the fiber part of \(\Phi(gh)\) is
\[
\psi\!\left(
\beta^{-(j+q+r)}(n_g\beta^q(n_h))
\right)
=
\psi\!\left(
\beta^{-(j+q+r)}n_g\;
\beta^{-(j+r)}n_h
\right).
\]
These are close by multiplicativity of \(\psi\).  Make the finite sofic test for \(\psi\) accurate enough that, on every required pair of elements of \(M\), the Hamming multiplicativity defect is at most \(\delta\).  A block can fail the displayed untwisted calculation only if either \(j+r\) or \(j+q+r\), represented as an ordinary integer, leaves \(\{0,\dots,L-1\}\).  The first event occurs for at most \(|r|\le Q\) values of \(j\), and the second for at most \(|q+r|\le Q\) values, because \(gh\in F^2\) was included when \(Q\) was chosen.  Thus at most \(2Q\) of the \(L\) blocks are boundary blocks.  On every other block the two fiber permutations disagree on at most a \(\delta\)-fraction of \(A_0\).  Averaging over blocks gives the explicit bound
\[
 d_{\mathrm{Hamm}}\bigl(\Phi(gh),\Phi(g)\Phi(h)\bigr)
 \le \frac{2Q}{L}+\delta.
\]
Choose \(L\) with \(2Q/L<\varepsilon/2\) and then \(\delta<\varepsilon/2\).  This proves the required multiplicativity estimate simultaneously for all \(g,h\in F\).

For freeness, take \(g=n_gt^q\in F\setminus\{1\}\).
If \(q\ne0\), choose \(L>2Q\).  Then \(|q|<L\), so the cyclic shift of the first coordinate has no fixed point; hence \(\Phi(g)\) has no fixed points.
If \(q=0\), then \(n_g\ne1\).  Include every
\(\beta^{-j}(n_g)\) in the finite sofic test set for \(\psi\).  Since automorphisms preserve nonidentity, each is nontrivial, so on every block the permutation
\(\psi(\beta^{-j}(n_g))\) moves a proportion arbitrarily close to one.  Averaging over blocks gives the required freeness.

Thus \(\Phi\) is a sofic approximation of \(G\). ∎

### Corollary 11.3
If \(\Gamma\) is sofic, then its ascending HNN extension along any injective endomorphism is sofic.

#### Proof
By Lemma 11.1, \(N\) is sofic.  Proposition 9.3 gives
\(G=N\rtimes\mathbb Z\), so Lemma 11.2 applies. ∎

This agrees with the general sofic-by-amenable extension theorem and with Brude--Sasyk's result that a group with a co-amenable sofic subgroup is sofic.

---

## 12. A permanence lemma for sofic actions under a cyclic extension

This is the key new technical input for the action question.

### Theorem 12.1 — cyclic extension of a sofic action

Let \(N\curvearrowright X\) be a sofic action.  Suppose \(t\) acts bijectively on \(X\), \(\beta\in\operatorname{Aut}(N)\), and the compatibility
\[
t(n x)=\beta(n)(t x)
\]
holds.  Equivalently, \(X\) carries an action of
\[
G=N\rtimes_\beta\mathbb Z.
\]
Then the full action
\[
\boxed{G\curvearrowright X\text{ is sofic}.}
\]

#### Proof
Fix finite \(F\subset G\), finite \(E\subset X\), and \(\varepsilon>0\).  Enlarge \(F\) so it is symmetric and contains \(1\), and write
\[
g=n_g t^{q_g}\qquad(g\in F\cup F^2).
\]
Let
\[
Q=\max_{g\in F\cup F^2}|q_g|.
\]
Choose \(L\) so large that
\[
\frac{10Q}{L}<\varepsilon/3.
\]

We will use a finite approximation of the \(N\)-action simultaneously at every stack height.  Define
\[
E'=
\{t^{-j}x:\ x\in E,\ -Q\le j\le L+Q\}.
\]
This is finite.  Let \(M\subset N\) be the finite set containing every element
\[
\beta^{-j}(n_g)
\]
that appears in either a multiplication check or an orbit-chart check for
\(g\in F\cup F^2\) and the finitely many relevant integers \(j\).

By soficity of \(N\curvearrowright X\), choose a finite set \(A_0\), a unital map
\[
\psi:N\to\operatorname{Sym}(A_0)
\]
which is as multiplicative as needed on \(M\), a subset
\[
S_0\subset A_0,
\qquad
|S_0|>(1-\delta)|A_0|,
\]
and, for each \(a\in S_0\), an injective chart
\[
\rho_a:E'\hookrightarrow B
\]
satisfying the \(N\)-orbit covariance for the finite test, where \(\delta>0\) is chosen much smaller than \(\varepsilon\).

Set
\[
A=(\mathbb Z/L\mathbb Z)\times A_0.
\]
As in Lemma 11.2, define
\[
T(j,a)=(j+1,a),
\]
\[
P(n)(j,a)=\bigl(j,\psi(\beta^{-j}(n))a\bigr),
\]
and
\[
\Phi(nt^q)=P(n)T^q.
\]
The calculation from Lemma 11.2 is quantitative: if the finite \(N\)-model \(\psi\) has multiplication defect at most \(\delta\) on the finite set \(M\), then for every \(g,h\in F\)
\[
 d_{\mathrm{Hamm}}\bigl(\Phi(gh),\Phi(g)\Phi(h)\bigr)
 \le \frac{2Q}{L}+\delta.
\]
Choose \(L\) and \(\delta\) so that this is below \(\varepsilon\) (the stronger choice \(10Q/L<\varepsilon/3\) already made above leaves ample room).  Hence \(\Phi\) is \((F,\varepsilon)\)-multiplicative.

Now let
\[
J_{\rm good}=\{Q,Q+1,\dots,L-1-Q\}
\]
and
\[
S=J_{\rm good}\times S_0.
\]
For large \(L\) and small \(\delta\),
\[
|S|>(1-\varepsilon)|A|.
\]
For \((j,a)\in S\), define
\[
\boxed{
\pi_{(j,a)}(x)=\rho_a(t^{-j}x),
\qquad x\in E.}
\]
Because \(\rho_a\) is injective, each \(\pi_{(j,a)}\) is injective.

It remains to verify the orbit covariance.  Let
\[
g=n t^q\in F,
\qquad
s=(j,a)\in S,
\]
and assume \(\Phi(g)s\in S\) and \(g^{-1}x\in E\).  The good-block condition prevents cyclic wrap, so if
\[
k=j+q,
\]
then
\[
\Phi(g)(j,a)
 =\left(k,\psi(\beta^{-k}(n))a\right).
\]
Therefore
\[
\pi_{\Phi(g)s}(x)
=
\rho_{\psi(\beta^{-k}(n))a}(t^{-k}x).
\]
By the \(N\)-orbit covariance of \(\rho\), this equals
\[
\rho_a\left((\beta^{-k}(n))^{-1}t^{-k}x\right).
\]
Since
\[
\beta^{-k}(n)=t^{-k}nt^k,
\]
we have
\[
(\beta^{-k}(n))^{-1}t^{-k}
=t^{-k}n^{-1}.
\]
Hence
\[
\pi_{\Phi(g)s}(x)
=
\rho_a(t^{-k}n^{-1}x).
\]
Because \(k=j+q\),
\[
t^{-k}n^{-1}
=t^{-j}t^{-q}n^{-1}
=t^{-j}g^{-1}.
\]
Thus
\[
\pi_{\Phi(g)s}(x)
=
\rho_a(t^{-j}g^{-1}x)
=\pi_s(g^{-1}x).
\]
This is exactly the GKEP orbit-approximation identity.  Therefore
\(G\curvearrowright X\) is sofic. ∎

This lemma is useful beyond the present HNN problem: it says that soficity of an action is stable under adjoining a compatible cyclic normalizer.

---

## 13. Finite-index ascending HNN coset actions are sofic

We now prove the promised new finish line.

Assume
\[
D=[\Gamma:\alpha(\Gamma)]<\infty.
\]
Recall
\[
\Gamma_j=t^{-j}\Gamma t^j
\qquad(j\in\mathbb Z).
\]

### Lemma 13.1 — consecutive levels have finite index \(D\)

For every \(j\in\mathbb Z\),
\[
\Gamma_j\le\Gamma_{j+1}
\]
and
\[
\boxed{[\Gamma_{j+1}:\Gamma_j]=D.}
\]
Hence for \(i\le j\),
\[
[\Gamma_j:\Gamma_i]=D^{j-i}.
\]

#### Proof
The inclusion was already noted.  Conjugating the pair
\(\alpha(\Gamma)\le\Gamma\) by \(t^{-j-1}\) identifies it with
\(\Gamma_j\le\Gamma_{j+1}\).  Conjugation is an isomorphism and preserves subgroup index, giving the stated value.  Multiplicativity of finite index along a chain yields the last formula. ∎

### Lemma 13.2 — every \(\Gamma_k\)-orbit in \(G/\Gamma\) is finite

Fix \(k\ge0\).  For every \(x\in G/\Gamma\),
\[
|\Gamma_k x|<\infty.
\]

#### Proof
Write
\[
x=g\Gamma,
\qquad
g=n t^q,
\]
with \(n\in N\), \(q\in\mathbb Z\).  The stabilizer of \(x\) in \(\Gamma_k\) is
\[
\operatorname{Stab}_{\Gamma_k}(x)
=\Gamma_k\cap g\Gamma g^{-1}.
\]
Now
\[
g\Gamma g^{-1}
=n t^q\Gamma t^{-q}n^{-1}
=n\Gamma_{-q}n^{-1}.
\]
Choose an integer \(R\) so large that
\[
k\le R,
\qquad
-q\le R,
\qquad
n\in\Gamma_R.
\]
By Lemma 13.1, both \(\Gamma_k\) and \(\Gamma_{-q}\) are finite-index subgroups of \(\Gamma_R\).  Since \(n\in\Gamma_R\), conjugation by \(n\) is an automorphism of \(\Gamma_R\), so
\[
n\Gamma_{-q}n^{-1}
\]
is also finite-index in \(\Gamma_R\).  The intersection of two finite-index subgroups of a group is finite-index in each of them.  Therefore
\[
\Gamma_k\cap n\Gamma_{-q}n^{-1}
\]
has finite index in \(\Gamma_k\).

By orbit-stabilizer,
\[
|\Gamma_kx|
=[\Gamma_k:\operatorname{Stab}_{\Gamma_k}(x)]<\infty.
\]
∎

### Lemma 13.3 — every finite-orbit action is sofic, with exact models

Let \(H\curvearrowright Y\) be an action such that every orbit is finite.  Then the action is sofic.  In fact every finite test admits a model with zero multiplicativity error and no bad model points.

#### Proof
Fix finite \(E\subset Y\).  Let
\[
Y_0=\bigcup_{x\in E}Hx.
\]
This is a finite \(H\)-invariant set.  Let
\[
\rho:H\to Q\le\operatorname{Sym}(Y_0)
\]
be the finite image of the action on \(Y_0\).  Take the finite model set
\[
A=Q
\]
with \(H\) acting through \(\rho\) by left multiplication:
\[
\varphi(h)(s)=\rho(h)s.
\]
This is an exact homomorphism.

Take \(B=Y_0\) and \(S=A\).  For \(s\in Q\), define
\[
\pi_s:E\to Y_0,
\qquad
\pi_s(x)=s^{-1}x.
\]
Since \(s\) is a permutation of \(Y_0\), \(\pi_s\) is injective.  Moreover,
\[
\pi_{\varphi(h)s}(x)
=(\rho(h)s)^{-1}x
=s^{-1}\rho(h)^{-1}x
=\pi_s(h^{-1}x).
\]
Thus the orbit approximation is exact. ∎

### Lemma 13.4 — increasing unions preserve soficity of a fixed action

Suppose
\[
H_0\le H_1\le\cdots,
\qquad
H=\bigcup_jH_j,
\]
and every restricted action \(H_j\curvearrowright X\) is sofic.  Then
\[
H\curvearrowright X
\]
is sofic.

#### Proof
Given finite \(F\subset H\), choose \(j\) with \(F\cup F^2\subset H_j\).  Take a sofic \((F,E,\varepsilon)\)-orbit approximation for \(H_j\curvearrowright X\), and extend its permutation map arbitrarily from \(H_j\) to \(H\).  All conditions tested on \(F\) are unchanged. ∎

### Theorem 13.5 — finite-index HNN coset action theorem

Let \(\alpha:\Gamma\to\Gamma\) be injective with finite-index image and let
\[
G=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma)\rangle.
\]
Then
\[
\boxed{G\curvearrowright G/\Gamma\text{ is a sofic action}.}
\]

#### Proof
Let
\[
N=\bigcup_{k\ge0}\Gamma_k.
\]
By Lemma 13.2, for every \(k\), every orbit of the restricted action
\[
\Gamma_k\curvearrowright G/\Gamma
\]
is finite.  Lemma 13.3 says each restricted action is sofic.  Lemma 13.4 then gives
\[
N\curvearrowright G/\Gamma
\]
sofic.

By Proposition 9.3,
\[
G=N\rtimes\langle t\rangle.
\]
The given \(G\)-action supplies exactly the compatibility hypothesis in Theorem 12.1.  Therefore the full action
\[
G\curvearrowright G/\Gamma
\]
is sofic. ∎

### Why this is stronger than the original guess

The theorem assumes **no soficity or residual finiteness of \(\Gamma\)**.  Finite index alone makes every finite telescope-level orbit finite, and action-soficity does not require the acting group itself to have a free sofic approximation.

For the wreath-product application, however, GKEP Theorem 3.6 also requires the **acting group \(G\)** to be sofic.  By Corollary 11.3, that follows if \(\Gamma\) is sofic.

---

## 14. Consequence: a clean sofic-wreath criterion for finite-index self-embeddings

### Theorem 14.1
Let \(\alpha:\Gamma\to\Gamma\) be injective with finite-index image.  Let
\[
G=\operatorname{HNN}(\Gamma,\alpha),
\qquad
X=G/\Gamma.
\]
If \(\Gamma\) is sofic and \(K\) is a sofic group, then
\[
\boxed{K\wr_XG=K^{(X)}\rtimes G\text{ is sofic}.}
\]

#### Proof
Since \(\Gamma\) is sofic, Corollary 11.3 gives that \(G\) is sofic.  Theorem 13.5 gives that \(G\curvearrowright X\) is a sofic action.  Apply GKEP Theorem 3.6. ∎

For \(K=\mathbb Z/2\mathbb Z\), this is exactly the finite-order-lamp setup contemplated in the email.

### Corollary 14.2 — the non-MF + sofic route

Suppose, in addition, that the action-form collapse criterion's remaining hypotheses (i) and (ii) hold and the analytic-core usage audit required by Theorem 7.2 is satisfied.  Then
\[
(\mathbb Z/2\mathbb Z)^{(G/\Gamma)}\rtimes G
\]
is both sofic and non-MF.

#### Proof
Soficity is Theorem 14.1.  Non-MF-ness is Theorem 7.2 applied to the collapse criterion. ∎

Thus the email's desired route works rigorously under the extra finite-index hypothesis on the self-embedding.

---

## 15. A second sufficient condition: LERF base groups

The finite-index condition is not the only way to close the action question.

Gao proved in arXiv:2402.17150:

> **Gao's theorem.** Every action of a LERF group on a set is sofic.

This yields a useful corollary for arbitrary injective self-embeddings.

### Corollary 15.1
Let \(\Gamma\) be LERF and let \(\alpha:\Gamma\to\Gamma\) be any injective endomorphism.  Then for the ascending HNN extension
\[
G=\operatorname{HNN}(\Gamma,\alpha),
\]
the action
\[
G\curvearrowright G/\Gamma
\]
is sofic.

#### Proof
Every telescope level \(\Gamma_k\) is isomorphic to \(\Gamma\), hence LERF.  By Gao's theorem, **every** action of \(\Gamma_k\) is sofic, in particular its restriction to \(G/\Gamma\).  Lemma 13.4 gives that the increasing-union action
\[
N=\bigcup_k\Gamma_k\curvearrowright G/\Gamma
\]
is sofic.  Theorem 12.1 then adjoins the stable-letter \(\mathbb Z\)-direction. ∎

This is stronger than requiring finite-index image, but LERF is much stronger than residual finiteness.

### What remains open from the original guess

The following implication is **not proved here**:

\[
\boxed{
\Gamma\text{ merely sofic/residually finite}
\quad\Longrightarrow\quad
G\curvearrowright G/\Gamma\text{ sofic}
}
\]
for an arbitrary proper infinite-index self-embedding \(\alpha\).

Co-amenability of \(\Gamma\) in \(G\) proves that **the group \(G\)** is sofic when \(\Gamma\) is sofic (Brude--Sasyk, or Section 11), but group-soficity plus co-amenability of a stabilizer does not automatically provide the orbit charts required in Definition 2.1.  The 2025 version of GKEP still treats general sofic actions as a nontrivial issue, and Gao's LERF theorem gives one strong positive class rather than “residually finite” in full generality.

So the clean current landscape is:

\[
\begin{array}{c|c}
\text{hypothesis on }\alpha,\Gamma& G\curvearrowright G/\Gamma\\ \hline
[\Gamma:\alpha\Gamma]<\infty & \text{sofic (Theorem 13.5)}\\
\Gamma\text{ LERF} & \text{sofic (Corollary 15.1)}\\
\Gamma\text{ merely sofic/RF, arbitrary }\alpha & \text{not settled by these arguments}
\end{array}
\]

---

## 16. Non-co-Hopfian property-(T) groups and what they buy

A group is **co-Hopfian** if every injective endomorphism is surjective.  Hence a non-co-Hopfian group admits a proper injective endomorphism
\[
\alpha:\Gamma\hookrightarrow\Gamma.
\]

If \(\Gamma\) has property (T), then the ascending HNN extension gives a canonical one-sided compressor:
\[
t\Gamma t^{-1}=\alpha(\Gamma)<\Gamma.
\]
This is exactly the geometry used by the repository's compression-form collapse theorem.

Therefore the mathematical slogan in the email is essentially correct for the **non-MF construction**:

> a property-(T) non-co-Hopfian group supplies the compression geometry needed to build a non-MF witness.

There are two qualifications.

1. To derive the specific action-form lamp theorem by removing (iii), the unavailable conditions (i) and (ii) still have to be checked for the constructed action.
2. To derive a **sofic and non-MF** generalized wreath product from the action-sofic route, one needs enough approximation structure in addition to non-co-Hopfianity.  A clean sufficient package is
   \[
   \Gamma\text{ property (T) and sofic},
   \qquad
   \alpha\text{ proper injective with finite-index image}.
   \]

The finite-index condition is not needed for non-MF-ness; it is the simple extra hypothesis that closes the action-soficity argument.

---

## 17. The literal affine family in the uploaded repository

The repository's concrete base uses an injective “doubling” endomorphism.  At a conceptual level it is the affine map
\[
\alpha(v,A)=(2v,A)
\]
on an integral affine group of the form
\[
\mathbb Z^3\rtimes \mathrm{SL}_3(\mathbb Z)
\]
(or the explicitly presented/matrix-realized copy used in the formal development).

Three elementary facts explain why this is an ideal example.

### 17.1 Injective and proper

If
\[
\alpha(v,A)=\alpha(w,B),
\]
then \(A=B\) and \(2v=2w\), hence \(v=w\).  Thus \(\alpha\) is injective.

Its image has translation part \(2\mathbb Z^3\), so a unit translation is not in the image.  Thus \(\alpha\) is not surjective.

The repository proves the corresponding facts as
`conjD_injective` and `v1G_not_mem_range`.

### 17.2 Finite-index image

The quotient of the translation lattice by its doubled copy is
\[
\mathbb Z^3/2\mathbb Z^3\cong(\mathbb Z/2)^3,
\]
so the evident affine model has index \(2^3=8\).  The formal repository proves the required finite-index statement as
`conjD_range_finiteIndex` in `LiteralBaseDoublingIndex.lean`.

Therefore Theorem 13.5 applies to the associated ascending-HNN coset action.

### 17.3 Residual finiteness/soficity

Integral matrix groups are residually finite by congruence reduction: if an integral matrix \(g\ne1\), some entry of \(g-I\) is a nonzero integer; choose a prime \(p\) not dividing that entry.  Reduction modulo \(p\) maps the group to a finite matrix group and keeps \(g\) nontrivial.  Hence the base is residually finite, therefore sofic.

The repository has a formal sofic theorem `gammaBar_isSofic` for its concrete base.

### 17.4 Property (T)

Property (T) for the concrete affine base is a genuinely nontrivial Kazhdan theorem/certificate, not an elementary consequence of the preceding three items.  The uploaded Lean development carries this as a proved theorem
`gammaBar_hasKazhdanPropertyT`, obtained from the repository's presented-base property-(T) certificate via a surjective affine quotient.

### 17.5 The resulting chain

For the literal finite-index affine self-embedding:

\[
\boxed{
\begin{aligned}
&\Gamma\text{ is Kazhdan and sofic},\\
&\alpha:\Gamma\hookrightarrow\Gamma\text{ is proper and finite-index},\\
&G=\operatorname{HNN}(\Gamma,\alpha)\text{ is sofic and surjects onto }\mathbb Z,\\
&G\curvearrowright G/\Gamma\text{ is amenable and sofic},\\
&(\mathbb Z/2)^{(G/\Gamma)}\rtimes G\text{ is sofic}.
\end{aligned}}
\]

The repository independently proves the corresponding **sign-free mod-two lamp quotient is not MF**, and then proves it is sofic.  Its literal endpoint is therefore already encoded in Lean as an explicit sofic non-MF group of the intended generalized-wreath form; as noted above, no hosted CI status was returned for the audited commit.

What the theorem in Section 13 adds is a short conceptual reason that the **coset action itself** is sofic in this finite-index setting, which is exactly the question raised in the email.

---

## 18. Relation to Monod--Popa and Brude--Sasyk

Monod--Popa prove co-amenability for an ascending HNN subgroup by setting
\[
N=\bigcup_{k\ge0}t^{-k}\Gamma t^k,
\qquad
G=N\rtimes\mathbb Z,
\]
and using the fact that evaluation at deeper cosets becomes invariant under larger and larger pieces of \(N\), followed by amenability of \(G/N\cong\mathbb Z\).

The explicit intervals \(A_{R,L}\) from Theorem 10.3 are a concrete Følner realization of the same phenomenon.

Brude--Sasyk prove a general metric approximation theorem for co-amenable subgroups.  In the sofic case it says, in particular:

\[
H\le G,\quad H\text{ sofic and co-amenable in }G
\quad\Longrightarrow\quad
G\text{ sofic}.
\]

This settles **group-level** soficity of the ascending HNN extension once \(\Gamma\) is sofic.  It does not by itself produce the GKEP orbit charts for the specific set \(G/\Gamma\); that is why Section 13 is a distinct argument rather than a restatement of co-amenability.

---

## 19. Relation to Kun--Thom

Kun--Thom's August 2026 paper proves nonsoficity of certain generalized wreath products from Kazhdan/infranormal pairs in which both the subgroup and the ambient group have property (T).  Their abstract states that the explicit pairs can be chosen residually finite and Kazhdan.

The ascending-HNN mechanism here is structurally different:

- the **Kazhdan group is the base \(\Gamma\)**;
- the ambient HNN group \(G\) has a quotient \(\mathbb Z\), so it cannot have property (T);
- the one-sided self-embedding is visible directly through the stable letter;
- co-amenability of \(\Gamma\) in \(G\) is automatic;
- finite-index self-embedding gives a particularly simple proof of action soficity.

So the email is right that the ascending-HNN version is a very natural prototype of the non-MF mechanism even though it lies outside the “ambient group is also property (T)” geometry of the Kun--Thom nonsofic examples.

---

## 20. Proof-status ledger

To prevent “proof by atmosphere,” here is the exact status of every major assertion.

| Statement | Status in this note |
|---|---|
| operator/rank/HS inequalities | **fully proved** |
| commuting-involution rank identity | **fully proved** |
| property (T) \(\Rightarrow\) finite generation | **fully proved** |
| finitely many moving generators | **fully proved** |
| max-displacement word estimate | **fully proved** |
| fixed argmax on a subsequence | **fully proved** |
| “subsequence collapse means death in a norm corona” | **false; counterexample proved** |
| finite block-amplification repair | **fully proved** |
| historical max-mover removal of (iii) | **proved at the estimate layer, with the norm-corona block-amplification repair; historical theorem notation remains email-dependent** |
| removal of (iii) for a fixed MF-radical element | **not proved; generally stronger** |
| ascending HNN normal form | **fully proved** |
| \(N=\cup t^{-k}\Gamma t^k\), \(G=N\rtimes\mathbb Z\) | **fully proved** |
| \(G\) not property (T) | **fully proved** |
| explicit Følner sets for \(G/\Gamma\) | **fully proved** |
| \(\Gamma\) sofic \(\Rightarrow G\) sofic | **fully proved by cyclic-stack construction** |
| cyclic extension permanence for sofic actions | **fully proved** |
| finite-index \(\alpha\Rightarrow G\curvearrowright G/\Gamma\) sofic | **fully proved; new derived theorem** |
| \(\Gamma\) LERF \(\Rightarrow\) HNN coset action sofic | **proved using Gao's published LERF theorem** |
| arbitrary sofic/RF \(\Gamma\), arbitrary infinite-index \(\alpha\) \(\Rightarrow\) action sofic | **not established here** |
| sofic groups + sofic action \(\Rightarrow\) generalized wreath product sofic | **proved self-contained in Section 29 from the GKEP construction** |
| literal mod-two sign-free quotient sofic and non-MF | **present as proved Lean endpoint in audited repository** |
| concrete affine base has property (T) | **deep input, formal theorem present in repository** |

---

## 21. A clean theorem package for an eventual paper

The preceding arguments can be compressed into the following paper-level sequence.

### Theorem A — multi-mover estimate
Let \(\Gamma\curvearrowright X\) have property (T), let \(x_0\in X\), and suppose a collapse proof is normalized by displacement and uses a generating hypothesis only to establish
\(\delta_n(g)\le C_gk_n\).  Then one may replace a distinguished mover by finitely many movers and set
\[
k_n=\max_i d_n(x_0,\gamma_i x_0).
\]
The word estimate and top-scale normalization survive.

### Theorem B — norm-corona finite-family obstruction
If the resulting single-top-mover analytic argument contradicts uniform survival of its corresponding witness, then a fixed finite family of possible witnesses is enough to rule out injective norm-corona representations.  Proof: simultaneous block amplification followed by an argmax subsequence.

### Theorem C — ascending-HNN co-amenability
For every injective endomorphism \(\alpha:\Gamma\to\Gamma\), the ascending HNN extension satisfies
\[
G=N\rtimes\mathbb Z,
\qquad
N=\bigcup_{k\ge0}t^{-k}\Gamma t^k,
\]
and \(G\curvearrowright G/\Gamma\) admits explicit interval Følner sets.

### Theorem D — finite-index HNN action soficity
If \([\Gamma:\alpha\Gamma]<\infty\), then \(G\curvearrowright G/\Gamma\) is sofic.

### Theorem E — sofic generalized wreath consequence
If, in Theorem D, \(\Gamma\) is sofic and \(K\) is sofic, then
\[
K^{(G/\Gamma)}\rtimes G
\]
is sofic.

### Corollary F — sofic non-MF route
If the collapse hypotheses also hold for finite-order lamps, the same generalized wreath product is sofic and non-MF.

This is, in my view, the most economical “finish line” extracted from the email.

---

## 22. Further deductions

### 22.1 Finite index is exactly a commensurability mechanism

The proof of Theorem 13.5 does not use arithmetic features of doubling.  It uses only that the telescope levels are pairwise commensurable.  Therefore the theorem extends verbatim to any ascending HNN setup in which every pair of levels
\[
t^{-i}\Gamma t^i,
\qquad
t^{-j}\Gamma t^j
\]
is commensurable with finite index in a common level.  Finite-index image is the simplest sufficient condition.

### 22.2 The action can be sofic even when the group proof uses a different mechanism

Action soficity and group soficity are logically different.  In Theorem 13.5 the restricted telescope-level actions are sofic because their orbits are finite, not because the level groups admit free finite models.  This is why the action theorem itself needs no soficity assumption on \(\Gamma\).

### 22.3 Co-amenability and action-soficity solve different approximation problems

Co-amenability supplies Følner sets in the **orbit space**.  A GKEP sofic action requires, at most model points, injective finite charts that intertwine finite pieces of the action.  These are different data.  The finite-index argument succeeds because commensurability makes each telescope-level orbit finite, furnishing exact charts before the \(\mathbb Z\)-direction is added.

### 22.4 The multi-mover argument naturally yields a “finite MF blocking set”

Even when no specific \(b_i\) lies in the MF radical, the finite set
\[
B=\{b_1,\dots,b_m\}
\]
acts as a **blocking family**: there is no injective corona representation on which the whole family survives after simultaneous separation.  This finite-family notion is worth recording separately from the pointwise MF radical.

### 22.5 A symmetry can recover pointwise radical membership

Suppose a group of automorphisms of the entire construction permutes
\(b_1,\dots,b_m\) transitively and preserves the class of corona representations.  If one can prove that every representation kills at least one candidate *in the actual target quotient being used*, precomposing by those symmetries can sometimes promote the finite-family obstruction to pointwise radical information.  This requires genuine symmetry; it is not a consequence of the maximum argument alone.

---

## 23. Wolfram computational cross-check

Wolfram was used only as a sanity check, not as a substitute for proof.  For the concrete commuting involutions
\[
U=\operatorname{diag}(1,-1,1,-1,1,-1),
\]
\[
W=\operatorname{diag}(1,1,-1,-1,-1,1),
\]
Wolfram evaluated \(T=U-W\) and returned

- \(T^3=4T\): `True`;
- \(\operatorname{rank}T=4\);
- \(\operatorname{Tr}(T^*T)=16\);
- \(4\operatorname{rank}T=16\);
- normalized HS square \(=16/6=8/3\);
- \(4\operatorname{rank}T/6=8/3\).

This exactly matches Lemma 3.3.  The general proof is the algebraic calculation given there.

---

## 24. GitHub/formalization cross-check

At the current audited `main` head `7df16bbaa925c55a95b39996e9938b3b91311ac1`, the following formal declarations are particularly relevant.

1. **Finite-index compressed range**
   
   `GroupApproximation/Sofic/LiteralBaseDoublingIndex.lean`:
   
   ```lean
   instance conjD_range_finiteIndex : (conjD).range.FiniteIndex := by
     ...
   ```

2. **Mod-two lamp group**
   
   `GroupApproximation/Sofic/CommutingLampQuotientSofic.lean`:
   
   ```lean
   abbrev ModTwoLamp (X : Type w) : Type w :=
     Multiplicative (X →₀ ZMod 2)
   ```

3. **Property (T) for the concrete affine base**
   
   `GroupApproximation/Sofic/CommutingLampCollapse.lean`:
   
   ```lean
   theorem gammaBar_hasKazhdanPropertyT :
       HasKazhdanPropertyT gammaBar := ...
   ```

4. **Literal non-MF endpoint**
   
   The same file proves
   
   ```lean
   theorem literalCommutingLampQuotient_not_isCDEOperatorMF :
       ¬ IsCDEOperatorMF (...) := ...
   ```

5. **Literal sofic + non-MF endpoint**
   
   `GroupApproximation/Sofic/CommutingLampQuotientSofic.lean` proves
   
   ```lean
   theorem literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF :
       IsSofic (...) ∧ ¬ IsCDEOperatorMF (...) := ...
   ```

Thus the uploaded project has already crossed the concrete “sofic and non-MF generalized mod-two lamp group” finish line.  The finite-index action theorem in this note explains why the associated coset action itself should also be regarded as sofic, rather than bypassing that question through a bespoke telescope-window group proof.

---

## 25. Final answer to the questions in the email

### “Why are there three distances?”

Because they encode three logically distinct resources:

\[
\boxed{
\begin{array}{rcl}
\text{operator norm}&=&\text{uniform algebraic/spectral control},\\
\text{rank}&=&\text{discrete size of the moving spectral support},\\
\text{Hilbert--Schmidt}&=&\text{quadratic Hilbert energy seen by property (T)}.
\end{array}}
\]

The exact commuting-involution identity and the rank/operator-to-HS inequality are the bridges.

### “Can condition (iii) be dropped?”

**For the historical max-mover proof: yes at the estimate layer, with the norm-corona block repair of Sections 6--7.  For the ascending-HNN involutive-lamp application, the answer is now stronger and unconditional:** the current involutive-compression theorem (Sections 32--34) kills every fixed two-lamp commutator along the Kazhdan orbit, so no distinguished mover hypothesis is needed at all.

But one must distinguish targets:

- in a norm ultraproduct, the finite ultrafilter pigeonhole picks one mover on an ultrafilter-large set;
- in the standard norm matrix corona, a subsequence does not make an element vanish globally.  The correct repair is the finite block-amplification argument of Lemma 7.1 and Theorem 7.2.

The conclusion is non-MF-ness, not automatic pointwise MF-radical membership of one specified two-lamp element.

### “Does a property-(T), non-co-Hopfian group suffice?”

For the **compression/non-MF mechanism**, that is essentially the right minimal structural input: a proper injective endomorphism gives the one-sided ascending-HNN compression.

For the **sofic + non-MF generalized wreath** route, one needs additional approximation input.  A particularly clean package is:

\[
\Gamma\text{ property (T) and sofic},
\quad
\alpha:\Gamma\hookrightarrow\Gamma\text{ proper with finite-index image}.
\]

### “Is the ascending-HNN action on \(G/\Gamma\) amenable?”

Yes, with explicit interval Følner sets; Theorem 10.3 proves it directly.

### “Is that action sofic when \(\Gamma\) is sofic/residually finite?”

- **Yes if the self-embedding has finite-index image** — Theorem 13.5 proves more: no soficity hypothesis on \(\Gamma\) is needed at the action level.
- **Yes if \(\Gamma\) is LERF**, for arbitrary injective self-embedding, by Gao's theorem plus the cyclic-extension lemma.
- **Mere residual finiteness/soficity with an arbitrary infinite-index self-embedding is not resolved by the arguments in this dossier.**

### “Does this produce a sofic wreath product?”

Under the finite-index + sofic-base hypotheses, yes: \(G\) is sofic, the action is sofic, and GKEP Theorem 3.6 gives soficity of the generalized wreath product.  In the literal uploaded project, the corresponding mod-two lamp quotient is moreover formally proved non-MF, yielding the desired sofic non-MF endpoint at the level of the repository's Lean theorem declarations.

---

## 26. References

1. N. Monod, S. Popa, *On co-amenability for groups and von Neumann algebras*, arXiv:math/0301348.  
   <https://arxiv.org/abs/math/0301348>

2. D. Gao, S. Kunnawalkam Elayavalli, G. Patchell, *Soficity for group actions on sets and applications*, arXiv:2401.04945.  
   <https://arxiv.org/abs/2401.04945>

3. D. Gao, *All actions of LERF groups on sets are sofic*, arXiv:2402.17150.  
   <https://arxiv.org/abs/2402.17150>

4. J. Brude, R. Sasyk, *Metric approximations of unrestricted wreath products when the acting group is amenable*, arXiv:2004.05735; Comm. Algebra 50 (2022), no. 3, 949--961.  
   <https://arxiv.org/abs/2004.05735>

5. G. Kun, A. Thom, *Nonsofic wreath products of residually finite groups*, arXiv:2608.06222.  
   <https://arxiv.org/abs/2608.06222>

6. Repository snapshot: `SauersML/group-approximation`, current audited `main` head `7df16bbaa925c55a95b39996e9938b3b91311ac1` (2026-08-15 23:16:50 UTC).  
   <https://github.com/SauersML/group-approximation/tree/7df16bbaa925c55a95b39996e9938b3b91311ac1>

7. Repository multi-mover claim:  
   <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/research/multi-mover-collapse-criterion.md>

8. Repository current action-soficity card:  
   <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/research/ascending-hnn-coset-action-sofic.md>

9. Formal mod-two/sofic endpoint:  
   <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/CommutingLampQuotientSofic.lean>

10. Formal non-MF endpoint:  
    <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/CommutingLampCollapse.lean>

11. Formal finite-index doubling result:  
    <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/LiteralBaseDoublingIndex.lean>

12. End-to-end involutive collapse endpoint:  
    <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/InvolutionCollapseEndpoint.lean>

13. Projection collapse endpoint:  
    <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/ProjectionCompressionCollapse.lean>

14. Finite-order Fourier/torsion collapse endpoint:  
    <https://github.com/SauersML/group-approximation/blob/7df16bbaa925c55a95b39996e9938b3b91311ac1/GroupApproximation/Sofic/TorsionSpectralCollapse.lean>

---

## 27. One-sentence takeaway

The cleanest synthesis is:

\[
\boxed{
\text{Kazhdan rigidity}
+\text{ finitely many movers}
+\text{ one-sided HNN compression}
+\text{ finite-index telescope commensurability}
\Longrightarrow
\text{a sofic action route to sofic non-MF mod-two wreath groups},
}
\]

with operator norm, rank, and Hilbert--Schmidt norm serving respectively as the algebraic, combinatorial-support, and Hilbert-energy layers of the proof.

---

# Continuation: closing the imported gaps and upgrading the endpoint

## 28. Archive correction: the current manuscript has a stronger theorem

The first version of this dossier treated the old action-form “Theorem 4.1” from the email as the only available collapse theorem.  That was too conservative.  The uploaded repository contains the current manuscript source

```text
non_mf_groups_exist.tex
```

and its present Section “Orbit collapse and defect saturation” contains the following theorem.

### Theorem 28.1 (current involutive compression theorem)

Let \(H\) be countable, let \(L\le H\) have property \((T)\), and let \(s\in H\) satisfy
\[
 sLs^{-1}\le L.
\]
An element \(k\in H\) is an **involutive compression witness** if

1. \(k^2=1\);
2. \([s\gamma s^{-1},k]=1\) for every \(\gamma\in L\);
3. the conjugates \(\gamma_1k\gamma_1^{-1}\) and \(\gamma_2k\gamma_2^{-1}\) commute for all \(\gamma_1,\gamma_2\in L\).

Then, for every such \(k\),
\[
 [\gamma,k]\in \operatorname{Rad}_{\mathrm{MF}}(H)
 \qquad(\gamma\in L),
\]
and therefore the normal subgroup generated by all these commutators is contained in the MF radical.

The repository records this endpoint in `Sofic/ManuscriptExactWrappers.lean` and builds the analytic chain in the `InvolutionCollapse*` modules.  Sections 32--33 below give a mathematical reconstruction of all load-bearing estimates rather than merely citing the formal theorem.

This is stronger than the historical finite-mover statement in two ways:

- the conclusion is **pointwise and universal in \(\gamma\)**, not merely existential over a finite mover family;
- the conclusion is genuine **MF-radical membership** for a fixed element, not merely a finite blocking-set obstruction to injectivity.

That distinction resolves the corona/subsequence problem from Sections 6--7: once a **fixed** commutator is under consideration, a failure of radical membership supplies a subsequence on which that same commutator is uniformly separated, and restriction to that subsequence preserves the almost-representation relations.

---

## 29. Full proof of the generalized-wreath soficity theorem

The earlier dossier imported Gao--Kunnawalkam Elayavalli--Patchell Theorem 3.6.  We now prove the construction in full.

### 29.1 Normalized Hamming metric

For a finite set \(A\), write
\[
 d_A(\sigma,\tau)
 =\frac{1}{|A|}\bigl|\{a\in A:\sigma(a)\ne\tau(a)\}\bigr|,
 \qquad \sigma,\tau\in\operatorname{Sym}(A).
\]
It is bi-invariant:
\[
 d_A(\rho\sigma,\rho\tau)=d_A(\sigma,\tau)
 =d_A(\sigma\rho,\tau\rho).
\]
The first equality is obvious because \(\rho\) is injective.  For the second,
\[
 \sigma(\rho(a))\ne\tau(\rho(a))
\]
holds on the inverse image under the bijection \(\rho\) of the disagreement set of \(\sigma\) and \(\tau\), so the cardinality is unchanged.

### 29.2 Sofic groups: the ultraproduct criterion

We use the following standard equivalence, and prove it because it is needed inside the wreath construction.

#### Lemma 29.2

For a countable group \(K\), the following are equivalent.

1. \(K\) is sofic in the usual finitary sense.
2. There are finite sets \(A_n\), a free ultrafilter \(\omega\), and an injective homomorphism
   \[
   \Theta:K\longrightarrow \prod_{\omega}(\operatorname{Sym}(A_n),d_{A_n}).
   \]
3. There are such data and a homomorphism \(\Theta\) for which every \(g\ne1\) satisfies
   \[
   d_\omega(\Theta(g),1)>0.
   \]

#### Proof

\((1)\Rightarrow(2)\). Enumerate \(K=\{g_1,g_2,\dots\}\).  For stage \(n\), choose a sofic approximation
\[
 \theta_n:K\to\operatorname{Sym}(A_n)
\]
which is \(1/n\)-multiplicative on \(F_n=\{g_1,\dots,g_n\}\cup F_n^{-1}\cup F_nF_n\) and satisfies
\[
 d_{A_n}(\theta_n(g),1)>1-1/n
\]
for every nontrivial \(g\in F_n\).  Put
\[
 \Theta(g)=[(\theta_n(g))]_\omega.
\]
For fixed \(g,h\), multiplicativity holds with error tending to zero once \(n\) contains \(g,h,gh\), so \(\Theta(gh)=\Theta(g)\Theta(h)\).  If \(g\ne1\), then
\[
 d_\omega(\Theta(g),1)=1,
\]
so \(\Theta\) is injective.

\((2)\Rightarrow(3)\) is immediate.

\((3)\Rightarrow(1)\). Fix finite \(F\subset K\) and \(\varepsilon>0\).  Write
\[
 \delta=\min_{g\in F\setminus\{1\}}d_\omega(\Theta(g),1)>0,
\]
where the minimum exists because \(F\) is finite.  Choose an integer \(r\) so large that
\[
 (1-\delta/2)^r<\varepsilon.
\]
Represent \(\Theta(g)\) by permutations \(\theta_n(g)\in\operatorname{Sym}(A_n)\).  Because \(\Theta\) is a homomorphism, on an \(\omega\)-large set of indices all multiplicative defects for pairs in \(F\) are smaller than a tolerance \(\eta>0\) to be chosen.  Also, on an \(\omega\)-large set,
\[
 d_{A_n}(\theta_n(g),1)>\delta/2
 \qquad(g\in F\setminus\{1\}).
\]

Amplify the permutation action diagonally to \(A_n^r\):
\[
 \theta_n^{(r)}(g)(a_1,\dots,a_r)
 =\bigl(\theta_n(g)a_1,\dots,\theta_n(g)a_r\bigr).
\]
If \(p=d_{A_n}(\theta_n(g),1)\), then a point of \(A_n^r\) is fixed precisely when all \(r\) coordinates are fixed, hence
\[
 d_{A_n^r}(\theta_n^{(r)}(g),1)
 =1-(1-p)^r
 >1-(1-\delta/2)^r
 >1-\varepsilon.
\]
Similarly, if two permutations disagree on a proportion at most \(\eta\), then their diagonal amplifications disagree on at most
\[
 1-(1-\eta)^r\le r\eta
\]
of \(A_n^r\).  Choose \(\eta<\varepsilon/r\).  One coordinate from the intersection of the finitely many \(\omega\)-large conditions gives the required \((F,\varepsilon)\)-sofic approximation. ∎

### 29.3 Finite direct sums of sofic groups are sofic

If \(K\) is sofic and \(B\) is finite, then the finite direct product
\[
 K^{B}=\prod_{b\in B}K
\]
is sofic.

Indeed, choose sofic approximations \(\theta:K\to\operatorname{Sym}(A)\) good on all coordinates appearing in a prescribed finite subset of \(K^B\).  Let \(K^B\) act on \(A^B\) coordinatewise:
\[
 (k_b)_{b\in B}\cdot(a_b)_{b\in B}
 =\bigl(\theta(k_b)a_b\bigr)_{b\in B}.
\]
Multiplicative errors are bounded by the sum of the coordinate errors.  If \((k_b)\ne1\), choose \(b_0\) with \(k_{b_0}\ne1\); then the fixed-point proportion of the product permutation is at most the fixed-point proportion of \(\theta(k_{b_0})\), so freeness is inherited.  Taking the coordinate tolerances sufficiently small proves soficity.

### 29.4 The finite permutation-wreath metric

Let \(J\) be a group and \(A\) finite.  On
\[
 J^{A}\rtimes\operatorname{Sym}(A)
\]
with the coordinate-permutation action, define
\[
 d_{J,A}(f\sigma,g\tau)
 =\frac1{|A|}\bigl|\{a\in A:
 \sigma(a)\ne\tau(a)
 \text{ or }
 f(\sigma(a))\ne g(\tau(a))\}\bigr|.
\]
This is a bi-invariant metric.  One can see this directly from the action on labelled points: multiplying on either side merely bijectively relabels the tested coordinates and simultaneously translates the group labels.

#### Lemma 29.4 (finite permutation-wreath targets are sofic metric targets)

If \(J\) is sofic and \(A\) finite, there exists an isometric embedding of the metric group
\[
 (J^{A}\rtimes\operatorname{Sym}(A),d_{J,A})
\]
into a metric ultraproduct of finite symmetric groups.

#### Proof

Choose a sofic ultraproduct embedding
\[
 \theta:J\hookrightarrow\prod_\omega\operatorname{Sym}(E_i)
\]
with nontrivial elements at Hamming distance \(1\) from the identity.  Write \(\theta_i(j)\in\operatorname{Sym}(E_i)\) for representatives.

Set
\[
 F_i=E_i\times A.
\]
For \(f\in J^A\) and \(\sigma\in\operatorname{Sym}(A)\), define
\[
 \Pi_i(f\sigma)(x,a)
 =\bigl(\theta_i(f(\sigma(a)))x,\sigma(a)\bigr).
\]
At finite \(i\) this need not be an exact homomorphism because \(\theta_i\) need not be.  In the ultraproduct, however, it is.  Indeed, using the semidirect product rule, the only discrepancy in
\[
 \Pi_i((f\sigma)(g\tau))
 \quad\text{versus}\quad
 \Pi_i(f\sigma)\Pi_i(g\tau)
\]
is a multiplicative defect of \(\theta_i\) for finitely many pairs of elements of \(J\), one for each \(a\in A\).  Since \(A\) is finite, all these defects vanish along \(\omega\).

Now compare \(f\sigma\) and \(g\tau\).  If \(\sigma(a)\ne\tau(a)\), then their images of every point \((x,a)\) have different second coordinates, so the entire fibre \(E_i\times\{a\}\) is a disagreement fibre.  If \(\sigma(a)=\tau(a)=b\), then on that fibre the disagreement proportion is
\[
 d_{E_i}\bigl(\theta_i(f(b)),\theta_i(g(b))\bigr).
\]
If \(f(b)=g(b)\), this tends to \(0\); if they differ, the quotient element \(f(b)^{-1}g(b)\ne1\) has ultralimit Hamming distance \(1\), so the disagreement tends to \(1\).  Averaging over \(a\in A\) gives exactly
\[
 \lim_\omega d_{F_i}(\Pi_i(f\sigma),\Pi_i(g\tau))
 =d_{J,A}(f\sigma,g\tau).
\]
Thus \(f\sigma\mapsto[(\Pi_i(f\sigma))]_\omega\) is an isometric group embedding. ∎

### 29.5 A useful corollary

Suppose a countable group \(W\) admits a homomorphism
\[
 \rho:W\to\prod_\omega
 (J_i^{A_i}\rtimes\operatorname{Sym}(A_i),d_{J_i,A_i})
\]
where each \(J_i\) is sofic.  Then \(W/\ker\rho\) is sofic.

Here is the diagonal argument in full.  Write \(\bar W=W/\ker\rho\), and fix a finite set \(F\subseteq\bar W\) and \(\varepsilon>0\).  Choose representatives \(x_i(w)\in J_i^{A_i}\rtimes\operatorname{Sym}(A_i)\) of \(\rho(w)\) for \(w\in F\cup F^2\cup\{1\}\).  Because \(\rho\) is a homomorphism, for every product \(uv=w\) among these finitely many elements,
\[
 d_{J_i,A_i}\bigl(x_i(u)x_i(v),x_i(w)\bigr)\longrightarrow_\omega0.
\]
If \(w\in F\setminus\{1\}\), then \(\rho(w)\ne1\), so
\[
 \delta_w:=\lim_\omega d_{J_i,A_i}(x_i(w),1)>0.
\]
As \(F\) is finite, \(\delta:=\min_{w\in F\setminus\{1\}}\delta_w>0\).  Hence there is an \(\omega\)-large set of outer indices \(i\) on which all multiplication defects above are smaller than an arbitrarily prescribed \(\eta>0\) and every nontrivial \(w\in F\) satisfies
\[
 d_{J_i,A_i}(x_i(w),1)>\delta/2.
\tag{29.5}
\]
Choose one such outer index \(i\).

By Lemma 29.4, the single metric group
\[
 L_i:=J_i^{A_i}\rtimes\operatorname{Sym}(A_i)
\]
admits an **isometric** homomorphic embedding
\[
 \iota_i:L_i\hookrightarrow\prod_\nu\operatorname{Sym}(E_j)
\]
into a symmetric-group metric ultraproduct.  Apply \(\iota_i\) to the finitely many elements \(x_i(w)\).  Since \(\iota_i\) is a homomorphism and preserves distance exactly in the ultralimit, there is an inner coordinate \(j\) for which all the finitely many multiplication relations are distorted by at most \(2\eta\), while every nontrivial \(w\in F\) has Hamming distance at least \(\delta/3\) from the identity.  This gives a finite permutation almost-model of \(F\) with a uniform positive separation constant.

Finally take the diagonal action on the \(r\)-fold Cartesian power \(E_j^r\).  If a permutation has Hamming distance at least \(c>0\) from the identity, its diagonal \(r\)-fold power fixes at most a proportion \((1-c)^r\) of points, so its Hamming distance is at least \(1-(1-c)^r\).  Choose \(r\) so large that
\[
 1-(1-\delta/3)^r>1-\varepsilon.
\]
The product defect increases by at most a factor \(r\), so choose \(\eta\) initially small enough that the amplified defect is below \(\varepsilon\).  Thus \(F\) has a usual sofic approximation.  Since \(F\) and \(\varepsilon\) were arbitrary, \(\bar W\) is sofic. ∎

### 29.6 Full generalized-wreath theorem

Let \(K\) and \(G\) be countable sofic groups and let
\[
 G\curvearrowright X
\]
be a sofic action.  Put
\[
 W=K^{(X)}\rtimes G,
\]
where \(K^{(X)}\) is the direct sum of finitely supported functions \(X\to K\) and
\[
 (g\cdot f)(x)=f(g^{-1}x).
\]

#### Theorem 29.6

\(W\) is sofic.

#### Proof

Choose increasing finite sets
\[
 F_i\nearrow G,
 \qquad
 E_i\nearrow X,
\]
and \(\varepsilon_i\downarrow0\).  Enlarge \(F_i,E_i\) as necessary so that for the finite pieces under consideration they contain all products, inverses, translates, and lamp supports required below.

By soficity of the action, choose finite sets \(A_i,B_i\), maps
\[
 \varphi_i:G\to\operatorname{Sym}(A_i),
\]
large good sets \(S_i\subseteq A_i\) with
\[
 |S_i|>(1-\varepsilon_i)|A_i|,
\]
and injective charts
\[
 \pi_s^i:E_i\hookrightarrow B_i
 \qquad(s\in S_i)
\]
such that, whenever all terms are defined in the finite window,
\[
 \pi_{\varphi_i(g)s}^i(x)
 =\pi_s^i(g^{-1}x).
\tag{29.1}
\]
Also \(\varphi_i\) is \(\varepsilon_i\)-multiplicative on \(F_i\).

Because \(B_i\) is finite and \(K\) is sofic, Section 29.3 gives that
\[
 J_i:=K^{B_i}
\]
is sofic.

For a lamp function \(f\in K^{(X)}\), let
\[
 p_i(f)=f|_{E_i}\in K^{E_i},
\]
interpreting values outside the support as the identity.  For \(s\in S_i\), the injection \(\pi_s^i:E_i\to B_i\) induces an injective homomorphism
\[
 q_s^i:K^{E_i}\to K^{B_i}
\]
by transporting the labels to \(\pi_s^i(E_i)\) and putting the identity elsewhere.  Put
\[
 P_s^i=q_s^i\circ p_i.
\]

Define a map
\[
 \rho_i:W\to J_i^{A_i}\rtimes\operatorname{Sym}(A_i)
\]
as follows.  Write \(w=fh\) with \(f\in K^{(X)}\), \(h\in G\).  Its permutation part is \(\varphi_i(h)\).  Its lamp coordinate at \(s\in A_i\) is
\[
 L_i(f)(s)=
 \begin{cases}
 P_s^i(f),&s\in S_i,\\
 1,&s\notin S_i.
 \end{cases}
\]
Thus
\[
 \rho_i(fh)=L_i(f)\,\varphi_i(h).
\tag{29.2}
\]

We claim that
\[
 \rho(w):=[(\rho_i(w))]_\omega
\]
defines a homomorphism into the metric ultraproduct.

Take two fixed elements \(w_1=f_1h_1\), \(w_2=f_2h_2\).  Their product is
\[
 w_1w_2=f_1\,(h_1\cdot f_2)\,h_1h_2.
\]
The permutation parts of \(\rho_i(w_1w_2)\) and \(\rho_i(w_1)\rho_i(w_2)\) disagree on at most \(\varepsilon_i|A_i|\) points for large \(i\), by multiplicativity of \(\varphi_i\).

We now compare the lamp coordinates with an explicit bad-set count.  For an input point \(a\in A_i\), put
\[
 b=\varphi_i(h_1h_2)a,
 \qquad
 b'=\varphi_i(h_1)\varphi_i(h_2)a.
\]
Discard exactly the following three sets of inputs:

1. those with \(b\ne b'\); their proportion is at most \(\varepsilon_i\) by multiplicativity of \(\varphi_i\);
2. those with \(b\notin S_i\); since \(\varphi_i(h_1h_2)\) is a permutation, their proportion is \(<\varepsilon_i\);
3. those with \(\varphi_i(h_1)^{-1}b\notin S_i\); again a permutation preserves cardinality, so their proportion is \(<\varepsilon_i\).

Thus the total discarded proportion is \(<3\varepsilon_i\).  On every remaining input we have \(b=b'\), both
\[
 s=b\in S_i,
 \qquad
 r=\varphi_i(h_1)^{-1}s\in S_i,
\]
and \(\varphi_i(h_1)r=s\) **exactly**.  We enlarged \(E_i\) so that the supports of \(f_2\) and \(h_1\cdot f_2\) lie in the chart window.  Applying (29.1) with base point \(r\) therefore gives, for every support coordinate involved,
\[
 \pi_s^i(x)=\pi_r^i(h_1^{-1}x).
\]
Consequently the transported lamp labels satisfy the exact identity
\[
 P_s^i(h_1\cdot f_2)
 =P_{\varphi_i(h_1)^{-1}s}^i(f_2).
\tag{29.3}
\]
This is precisely the semidirect-product coordinate identity required for
\[
 L_i(f_1(h_1\cdot f_2))
 =L_i(f_1)\cdot
   \bigl(\varphi_i(h_1)\cdot L_i(f_2)\bigr)
\]
at every non-discarded input.  The wreath metric already counts the permutation disagreement as bad, so the union bound gives the concrete estimate
\[
 d_{J_i,A_i}\bigl(\rho_i(w_1w_2),\rho_i(w_1)\rho_i(w_2)\bigr)
 <3\varepsilon_i\longrightarrow0.
\]
Therefore \(\rho\) is a homomorphism.

Let
\[
 N=\ker\rho.
\]
By Section 29.5, \(W/N\) is sofic.

It remains to recover the information that might have been lost in \(N\).  Define
\[
 \Psi:W\to (W/N)\times G,
 \qquad
 \Psi(fh)=(fhN,h).
\tag{29.4}
\]
This is a homomorphism.  We prove it is injective.

Suppose \(\Psi(fh)=1\).  Then \(h=1\), so the element is a pure lamp \(f\in K^{(X)}\), and \(f\in N\).  If \(f\ne1\), choose \(x\in X\) with \(f(x)\ne1\).  For all sufficiently large \(i\), \(x\in E_i\).  Since every \(\pi_s^i\) is injective, for every \(s\in S_i\) the transported lamp \(P_s^i(f)\) is nontrivial: at the coordinate \(\pi_s^i(x)\) it has value \(f(x)\ne1\).  Consequently, in the metric \(d_{J_i,A_i}\),
\[
 d_{J_i,A_i}(\rho_i(f),1)
 \ge\frac{|S_i|}{|A_i|}
 >1-\varepsilon_i.
\]
Thus \(d_\omega(\rho(f),1)=1\), contradicting \(f\in N\).  Hence \(f=1\), proving \(\Psi\) injective.

The group \(G\) is sofic by hypothesis, and \(W/N\) is sofic.  Finite direct products of sofic groups are sofic, so \((W/N)\times G\) is sofic.  Every subgroup of a sofic group is sofic (restrict any finite approximation to the prescribed finite subset of the subgroup).  Since \(W\) embeds through \(\Psi\), \(W\) is sofic. ∎

### 29.7 What the theorem actually uses

The proof exposes the roles of the hypotheses exactly:

- soficity of the **action** supplies the local orbit charts \(\pi_s^i\);
- soficity of the **lamp group** makes each finite coordinate group \(K^{B_i}\) sofic;
- soficity of the **acting group** is used only at the final injection \(W\hookrightarrow(W/N)\times G\), because the approximate wreath model may have a kernel projecting nontrivially to the acting coordinate.

This closes one of the largest imported gaps in the first version of the dossier.

---

## 30. Full proof that every action of a LERF group is sofic

We now close the second imported gap.

### 30.1 Chabauty convergence of subgroups

For a countable group \(G\), a sequence of subgroups \(H_n\le G\) converges to \(H\le G\) in the Chabauty topology exactly when for every \(g\in G\),
\[
 1_{H_n}(g)\longrightarrow1_H(g).
\]
Equivalently:

- if \(g\in H\), then \(g\in H_n\) eventually;
- if \(g\notin H\), then \(g\notin H_n\) eventually.

Only finitely many membership tests appear in any finite orbit approximation, which is why this topology is the correct closure notion.

### 30.2 Exact soficity of finite-index coset actions

#### Lemma 30.2

If \(K\le G\) has finite index, then the action
\[
 G\curvearrowright G/K
\]
is sofic, in fact with zero multiplicative and orbit-chart error.

#### Proof

Let
\[
 Y=G/K,
\]
and let
\[
 \rho:G\to Q\le\operatorname{Sym}(Y)
\]
be the finite permutation image of the exact coset action.  Use the finite model set
\[
 A=Q
\]
with \(G\) acting by left multiplication through \(\rho\):
\[
 \varphi(g)(s)=\rho(g)s.
\]
This is an exact homomorphism.  Put \(S=A\), take \(B=Y\), and for \(s\in Q\) define
\[
 \pi_s:E\to Y,
 \qquad
 \pi_s(x)=s^{-1}(x).
\]
Because \(s\) is a permutation of \(Y\), \(\pi_s\) is injective.  Moreover
\[
 \begin{aligned}
 \pi_{\varphi(g)s}(x)
 &=(\rho(g)s)^{-1}(x)\\
 &=s^{-1}\rho(g)^{-1}(x)\\
 &=\pi_s(g^{-1}x),
 \end{aligned}
\]
which is exactly the orbit-chart identity.  Thus both the multiplicative error and the orbit-model error are zero. ∎

### 30.3 Chabauty closure of transitive sofic actions

#### Proposition 30.3

Suppose \(H_n\to H\) in \(\operatorname{Sub}(G)\) and each transitive action
\[
 G\curvearrowright G/H_n
\]
is sofic.  Then
\[
 G\curvearrowright G/H
\]
is sofic.

#### Proof

Fix finite \(F\subseteq G\), finite \(E\subseteq G/H\), and \(\varepsilon>0\).  Choose a section
\[
 \sigma:E\to G
\]
of the quotient map, so \(\sigma(x)H=x\).

There are two finite families of membership conditions.

**Injectivity conditions.**  For distinct \(x,y\in E\),
\[
 \sigma(x)H\ne\sigma(y)H
\]
means
\[
 \sigma(x)^{-1}\sigma(y)\notin H.
\tag{30.1}
\]
By Chabauty convergence, (30.1) remains outside \(H_n\) for all sufficiently large \(n\), simultaneously for all finitely many pairs \(x\ne y\).  Therefore the map
\[
 q_n:E\to G/H_n,
 \qquad
 q_n(x)=\sigma(x)H_n
\tag{30.2}
\]
is injective for large \(n\).

**Transition conditions.**  If \(g\in F\), \(x\in E\), and \(g^{-1}x\in E\), then
\[
 \sigma(g^{-1}x)H=g^{-1}\sigma(x)H.
\]
Hence
\[
 \sigma(g^{-1}x)^{-1}g^{-1}\sigma(x)\in H.
\tag{30.3}
\]
By Chabauty convergence, every element in the finite list (30.3) lies in \(H_n\) for all sufficiently large \(n\).  Thus
\[
 q_n(g^{-1}x)=g^{-1}q_n(x)
\tag{30.4}
\]
whenever the finite-window relation is required.

Choose one large \(n\) satisfying all (30.1)--(30.4).  By soficity of \(G\curvearrowright G/H_n\), choose an \((F,q_n(E),\varepsilon)\)-orbit approximation
\[
 \varphi:G\to\operatorname{Sym}(A)
\]
with good set \(S\subseteq A\) and injective charts
\[
 \rho_s:q_n(E)\hookrightarrow B.
\]
Define
\[
 \pi_s=\rho_s\circ q_n:E\hookrightarrow B.
\]
Injectivity follows from injectivity of both factors.  Whenever \(\varphi(g)s\in S\) and \(g^{-1}x\in E\),
\[
 \begin{aligned}
 \pi_{\varphi(g)s}(x)
 &=\rho_{\varphi(g)s}(q_n(x))\\
 &=\rho_s(g^{-1}q_n(x))\\
 &=\rho_s(q_n(g^{-1}x))\\
 &=\pi_s(g^{-1}x),
 \end{aligned}
\]
where the third equality is (30.4).  The same map \(\varphi\) remains unital and \((F,\varepsilon)\)-multiplicative.  Hence it is an \((F,E,\varepsilon)\)-orbit approximation of \(G/H\). ∎

### 30.4 Orbitwise gluing

#### Lemma 30.4

If every transitive orbit of an action \(G\curvearrowright X\) is a sofic \(G\)-action, then the whole action is sofic.

#### Proof

Fix finite \(F\subseteq G\), \(E\subseteq X\), and \(\varepsilon>0\).  The set \(E\) meets only finitely many orbits, say \(X_1,\dots,X_r\).  Put \(E_j=E\cap X_j\).

For each \(j\), choose a sofic action approximation
\[
 \varphi_j:G\to\operatorname{Sym}(A_j)
\]
with error \(\eta>0\), where \(\eta\) will be chosen much smaller than \(\varepsilon/r\).  Let \(S_j\subseteq A_j\) be its good set and \(\pi^{j}_{s_j}:E_j\to B_j\) the charts.

Set
\[
 A=A_1\times\cdots\times A_r
\]
and define the product permutation
\[
 \varphi(g)(a_1,\dots,a_r)
 =\bigl(\varphi_1(g)a_1,\dots,\varphi_r(g)a_r\bigr).
\]
If each coordinate multiplicative defect is at most \(\eta\), then by the union bound the product defect is at most \(r\eta\).  Set
\[
 S=S_1\times\cdots\times S_r.
\]
Then
\[
 \frac{|S|}{|A|}
 =\prod_{j=1}^r\frac{|S_j|}{|A_j|}
 >(1-\eta)^r
 \ge1-r\eta.
\]
Take \(\eta<\varepsilon/r\).

Let
\[
 B=B_1\sqcup\cdots\sqcup B_r.
\]
For \(s=(s_1,\dots,s_r)\in S\), define \(\pi_s:E\to B\) by using \(\pi^j_{s_j}\) on \(E_j\).  Distinct orbits land in disjoint summands, and within one orbit the chart is injective, so \(\pi_s\) is injective.  The covariance identity is checked within each orbit and is inherited from the corresponding \(\pi^j\).  Thus the whole action is sofic. ∎

### 30.5 LERF implies every action is sofic

Recall that \(G\) is **LERF** (subgroup separable) if every finitely generated subgroup \(H\le G\) is an intersection of finite-index subgroups of \(G\).  Equivalently, for every finitely generated \(H\) and \(g\notin H\), there is a finite-index subgroup \(K\) with
\[
 H\le K,
 \qquad
 g\notin K.
\]

#### Theorem 30.5 (Gao)

Every action of a countable LERF group on a countable set is sofic.

#### Proof

It suffices by Lemma 30.4 to prove every transitive action \(G\curvearrowright G/H\) sofic.

**Step 1: finitely generated stabilizer.**  Suppose first that \(H\) is finitely generated.  Enumerate \(G\setminus H=\{g_1,g_2,\dots\}\).  By LERF, for each \(j\) choose a finite-index subgroup \(K_j\) with
\[
 H\le K_j,
 \qquad
 g_j\notin K_j.
\]
Define
\[
 L_n=K_1\cap\cdots\cap K_n.
\]
Then each \(L_n\) has finite index, \(H\le L_n\), the sequence is decreasing, and
\[
 \bigcap_nL_n=H.
\]
Therefore \(L_n\to H\) in the Chabauty topology: elements of \(H\) lie in every \(L_n\), while if \(g=g_j\notin H\), then \(g\notin L_n\) for all \(n\ge j\).  By Lemma 30.2, each \(G/L_n\) action is sofic.  Proposition 30.3 gives that \(G/H\) is sofic.

**Step 2: arbitrary stabilizer.**  Since \(G\) is countable, so is \(H\).  Enumerate
\[
 H=\{h_1,h_2,\dots\}
\]
and put
\[
 H_r=\langle h_1,\dots,h_r\rangle.
\]
Then each \(H_r\) is finitely generated and \(H_r\to H\): every \(h\in H\) lies in all sufficiently large \(H_r\), while an element outside \(H\) lies in none of them.  By Step 1, every action \(G/H_r\) is sofic.  Proposition 30.3 once again gives \(G/H\) sofic.

By Lemma 30.4, every action is sofic. ∎

### 30.6 A stronger class: LERA groups

Gao's proof actually isolates a broader approximation property.

Call \(K\le G\) **strongly co-amenable** if
\[
 G/\operatorname{core}_G(K)
\]
is amenable, where
\[
 \operatorname{core}_G(K)=\bigcap_{g\in G}gKg^{-1}.
\]
Following Gao, call \(G\) **LERA** (locally extended residually amenable) if for every finitely generated subgroup \(H\le G\) there is a **decreasing sequence** of strongly co-amenable subgroups
\[
 K_1\ge K_2\ge\cdots,
 \qquad
 H=\bigcap_{n\ge1}K_n.
\]
For a decreasing sequence this is automatically Chabauty convergence to \(H\): membership of an element of \(H\) is permanent, while an element outside the intersection eventually leaves the sequence.

We prove that every action of a LERA group is sofic.  The only extra input needed is that every action of an amenable group is sofic; here is a direct proof.

#### Lemma 30.6 (amenable groups have only sofic set-actions)

Let \(Q\) be amenable and \(Q\curvearrowright Y\) any action.  Then the action is sofic.

#### Proof

Fix finite symmetric \(F\subseteq Q\) containing \(1\), finite \(E\subseteq Y\), and \(\varepsilon>0\).  Choose a finite Følner set \(A\subseteq Q\) so invariant under \(F^2\) that
\[
 \frac{|\bigcap_{g\in F^2}gA|}{|A|}>1-\varepsilon.
\]
For each \(q\in F^2\), left multiplication is a bijection
\[
 A\cap q^{-1}A\longrightarrow qA\cap A.
\]
Extend this partial bijection arbitrarily to a permutation \(\varphi(q)\in\operatorname{Sym}(A)\); put \(\varphi(1)=1\), and define \(\varphi\) arbitrarily on group elements outside \(F^2\).

Let
\[
 S=\{a\in A: qa\in A\text{ for every }q\in F^2\}.
\]
Because \(F^2\) is finite and symmetric, the Følner set can be chosen so that \(|S|>(1-\varepsilon)|A|\).  If \(g,h\in F\) and \(a\in S\), then \(ha,gha\in A\), so
\[
 \varphi(g)\varphi(h)a=gha=\varphi(gh)a.
\]
Thus every \(F\)-multiplication test is exact on \(S\), and therefore
\[
 d_A\bigl(\varphi(gh),\varphi(g)\varphi(h)\bigr)
 <\varepsilon.
\]

The definition of a sofic action also requires a **finite** chart target.  Set
\[
 B=\{a^{-1}y:a\in A,\ y\in E\}\subseteq Y.
\]
This is finite.  For every \(a\in A\) define
\[
 \pi_a:E\to B,
 \qquad
 \pi_a(y)=a^{-1}y.
\]
Each \(\pi_a\) is injective because \(a^{-1}\) acts by a bijection of \(Y\).  Now let \(a\in S\), \(g\in F\), assume \(\varphi(g)a\in S\), and let \(g^{-1}y\in E\).  Since \(a\in S\), we have \(ga\in A\), hence the chosen partial extension agrees with left multiplication at \(a\): \(\varphi(g)a=ga\).  Therefore
\[
 \pi_{\varphi(g)a}(y)
 =(ga)^{-1}y
 =a^{-1}g^{-1}y
 =\pi_a(g^{-1}y).
\]
This is exactly the GKEP orbit-chart identity, with finite \(B\), so the action is sofic. ∎

Now if \(K\le G\) is strongly co-amenable, the action \(G\curvearrowright G/K\) factors through the amenable quotient
\[
 Q=G/\operatorname{core}_G(K),
\]
so Lemma 30.6 makes it sofic.

We also record the closure fact that makes the definition stable under the usual finite-intersection refinement.  If \(K_1,\dots,K_r\le G\) are strongly co-amenable and
\[
 C_i=\operatorname{core}_G(K_i),
\]
then
\[
 \operatorname{core}_G\Bigl(\bigcap_{i=1}^rK_i\Bigr)
 =\bigcap_{i=1}^r C_i.
\]
The quotient by this intersection embeds diagonally into
\[
 \prod_{i=1}^r G/C_i,
\]
a finite product of amenable groups.  Amenability passes to finite products and subgroups, so \(\bigcap_iK_i\) is again strongly co-amenable.  Consequently, if a finitely generated subgroup is given merely as a countable intersection of strongly co-amenable subgroups containing it, taking successive finite intersections produces the decreasing sequence required in Gao's definition.

Exactly the proof of Theorem 30.5 now works with “finite-index” replaced by “strongly co-amenable”: finitely generated stabilizers are Chabauty limits of strongly co-amenable subgroups, Proposition 30.3 passes soficity to the limit, arbitrary stabilizers are increasing limits of finitely generated ones, and Lemma 30.4 glues orbits.

#### Theorem 30.7

Every action of a countable LERA group on a countable set is sofic.

Since finite-index subgroups are strongly co-amenable, LERF groups are LERA.  Amenable groups are also LERA (every quotient of an amenable group is amenable).

---

## 31. The universal-action-sofic HNN theorem

The previous two sections allow a clean abstraction.

### Definition 31.1

Call a countable group \(\Gamma\) **universally action-sofic** (UAS) if every action of \(\Gamma\) on a countable set is sofic.

By Theorems 30.5 and 30.7:
\[
 \text{LERF}\Longrightarrow\text{LERA}\Longrightarrow\text{UAS}.
\]
The next lemma records the group-level implication rather than importing it.

### Lemma 31.1A (a sofic left-regular action forces a sofic group)

If the left regular action \(\Gamma\curvearrowright\Gamma\) is sofic as a set-action, then \(\Gamma\) is a sofic group.  Consequently every UAS group is sofic.

#### Proof

Fix a finite set \(F\subseteq\Gamma\) and \(\varepsilon>0\).  Enlarge the action window to a finite set
\[
 E\subseteq\Gamma
\]
containing \(1\), every \(g^{-1}\) with \(g\in F\), and any additional translates required by the finite multiplication tests.  Choose an action-sofic model
\[
 \varphi:\Gamma\to\operatorname{Sym}(A)
\]
with a good set \(S\subseteq A\), \(|S|>(1-\eta)|A|\), and injective charts
\[
 \pi_s:E\hookrightarrow B \qquad(s\in S),
\]
such that on the good set the covariance identity is
\[
 \pi_{\varphi(g)s}(x)=\pi_s(g^{-1}x)
\tag{31.1}
\]
whenever the terms involved belong to the chosen finite window.  The map \(\varphi\) is also \(\eta\)-multiplicative on the prescribed finite group window.

Let \(g\in F\setminus\{1\}\).  Put
\[
 S_g=S\cap\varphi(g)^{-1}S.
\]
Then
\[
 |S_g|\ge |S|+|\varphi(g)^{-1}S|-|A|>(1-2\eta)|A|.
\]
We claim that \(\varphi(g)\) has no fixed point in \(S_g\).  Indeed, if \(s\in S_g\) and \(\varphi(g)s=s\), apply (31.1) with \(x=1\).  Since \(g^{-1}\in E\),
\[
 \pi_s(1)
 =\pi_{\varphi(g)s}(1)
 =\pi_s(g^{-1}),
\]
contradicting injectivity of \(\pi_s\), because \(g^{-1}\ne1\).  Therefore
\[
 d_{\mathrm{Hamm}}(\varphi(g),1)
 \ge\frac{|S_g|}{|A|}>1-2\eta.
\]
Choosing \(\eta<\varepsilon/2\), and simultaneously small enough for the finite multiplication tests, gives an \((F,\varepsilon)\)-sofic approximation of the group \(\Gamma\). ∎

Thus
\[
 \text{LERF}\Longrightarrow\text{LERA}\Longrightarrow\text{UAS}\Longrightarrow\text{sofic}.
\]

### Theorem 31.2 (arbitrary ascending HNN self-embedding over a UAS base)

Let \(\Gamma\) be countable and UAS, and let
\[
 \alpha:\Gamma\hookrightarrow\Gamma
\]
be any injective endomorphism.  Let
\[
 G=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma),\ \gamma\in\Gamma\rangle.
\]
Then the natural action
\[
 G\curvearrowright G/\Gamma
\]
is sofic.

#### Proof

As in Section 9, put
\[
 \Gamma_n=t^{-n}\Gamma t^n,
 \qquad
 N=\bigcup_{n\ge0}\Gamma_n.
\]
Then
\[
 \Gamma_0\le\Gamma_1\le\Gamma_2\le\cdots,
 \qquad
 N\trianglelefteq G,
 \qquad
 G=N\rtimes\langle t\rangle.
\]
Each \(\Gamma_n\cong\Gamma\), so each \(\Gamma_n\) is UAS.  Therefore the restriction of the action on \(X=G/\Gamma\) to \(\Gamma_n\) is sofic for every \(n\).

By the increasing-union permanence lemma proved in Section 13, the restricted action
\[
 N\curvearrowright X
\]
is sofic: a finite control set in \(N\) lies in one \(\Gamma_n\), so the required approximation comes from that level.

Section 12 proved the cyclic-extension permanence theorem for actions: if \(N\curvearrowright X\) is sofic and a compatible action of \(N\rtimes\mathbb Z\) extends it, then the full action is sofic by stacking finitely many translated copies of an \(N\)-model around a large cycle.  Applying that theorem to
\[
 G=N\rtimes\langle t\rangle
\]
gives the result. ∎

### Corollary 31.3

If \(\Gamma\) is LERA -- in particular if it is LERF -- then for **every** injective endomorphism \(\alpha\), the ascending-HNN coset action \(G\curvearrowright G/\Gamma\) is sofic.

This improves Section 15 from LERF to LERA and makes explicit the actual abstract hypothesis used by the telescope argument.

### Corollary 31.4 (wreath products over arbitrary self-embeddings of UAS groups)

Let \(\Gamma\) be UAS, \(\alpha:\Gamma\hookrightarrow\Gamma\) injective, and \(K\) sofic.  With \(G\) as above,
\[
 K^{(G/\Gamma)}\rtimes G
\]
is sofic.

#### Proof

UAS implies \(\Gamma\) sofic.  Section 11 then gives soficity of the ascending HNN group \(G=N\rtimes\mathbb Z\): \(N\) is a directed union of copies of the sofic group \(\Gamma\), and extension by the amenable quotient \(\mathbb Z\) preserves soficity.  Theorem 31.2 gives soficity of the action \(G\curvearrowright G/\Gamma\).  Theorem 29.6 now applies. ∎

This is the strongest general action-soficity conclusion obtainable from the present argument without settling the open problem “are all actions of all sofic groups sofic?”

---

## 32. The three metrics revisited: one defect, two factorizations

This is the conceptual explanation requested in the email.  The mysterious switching between operator norm, rank, and Hilbert--Schmidt norm is not arbitrary.  The same cocycle defect has **two different algebraic decompositions**, each suited to one metric, and the Hilbert--Schmidt estimate is obtained by multiplying the information from the two decompositions.

### 32.1 The basic rank--operator inequality

For every matrix \(D\),
\[
 \|D\|_F^2
 =\sum_j s_j(D)^2
 \le \operatorname{rank}(D)\,\|D\|_{\mathrm{op}}^2,
\tag{32.1}
\]
because there are at most \(\operatorname{rank}(D)\) nonzero singular values and every singular value is at most \(\|D\|_{\mathrm{op}}\).

Thus:

- **rank** controls how many singular directions may contribute;
- **operator norm** controls the size of each contributing singular direction;
- **Frobenius/Hilbert--Schmidt norm** is the total quadratic energy.

Neither rank nor operator norm alone gives the needed energy estimate at the dynamically chosen rank scale \(k_n\), but their product does.

### 32.2 Exact commuting involutions

Let \(V_\lambda,V_\mu\) be commuting self-adjoint involutions.  Since they are commuting normal matrices, they are simultaneously unitarily diagonalizable, with diagonal entries in \(\{\pm1\}\).  Therefore \(V_\lambda-V_\mu\) has diagonal entries in \(\{0,\pm2\}\), so
\[
 \frac{(V_\lambda-V_\mu)^2}{4}
\]
is exactly the projection onto the disagreement subspace.  Hence
\[
 d(\lambda,\mu)
 :=\operatorname{rank}(V_\lambda-V_\mu)
\]
is the number of disagreement coordinates and
\[
 \|V_\lambda-V_\mu\|_F^2=4d(\lambda,\mu).
\tag{32.2}
\]
This identity is why rank is the correct normalization scale for involutive lamps.

### 32.3 The almost-cocycle defect

Fix \(a,\gamma\in L\) and put
\[
 \mu=a^{-1}\gamma,
 \qquad
 U=U_{a,n}.
\]
The normalized displacement is
\[
 b_n(\lambda)=k_n^{-1/2}(V_n(\lambda)-V_n(1)).
\]
The unnormalized cocycle defect is
\[
 \begin{aligned}
 M_n
 &=(V_n(\gamma)-V_n(1))
   -U(V_n(\mu)-V_n(1))U^*
   -(V_n(a)-V_n(1)).
\end{aligned}
\tag{32.3}
\]
Then
\[
 b_n(\gamma)-\operatorname{Ad}(U)b_n(\mu)-b_n(a)
 =k_n^{-1/2}M_n.
\tag{32.4}
\]

#### Operator-norm factorization

A direct rearrangement gives
\[
 M_n
 =\underbrace{V_n(\gamma)-UV_n(\mu)U^*}_{\text{covariance error}}
 +\underbrace{UV_n(1)U^*-V_n(a)}_{\text{covariance error}}.
\tag{32.5}
\]
Each term tends to zero in operator norm, so
\[
 \|M_n\|_{\mathrm{op}}\longrightarrow0.
\tag{32.6}
\]

#### Rank factorization

Do **not** use (32.5) for rank: a tiny operator-norm error can have full rank.  Instead retain the original displacement form (32.3).  By subadditivity of rank and unitary invariance,
\[
 \begin{aligned}
 \operatorname{rank}(M_n)
 &\le d_n(1,\gamma)+d_n(1,\mu)+d_n(1,a).
\end{aligned}
\tag{32.7}
\]
The word bound gives, for a constant \(C=C(a,\gamma)\),
\[
 \operatorname{rank}(M_n)\le Ck_n
\tag{32.8}
\]
for all sufficiently large \(n\).

Combining (32.1), (32.6), and (32.8),
\[
 \begin{aligned}
 \bigl\|b_n(\gamma)-\operatorname{Ad}(U)b_n(\mu)-b_n(a)\bigr\|_F^2
 &=\frac{\|M_n\|_F^2}{k_n}\\
 &\le\frac{\operatorname{rank}(M_n)}{k_n}
       \|M_n\|_{\mathrm{op}}^2\\
 &\le C\|M_n\|_{\mathrm{op}}^2
 \longrightarrow0.
\end{aligned}
\tag{32.9}
\]

This is the entire conceptual story:

> **Operator norm makes the relations exact in the limit; rank remembers the finite-support size; Hilbert--Schmidt norm is the Hilbert-space energy on which property (T) acts.**

The proof switches metrics because each metric answers a different question about the **same** error term.

---

## 33. Full proof of the current involutive compression theorem

We now prove Theorem 28.1 from the ground up at the paper level, including the transport mechanism that was only summarized in the first version of the dossier.

### 33.1 Corona representations and marked extraction

Let
\[
 \mathcal Q_{\mathbf d}
 =\prod_nM_{d_n}(\mathbb C)
   \Big/\bigoplus_nM_{d_n}(\mathbb C)
\]
be a norm matrix corona.  Let
\[
 \pi:H\to U(\mathcal Q_{\mathbf d})
\]
be a homomorphism.  Coordinatewise polar correction allows us to choose exact unitaries
\[
 U_{g,n}\in U(d_n)
\]
representing \(\pi(g)\) such that, for every fixed \(g,h\in H\),
\[
 \|U_{gh,n}-U_{g,n}U_{h,n}\|_{\mathrm{op}}\to0,
\qquad
 \|U_{1,n}-I\|_{\mathrm{op}}\to0.
\tag{33.1}
\]
Replacing \(U_{1,n}\) by \(I\) changes nothing in the corona.

Fix a witness \(k\) and \(\gamma_0\in L\).  To prove
\[
 [\gamma_0,k]\in\ker\pi,
\]
suppose the contrary.  Then
\[
 \|\pi([\gamma_0,k])-1\|>0.
\]
By the definition of the quotient norm, there is \(\delta>0\) and a subsequence, which we relabel by \(n\), such that
\[
 \|U_{[\gamma_0,k],n}-I\|_{\mathrm{op}}\ge\delta
 \qquad\text{for every }n.
\tag{33.2}
\]
All relations (33.1) remain valid after restriction to this subsequence.  This fixed-element extraction is legitimate in a norm corona; it is exactly what was unavailable in the historical *finite-family existential* argument before block amplification.

### 33.2 Exactification of commuting approximate involutions

For \(\gamma\in L\), set
\[
 v_\gamma=\gamma k\gamma^{-1}.
\]
By (W1) and (W3), the family \(\{v_\gamma:\gamma\in L\}\) consists of pairwise commuting involutions.

We need exact commuting matrix involutions approximating their microstates.

#### Lemma 33.2 (finite commuting-involution correction)

Let \(r\ge0\).  Suppose \(W_1,\dots,W_r\) are exact pairwise commuting self-adjoint involutions and \(u\) is a unitary satisfying
\[
 \|u^2-I\|_{\mathrm{op}}\le\eta,
 \qquad
 \|[u,W_j]\|_{\mathrm{op}}\le\eta
 \quad(1\le j\le r).
\]
Then, for \(\eta\) sufficiently small, there is a self-adjoint involution \(W_{r+1}\) commuting exactly with every \(W_j\) and satisfying
\[
 \|W_{r+1}-u\|_{\mathrm{op}}\le C_r\eta
\]
after replacing \(C_r\eta\) by a function tending to zero with \(\eta\) if desired.

#### Proof

For one involution \(W\), the map
\[
 E_W(x)=\frac12(x+WxW)
\]
is a contractive conditional expectation onto the commutant of \(W\), and
\[
 \|E_W(x)-x\|
 =\frac12\|WxW-x\|
 =\frac12\|Wx-xW\|.
\]
Because the \(W_j\) commute, the expectations \(E_{W_j}\) commute.  Put
\[
 E=E_{W_1}\cdots E_{W_r}.
\]
Then \(E(u)\) commutes with all \(W_j\) and a telescoping estimate gives
\[
 \|E(u)-u\|\le\frac r2\eta.
\]
Let
\[
 h=\frac12(E(u)+E(u)^*).
\]
Then \(h=h^*\), it commutes with all \(W_j\), and since \(u\) is close to an involutive unitary, \(h^2\) is close to \(I\).  More explicitly, from \(u^2\approx I\) and unitarity we get \(u^*\approx u\), hence \(E(u)^*\approx E(u)\) and \(h\approx u\).  Therefore
\[
 \|h^2-I\|\to0
\]
as \(\eta\to0\).  For small \(\eta\), the spectrum of \(h\) avoids \((-1/2,1/2)\).  Functional calculus defines
\[
 W_{r+1}=\operatorname{sgn}(h),
\]
which is an exact self-adjoint involution.  Since it is a function of \(h\), it commutes with every \(W_j\), and continuity of the sign function on the spectral set gives \(\|W_{r+1}-h\|\to0\).  Hence \(\|W_{r+1}-u\|\to0\). ∎

Enumerate \(L=\{\lambda_1,\lambda_2,\dots\}\).  Apply Lemma 33.2 diagonally: at stage \(n\), correct the first \(r(n)\) raw orbit matrices, where \(r(n)\to\infty\) sufficiently slowly compared with all relevant multiplicative and commutator errors.  Fill every not-yet-corrected index with the identity matrix (or any fixed exact self-adjoint involution).  We obtain matrices
\[
 V_n(\gamma)
\]
such that for every fixed indices \(\gamma,\mu\in L\):

1. \(V_n(\gamma)=V_n(\gamma)^*=V_n(\gamma)^{-1}\);
2. for every fixed pair \(\gamma,\mu\), \([V_n(\gamma),V_n(\mu)]=0\) exactly for all sufficiently large \(n\); because every later use involves only finitely many fixed indices at a time, we discard a finite initial segment whenever an exact rank identity is invoked;
3. the corrected matrix converges to the raw orbit microstate:
   \[
   \|V_n(\gamma)-U_{v_\gamma,n}\|_{\mathrm{op}}\to0.
   \tag{33.3}
   \]

The group identity
\[
 g v_\gamma g^{-1}=v_{g\gamma}
\]
and (33.1), (33.3) yield the covariance relation
\[
 \|U_{g,n}V_n(\gamma)U_{g,n}^*-V_n(g\gamma)\|_{\mathrm{op}}\to0
\tag{33.4}
\]
for every fixed \(g,\gamma\in L\).

### 33.3 Rank displacement and exact eventual invariance

Define
\[
 d_n(\gamma,\mu)
 =\operatorname{rank}(V_n(\gamma)-V_n(\mu)).
\tag{33.5}
\]
By simultaneous diagonalization of commuting self-adjoint involutions, \(d_n\) is an integer-valued pseudometric and
\[
 \|V_n(\gamma)-V_n(\mu)\|_F^2=4d_n(\gamma,\mu).
\tag{33.6}
\]

For fixed \(g,\gamma,\mu\), define the disagreement projections
\[
 P_n=\frac{(V_n(\gamma)-V_n(\mu))^2}{4},
\qquad
 Q_n=\frac{(V_n(g\gamma)-V_n(g\mu))^2}{4}.
\]
Covariance (33.4) implies
\[
 \|U_{g,n}P_nU_{g,n}^*-Q_n\|_{\mathrm{op}}\to0.
\]
If two orthogonal projections are at operator distance \(<1\), they have equal rank: the restriction of one projection to the range of the other is injective in both directions.  Hence, eventually,
\[
 d_n(g\gamma,g\mu)=d_n(\gamma,\mu).
\tag{33.7}
\]
This is **exact** eventual translation invariance, extracted from approximate covariance by discrete rank rigidity.

### 33.4 Property (T) gives a finite normalization scale

Choose a finite symmetric generating Kazhdan set \(S\subseteq L\) with Kazhdan constant \(\kappa>0\), and assume \(1\in S\) if convenient.  Put
\[
 k_n=\sum_{a\in S}d_n(1,a).
\tag{33.8}
\]

If
\[
 \gamma=a_1a_2\cdots a_r
 \qquad(a_j\in S),
\]
then by the triangle inequality and eventual translation invariance,
\[
 \begin{aligned}
 d_n(1,\gamma)
 &\le \sum_{j=1}^r
 d_n(a_1\cdots a_{j-1},a_1\cdots a_j)\\
 &=\sum_{j=1}^rd_n(1,a_j)\\
 &\le r k_n
\end{aligned}
\tag{33.9}
\]
for all sufficiently large \(n\) depending on \(\gamma\).

We claim \(k_n\ge1\) eventually.  If not, pass to a subsequence with \(k_n=0\).  Then \(V_n(a)=V_n(1)\) for every \(a\in S\).  By (33.9),
\[
 V_n(\gamma_0)=V_n(1)
\]
for all large \(n\) in that subsequence.  Because \(k^2=1\) and the orbit elements commute,
\[
 [\gamma_0,k]
 =v_{\gamma_0}k.
\]
Using (33.3), multiplicativity, and \(V_n(\gamma_0)=V_n(1)\), we obtain
\[
 \|U_{[\gamma_0,k],n}-I\|_{\mathrm{op}}\to0,
\]
contradicting (33.2).  Thus
\[
 k_n\ge1
\tag{33.10}
\]
for all large \(n\).

### 33.5 The normalized displacement cocycle and the mass anchor

On the real Hilbert space underlying \(M_{d_n}(\mathbb C)\) with Frobenius norm, set
\[
 b_n(\gamma)
 =\frac{V_n(\gamma)-V_n(1)}{\sqrt{k_n}}.
\tag{33.11}
\]
By (33.6),
\[
 \|b_n(\gamma)\|_F^2
 =4\frac{d_n(1,\gamma)}{k_n}
 \le4|\gamma|_S.
\tag{33.12}
\]
Moreover, by the very definition of \(k_n\),
\[
 \sum_{a\in S}\|b_n(a)\|_F^2
 =4.
\tag{33.13}
\]
This identity is the **mass anchor** that the proof will contradict.

Let
\[
 \rho_n(g)=\operatorname{Ad}(U_{g,n}).
\]
Each \(\rho_n(g)\) is an exact orthogonal operator on the Frobenius Hilbert space.  By (33.1),
\[
 \|\rho_n(gh)-\rho_n(g)\rho_n(h)\|_{\mathrm{op}}\to0.
\tag{33.14}
\]
Indeed,
\[
 \|\operatorname{Ad}(U)-\operatorname{Ad}(V)\|_{B(M_d)}
 \le2\|U-V\|_{\mathrm{op}}.
\]

Section 32 proved that for every fixed \(a,\gamma\in L\),
\[
 \|b_n(\gamma)-b_n(a)-\rho_n(a)b_n(a^{-1}\gamma)\|_F\to0.
\tag{33.15}
\]
This is the almost-cocycle identity at the rank scale.

### 33.6 Pass to a Hilbert ultraproduct: the cocycle becomes exact

Choose any free ultrafilter \(\omega\).  Give the \(n\)-th matrix space the rescaled inner product
\[
 \langle X,Y\rangle_n
 =\frac{1}{k_n}\operatorname{Re}\operatorname{Tr}(Y^*X)
\]
if one works with the **unnormalized** displacement \(V_n(\gamma)-V_n(1)\), or equivalently keep the ordinary Frobenius norm and use the normalized vectors \(b_n\).  We take the second description.

Let \(\mathcal H_\omega\) be the Hilbert ultraproduct of the matrix Hilbert spaces along \(\omega\).  Because of (33.14),
\[
 \rho(g)[X_n]=[\rho_n(g)X_n]
\]
defines a genuine orthogonal representation of \(L\) on \(\mathcal H_\omega\).  Equation (33.12) shows that
\[
 b(\gamma)=[b_n(\gamma)]
\]
is well-defined for each \(\gamma\), and (33.15) becomes the exact cocycle identity
\[
 b(a\mu)=b(a)+\rho(a)b(\mu).
\tag{33.16}
\]
Thus \(b:L\to\mathcal H_\omega\) is a genuine \(1\)-cocycle.

### 33.7 A self-contained boundedness proof from the Kazhdan pair

We now prove directly that every Hilbert-space cocycle of \(L\) is bounded, using only the Kazhdan pair and the Gaussian kernel.

#### Lemma 33.7 (Gaussian kernel)

If \(z_g\) is any family of vectors in a real Hilbert space and \(t>0\), then
\[
 K_t(g,h)=e^{-t\|z_g-z_h\|^2}
\]
is positive definite.

#### Proof

Write
\[
 e^{-t\|x-y\|^2}
 =e^{-t\|x\|^2}e^{-t\|y\|^2}e^{2t\langle x,y\rangle}.
\]
The kernel \(\langle x,y\rangle^m\) is positive definite because it is the Gram kernel of the tensor vectors \(x^{\otimes m}\).  Therefore
\[
 e^{2t\langle x,y\rangle}
 =\sum_{m=0}^\infty\frac{(2t)^m}{m!}\langle x,y\rangle^m
\]
is positive definite as a locally uniformly convergent sum of positive-definite kernels with nonnegative coefficients.  Multiplication by the scalar factors \(e^{-t\|x\|^2}e^{-t\|y\|^2}\) preserves positive definiteness. ∎

For a cocycle \(b\),
\[
 b(g^{-1}h)=\rho(g^{-1})(b(h)-b(g)),
\]
so
\[
 \|b(g^{-1}h)\|=\|b(h)-b(g)\|.
\tag{33.17}
\]
Thus
\[
 \varphi_t(g)=e^{-t\|b(g)\|^2}
\tag{33.18}
\]
is a normalized positive-definite function.  Let \((\pi_t,\xi_t)\) be its GNS representation, so
\[
 \langle\pi_t(g)\xi_t,\xi_t\rangle=\varphi_t(g),
 \qquad \|\xi_t\|=1.
\]
Since \(S\) is finite, choose \(t>0\) so small that
\[
 \max_{a\in S}
 \|\pi_t(a)\xi_t-\xi_t\|
 <\frac\kappa4.
\tag{33.19}
\]
This is possible because
\[
 \|\pi_t(a)\xi_t-\xi_t\|^2
 =2(1-e^{-t\|b(a)\|^2})\to0
\]
as \(t\downarrow0\).

Let \(P\) be the projection onto the invariant subspace of \(\pi_t\), and write
\[
 \xi_t=P\xi_t+\zeta,
 \qquad \zeta\perp\operatorname{Fix}(\pi_t).
\]
The Kazhdan inequality on the orthogonal complement says
\[
 \kappa\|\zeta\|
 \le\max_{a\in S}\|\pi_t(a)\zeta-\zeta\|.
\]
Since \(P\xi_t\) is invariant, the right side equals the displacement of \(\xi_t\), so by (33.19),
\[
 \|\zeta\|<\frac14.
\tag{33.20}
\]
For every \(g\in L\),
\[
 \|\pi_t(g)\xi_t-\xi_t\|
 =\|\pi_t(g)\zeta-\zeta\|
 \le2\|\zeta\|<\frac12.
\]
Therefore
\[
 2(1-\varphi_t(g))<\frac14,
\]
so
\[
 \varphi_t(g)>\frac78.
\]
Using (33.18),
\[
 e^{-t\|b(g)\|^2}>\frac78,
\]
and hence
\[
 \|b(g)\|^2<\frac1t\log\frac87
 \qquad(g\in L).
\tag{33.21}
\]
Thus the cocycle orbit is uniformly bounded.

### 33.8 Bounded affine orbits in Hilbert space have a fixed point

The cocycle defines the affine isometric action
\[
 \alpha(g)x=\rho(g)x+b(g).
\tag{33.22}
\]
The orbit \(\alpha(L)0=\{b(g):g\in L\}\) is bounded by (33.21).

#### Lemma 33.8 (circumcenter lemma)

Every bounded set \(B\) in a Hilbert space has a unique point minimizing
\[
 r(x)=\sup_{y\in B}\|x-y\|.
\]
If a group of affine isometries preserves \(B\), that minimizer is fixed.

#### Proof

Let \(r_*=\inf_xr(x)\), and choose \(x_n\) with \(r(x_n)^2\le r_*^2+1/n\).  For any \(x,x'\) and \(y\), the parallelogram identity gives
\[
 \left\|\frac{x+x'}2-y\right\|^2
 +\frac14\|x-x'\|^2
 =\frac12\|x-y\|^2+\frac12\|x'-y\|^2.
\]
Taking the supremum over \(y\in B\),
\[
 r\left(\frac{x+x'}2\right)^2
 +\frac14\|x-x'\|^2
 \le\frac12r(x)^2+\frac12r(x')^2.
\]
Since the first term is at least \(r_*^2\), the minimizing sequence is Cauchy.  Its limit \(c\) satisfies \(r(c)=r_*\).  The same inequality shows uniqueness: two minimizers would have zero distance.  Any affine isometry preserving \(B\) preserves \(r\), so it sends \(c\) to another minimizer; uniqueness forces it to fix \(c\). ∎

Applying the lemma to the orbit of \(0\), there is \(w\in\mathcal H_\omega\) fixed by (33.22).  Thus
\[
 \rho(g)w+b(g)=w,
\]
or
\[
 b(g)=w-\rho(g)w
 \qquad(g\in L).
\tag{33.23}
\]
Choose a bounded representative sequence \(w=[w_n]\).

### 33.9 Compressed elements have zero displacement

For \(a\in L\), choose \(\delta_a\in L\) such that
\[
 s a s^{-1}=\delta_a.
\tag{33.24}
\]
By (W2), \(\delta_a\) commutes with \(k\), hence
\[
 v_{\delta_a}=\delta_a k\delta_a^{-1}=k=v_1.
\tag{33.25}
\]
Consequently both \(V_n(\delta_a)\) and \(V_n(1)\) converge in operator norm to the same raw microstate of \(k\).  Since they are commuting exact self-adjoint involutions, once their operator distance is \(<2\) they are equal: simultaneous diagonalization shows that any nonzero difference has an eigenvalue \(\pm2\).  Therefore
\[
 V_n(\delta_a)=V_n(1)
\]
for all sufficiently large \(n\), and hence
\[
 b(\delta_a)=0.
\tag{33.26}
\]
Equation (33.23) then says
\[
 \rho(\delta_a)w=w.
\tag{33.27}
\]
So the primitive is fixed by the compressed copy \(sLs^{-1}\).

At this point pure Hilbert-space reasoning is **not** enough.  From \(sLs^{-1}\le L\), invariance under the compressed subgroup need not imply invariance under all of \(L\) in an arbitrary infinite-dimensional representation.  The missing input is finite-dimensional rank equality at every matrix stage.  We now prove that transport lemma.

### 33.10 The Kazhdan spectral corner

For the finite symmetric Kazhdan set \(S\), define on the finite-dimensional matrix Hilbert space
\[
 A_n
 =\frac1{2|S|}\sum_{a\in S}
   \bigl(\rho_n(a)+\rho_n(a)^*\bigr).
\tag{33.28}
\]
It is self-adjoint and \(\|A_n\|\le1\).  Choose
\[
 1-\frac{\kappa^2}{2|S|}<\theta<1.
\tag{33.29}
\]
Let
\[
 P_n=1_{[\theta,1]}(A_n)
\tag{33.30}
\]
be the high-spectrum projection.

#### Lemma 33.10A (exact Kazhdan spectral gap)

For any genuine unitary representation \(\rho\) of \(L\), if
\[
 A=\frac1{2|S|}\sum_{a\in S}(\rho(a)+\rho(a)^*),
\]
then
\[
 A|_{\operatorname{Fix}(\rho)^\perp}
 \le 1-\frac{\kappa^2}{2|S|}.
\tag{33.31}
\]

#### Proof

For \(\xi\perp\operatorname{Fix}(\rho)\), the Kazhdan inequality gives some \(a\in S\) with
\[
 \|\rho(a)\xi-\xi\|\ge\kappa\|\xi\|.
\]
Therefore
\[
 \sum_{a\in S}\|\rho(a)\xi-\xi\|^2
 \ge\kappa^2\|\xi\|^2.
\]
But
\[
 \langle(1-A)\xi,\xi\rangle
 =\frac1{2|S|}\sum_{a\in S}
   \|\rho(a)\xi-\xi\|^2.
\]
Hence
\[
 \langle A\xi,\xi\rangle
 \le\left(1-\frac{\kappa^2}{2|S|}\right)\|\xi\|^2.
\]
Since this holds for every \(\xi\) in the orthogonal complement, (33.31) follows. ∎

#### Lemma 33.10B (the finite-stage corner is asymptotically fixed)

For every fixed \(g\in L\),
\[
 \|(\rho_n(g)-1)P_n\|_{\mathrm{op}}\to0.
\tag{33.32}
\]

#### Proof

Suppose not.  After taking a subsequence, there are unit vectors \(\xi_n\in\operatorname{Ran}P_n\) and \(\varepsilon>0\) with
\[
 \|\rho_n(g)\xi_n-\xi_n\|\ge\varepsilon.
\tag{33.33}
\]
Take the ordinary Hilbert ultraproduct of these finite-dimensional Hilbert spaces.  Relation (33.14) yields a genuine representation \(\rho\) of \(L\), with averaged operator \(A=[A_n]\).  Let \(\xi=[\xi_n]\).

Choose a continuous function \(f:[-1,1]\to[0,1]\) such that
\[
 f=0\text{ on }
 [-1,1-\kappa^2/(2|S|)],
 \qquad
 f=1\text{ on }[\theta,1].
\]
Because \(\xi_n\in\operatorname{Ran}P_n\),
\[
 f(A_n)\xi_n=\xi_n.
\]
Continuous functional calculus commutes with norm ultraproducts, so
\[
 f(A)\xi=\xi.
\]
By Lemma 33.10A, the spectrum of \(A\) outside the invariant subspace is contained below the support where \(f\) vanishes, while \(A=1\) on the invariant subspace.  Hence \(f(A)\) is exactly the projection onto \(\operatorname{Fix}(\rho)\).  Thus \(\xi\) is invariant, contradicting the ultralimit of (33.33). ∎

#### Lemma 33.10C (spectral capture)

For every vector \(x\),
\[
 \|(1-P_n)x\|^2
 \le\frac{1}{1-\theta}
 \langle(1-A_n)x,x\rangle
 =\frac{1}{2|S|(1-\theta)}
 \sum_{a\in S}\|\rho_n(a)x-x\|^2.
\tag{33.34}
\]

#### Proof

On \(\operatorname{Ran}(1-P_n)\), the spectrum of \(A_n\) is at most \(\theta\), so
\[
 1-A_n\ge(1-\theta)(1-P_n).
\]
Taking the quadratic form at \(x\) gives the inequality.  The displayed identity follows by expanding \(\|\rho_n(a)x-x\|^2\) and using unitarity. ∎

### 33.11 One-sided compression of the corner

Let
\[
 T_n=\rho_n(s)=\operatorname{Ad}(U_{s,n})
\]
and
\[
 Q_n=T_nP_nT_n^*.
\tag{33.35}
\]
The projections \(P_n\) and \(Q_n\) have **exactly the same finite rank**.

#### Lemma 33.11A (one-sided corner inclusion)

\[
 \|(1-Q_n)P_n\|_{\mathrm{op}}\to0.
\tag{33.36}
\]

#### Proof

Let \(x\in\operatorname{Ran}P_n\) be a unit vector.  We must show that \(T_n^*x\) is close to \(\operatorname{Ran}P_n\), because
\[
 \|(1-Q_n)x\|
 =\|(1-P_n)T_n^*x\|.
\tag{33.37}
\]

For \(a\in S\), let \(\delta_a=sas^{-1}\in L\).  Approximate multiplicativity gives
\[
 \|\rho_n(a)T_n^*-T_n^*\rho_n(\delta_a)\|_{\mathrm{op}}\to0.
\tag{33.38}
\]
By Lemma 33.10B,
\[
 \|(\rho_n(\delta_a)-1)x\|
 \le\|(\rho_n(\delta_a)-1)P_n\|\to0
\]
uniformly over unit \(x\in\operatorname{Ran}P_n\).  Hence, using (33.38),
\[
 \|\rho_n(a)T_n^*x-T_n^*x\|\to0
\]
uniformly in such \(x\), for every \(a\in S\).  Lemma 33.10C gives
\[
 \|(1-P_n)T_n^*x\|\to0
\]
uniformly, which is (33.36). ∎

The direction is worth pausing over.  The inclusion \(sLs^{-1}\le L\) says that an \(L\)-fixed vector remains fixed by the **compressed** subgroup.  Conjugating backwards by \(s^{-1}\) therefore maps the high \(L\)-fixed corner approximately into itself; equivalently,
\[
 P_n\lesssim T_nP_nT_n^*=Q_n.
\]

### 33.12 Equal-rank reversal

The one-sided inclusion becomes two-sided because \(P_n\) and \(Q_n\) have the same finite rank.

#### Lemma 33.12

If \(P,Q\) are finite-rank orthogonal projections of equal rank and
\[
 \|(1-Q)P\|<1,
\]
then
\[
 \|(1-P)Q\|=\|(1-Q)P\|.
\tag{33.39}
\]
In particular, if \(\|(1-Q_n)P_n\|\to0\), then
\[
 \|(1-P_n)Q_n\|\to0.
\tag{33.40}
\]

#### Proof

On \(\operatorname{Ran}P\),
\[
 \|(1-Q)P\|^2
 =\|P-PQP\|.
\]
The hypothesis \(<1\) implies that \(PQP|_{\operatorname{Ran}P}\) is invertible, so all its \(r=\operatorname{rank}P\) eigenvalues are positive.  Similarly, the nonzero eigenvalues of \(PQP\) and \(QPQ\) coincide with multiplicity: they are the squares of the singular values of
\[
 QP:\operatorname{Ran}P\to\operatorname{Ran}Q.
\]
Because the ranks are equal and \(QP\) is injective, it is bijective, so \(QPQ|_{\operatorname{Ran}Q}\) has the same full list of \(r\) positive eigenvalues.  Hence the smallest eigenvalues of \(PQP\) and \(QPQ\) agree.  Therefore
\[
 \begin{aligned}
 \|(1-Q)P\|^2
 &=1-\lambda_{\min}(PQP),\\
 \|(1-P)Q\|^2
 &=1-\lambda_{\min}(QPQ),
 \end{aligned}
\]
and the two quantities are equal. ∎

Combining Lemmas 33.11A and 33.12,
\[
 \|(1-P_n)Q_n\|_{\mathrm{op}}\to0.
\tag{33.41}
\]
This is the finite-dimensional “Mautner reversal” that fails in unrestricted infinite-dimensional Hilbert space.  **Finite equal rank is the indispensable resource.**

### 33.13 Scaled transport lemma

We now package the preceding spectral corner estimates at the exact rank scale used by the cocycle.

#### Lemma 33.13 (scaled forward transport)

Let \(x_n\) be a sequence of matrix vectors such that
\[
 \sup_n\frac{\|x_n\|_F^2}{k_n}<\infty.
\tag{33.42}
\]
Suppose
\[
 \frac{\|\rho_n(a)T_n^*x_n-T_n^*x_n\|_F^2}{k_n}\to0
 \qquad(a\in S).
\tag{33.43}
\]
Then
\[
 \frac{\|\rho_n(a)x_n-x_n\|_F^2}{k_n}\to0
 \qquad(a\in S).
\tag{33.44}
\]

#### Proof

Put
\[
 u_n=T_n^*x_n.
\]
By (33.43) and spectral capture (33.34),
\[
 \frac{\|(1-P_n)u_n\|_F^2}{k_n}\to0.
\tag{33.45}
\]
Since \(T_n\) is unitary,
\[
 x_n=T_nu_n
\]
is close at the same scale to
\[
 T_nP_nu_n=Q_nx_n.
\]
Thus
\[
 \frac{\|(1-Q_n)x_n\|_F^2}{k_n}\to0.
\tag{33.46}
\]

By (33.41) and the mass bound (33.42),
\[
 \frac{\|(1-P_n)Q_nx_n\|_F^2}{k_n}
 \le \|(1-P_n)Q_n\|_{\mathrm{op}}^2
      \frac{\|x_n\|_F^2}{k_n}
 \to0.
\]
Together with (33.46),
\[
 \frac{\|(1-P_n)x_n\|_F^2}{k_n}\to0.
\tag{33.47}
\]

Finally, decompose
\[
 x_n=P_nx_n+(1-P_n)x_n.
\]
For \(a\in S\),
\[
 \begin{aligned}
 \|\rho_n(a)x_n-x_n\|_F
 &\le \|(\rho_n(a)-1)P_nx_n\|_F
   +2\|(1-P_n)x_n\|_F\\
 &\le \|(\rho_n(a)-1)P_n\|_{\mathrm{op}}\|x_n\|_F
   +2\|(1-P_n)x_n\|_F.
\end{aligned}
\]
Divide by \(\sqrt{k_n}\).  The first term tends to zero by Lemma 33.10B and (33.42); the second by (33.47).  This proves (33.44).

Exactly the same chain of inequalities is valid with ordinary limits replaced everywhere by limits along a fixed free ultrafilter \(\omega\): the operator-norm corner errors in Lemmas 33.10B--33.12 tend to zero ordinarily and therefore also along \(\omega\), while every remaining step is an inequality between nonnegative scalar sequences.  We will use this ultrafilter form below. ∎

### 33.14 Apply scaled transport to the primitive

Equation (33.27) says, in the ultraproduct,
\[
 \rho(\delta_a)w=w
 \qquad(a\in S).
\]
Therefore, for representatives,
\[
 \frac{\|\rho_n(\delta_a)w_n-w_n\|_F^2}{1}
 \to_\omega0.
\tag{33.48}
\]
Because the \(b_n\) were already normalized by \(\sqrt{k_n}\), one may equivalently formulate the same argument in the unnormalized matrix space with mass scale \(k_n\).  To keep the scale visible, write \(W_n=\sqrt{k_n}w_n\).  Then
\[
 \sup_\omega\frac{\|W_n\|_F^2}{k_n}<\infty
\tag{33.49}
\]
and
\[
 \frac{\|\rho_n(\delta_a)W_n-W_n\|_F^2}{k_n}\to_\omega0.
\tag{33.50}
\]

Put
\[
 X_n=T_n^*W_n.
\]
The group relation \(sas^{-1}=\delta_a\), together with (33.1), gives
\[
 \|\rho_n(a)T_n^*-T_n^*\rho_n(\delta_a)\|_{\mathrm{op}}\to0.
\tag{33.51}
\]
Using (33.49)--(33.51),
\[
 \frac{\|\rho_n(a)X_n-X_n\|_F^2}{k_n}\to_\omega0.
\tag{33.52}
\]
Now apply the ultrafilter form of Lemma 33.13 with \(x_n=W_n\): it returns
\[
 \frac{\|\rho_n(a)W_n-W_n\|_F^2}{k_n}\to_\omega0
 \qquad(a\in S).
\tag{33.53}
\]
Equivalently,
\[
 \|\rho_n(a)w_n-w_n\|_F\to_\omega0.
\tag{33.54}
\]

But the coboundary identity (33.23) means
\[
 \|b_n(a)-(w_n-\rho_n(a)w_n)\|_F\to_\omega0.
\tag{33.55}
\]
Combining (33.54) and (33.55),
\[
 \|b_n(a)\|_F\to_\omega0
 \qquad(a\in S).
\]
Since \(S\) is finite,
\[
 \sum_{a\in S}\|b_n(a)\|_F^2\to_\omega0,
\]
contradicting the exact mass anchor (33.13), which says this sum is identically \(4\) for all sufficiently large stages.

The contradiction proves
\[
 \pi([\gamma_0,k])=1.
\]
Because \(\pi\) was an arbitrary corona representation and \(\gamma_0\in L\) was arbitrary,
\[
 [\gamma,k]\in\operatorname{Rad}_{\mathrm{MF}}(H)
 \qquad(\gamma\in L).
\]
Every corona kernel is normal, so it contains the normal closure of all these commutators.  Hence
\[
 D_{\mathrm{coll}}(L,s)
 \le\operatorname{Rad}_{\mathrm{MF}}(H).
\]
This completes the proof of Theorem 28.1. ∎

### 33.15 Where property \((T)\) is used -- exactly three times

The full proof makes the three uses transparent.

1. **Finite generation:** it supplies the finite symmetric generating Kazhdan set \(S\), hence the finite normalization
   \[
   k_n=\sum_{a\in S}d_n(1,a).
   \]
2. **Bounded affine profile:** the Kazhdan pair bounds the Gaussian GNS representation and forces the displacement cocycle to be bounded, hence a coboundary.
3. **Spectral transport:** the Kazhdan gap isolates the almost-fixed spectral corner \(P_n\), which can then be transported through the one-sided compressor and reversed using equal finite rank.

The first is combinatorial, the second is Hilbert-geometric, and the third is finite-dimensional spectral rigidity.  This is why a proof that merely says “property \((T)\) gives a fixed point” misses a substantial part of the mechanism.

---

## 34. Ascending HNN application: non-co-Hopfian property \((T)\) is enough

We now apply the current theorem directly to the construction proposed in the email.

Let \(\Gamma\) be a countable property \((T)\) group and let
\[
 \alpha:\Gamma\hookrightarrow\Gamma
\]
be a proper injective endomorphism.  Form the ascending HNN extension
\[
 G=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma),\ \gamma\in\Gamma\rangle.
\tag{34.1}
\]
Let
\[
 X=G/\Gamma.
\]
Let \(C_2=\{1,c\}\), and form the permutational wreath product
\[
 W=C_2^{(X)}\rtimes G.
\tag{34.2}
\]
For \(x\in X\), write \(c_x\) for the nontrivial lamp at site \(x\).

### 34.1 The correct basepoint is \(x_0=t\Gamma\)

Set
\[
 x_0=t\Gamma.
\tag{34.3}
\]
The stabilizer of \(x_0\) inside the subgroup \(\Gamma\le G\) is exactly
\[
 \operatorname{Stab}_\Gamma(x_0)=\alpha(\Gamma).
\tag{34.4}
\]

#### Proof

For \(\gamma\in\Gamma\),
\[
 \gamma t\Gamma=t\Gamma
\]
if and only if
\[
 t^{-1}\gamma t\in\Gamma.
\]
If \(\gamma=\alpha(\delta)=t\delta t^{-1}\), then
\[
 t^{-1}\gamma t=\delta\in\Gamma,
\]
so \(\alpha(\Gamma)\) is contained in the stabilizer.

Conversely, if \(t^{-1}\gamma t=\delta\in\Gamma\), then
\[
 \gamma=t\delta t^{-1}=\alpha(\delta),
\]
so \(\gamma\in\alpha(\Gamma)\). ∎

Thus properness of \(\alpha\) supplies some
\[
 \gamma_0\in\Gamma\setminus\alpha(\Gamma)
\]
with
\[
 \gamma_0x_0\ne x_0.
\tag{34.5}
\]

### 34.2 The lamp at \(t\Gamma\) is an involutive compression witness

Take
\[
 L=\Gamma\le W,
 \qquad s=t\in W,
 \qquad k=c_{x_0}.
\]
We verify (W1)--(W3).

**(W1).** Since the lamp group is \(C_2\),
\[
 k^2=1.
\]

**Compression.** By the HNN relation,
\[
 sLs^{-1}=t\Gamma t^{-1}=\alpha(\Gamma)\le\Gamma=L.
\tag{34.6}
\]

**(W2).** For \(\gamma\in\Gamma\),
\[
 t\gamma t^{-1}=\alpha(\gamma).
\]
This element fixes \(x_0=t\Gamma\), because
\[
 \alpha(\gamma)t\Gamma
 =t\gamma t^{-1}t\Gamma
 =t\gamma\Gamma
 =t\Gamma.
\]
Conjugation by an acting-group element sends a lamp at \(x\) to the corresponding lamp at its translate.  Hence
\[
 (t\gamma t^{-1})k(t\gamma t^{-1})^{-1}=k,
\]
so the compressed element commutes with \(k\).

**(W3).** For \(\gamma\in\Gamma\),
\[
 \gamma k\gamma^{-1}=c_{\gamma x_0}.
\]
The base group \(C_2^{(X)}\) is abelian, so any two such lamp conjugates commute.

Therefore \(k\) is an involutive compression witness for \((\Gamma,t)\) inside \(W\).

### 34.3 Every mover gives a fixed MF-radical element

Theorem 28.1 now yields
\[
 [\gamma,k]\in\operatorname{Rad}_{\mathrm{MF}}(W)
 \qquad(\gamma\in\Gamma).
\tag{34.7}
\]
For our commutator convention
\[
 [\gamma,k]=\gamma k\gamma^{-1}k^{-1},
\]
and \(k^{-1}=k\), so
\[
 [\gamma,k]
 =c_{\gamma x_0}c_{x_0}.
\tag{34.8}
\]
If \(\gamma\notin\alpha(\Gamma)\), then \(\gamma x_0\ne x_0\) by (34.4), and the two lamps have distinct supports.  Therefore
\[
 c_{\gamma x_0}c_{x_0}\ne1.
\tag{34.9}
\]
Thus the MF radical is nontrivial.

### Theorem 34.4 (Francesco's non-co-Hopfian reduction, fully proved)

If \(\Gamma\) is a countable property \((T)\) group with a proper injective endomorphism, then there exists a **finitely generated non-MF group**.

A concrete choice is
\[
 W=C_2^{(G/\Gamma)}\rtimes G,
\]
where \(G\) is the ascending HNN extension (34.1).

#### Proof

Non-MF-ness follows from (34.7)--(34.9): a nontrivial element lies in the intersection of the kernels of all norm-corona representations, so no such representation can be injective.

It remains to prove finite generation.  Property \((T)\) implies \(\Gamma\) is finitely generated; let \(S\) be a finite generating set.  Then the ascending HNN extension \(G\) is generated by
\[
 S\cup\{t\}.
\]
The action of \(G\) on \(G/\Gamma\) is transitive.  Hence the conjugates of the single lamp \(k=c_{t\Gamma}\) by elements of \(G\) give all single-site lamps \(c_x\).  These generate the direct-sum base \(C_2^{(X)}\).  Therefore
\[
 W=\langle S,t,k\rangle
\]
is finitely generated. ∎

This proves the central suggestion in the email without the historical condition (iii), without a finite mover pigeonhole, and without any soficity hypothesis.

### 34.5 Finite-index self-embedding: a sofic non-MF theorem

We can now combine the fully proved action and wreath results.

#### Theorem 34.5

Assume in addition that

- \(\Gamma\) is sofic;
- \([\Gamma:\alpha(\Gamma)]<\infty\).

Then
\[
 W=C_2^{(G/\Gamma)}\rtimes G
\]
is **sofic and non-MF**.

#### Proof

Non-MF-ness is Theorem 34.4 and does not use the two additional hypotheses.

For soficity:

1. Section 11 proves \(G\) sofic from soficity of \(\Gamma\): the normal telescope
   \[
   N=\bigcup_{n\ge0}t^{-n}\Gamma t^n
   \]
   is a directed union of sofic groups, and \(G=N\rtimes\mathbb Z\) is sofic.
2. The finite-index hypothesis makes each telescope-level orbit on \(G/\Gamma\) finite.  Section 13 then gives a direct finite-window proof that
   \[
   G\curvearrowright G/\Gamma
   \]
   is a sofic action.
3. \(C_2\) is finite, hence sofic.
4. Theorem 29.6 gives soficity of the generalized wreath product.

Thus \(W\) is both sofic and non-MF. ∎

In particular, **residual finiteness of \(\Gamma\)** is more than enough for the group-soficity input in this finite-index case.

### 34.6 Arbitrary self-embedding over a UAS/LERA base

The finite-index restriction can be replaced by the universal-action-sofic hypothesis from Section 31.

#### Theorem 34.6

Let \(\Gamma\) be a countable property \((T)\), universally action-sofic group, and let
\[
 \alpha:\Gamma\hookrightarrow\Gamma
\]
be any proper injective endomorphism.  Then, with \(G\) and \(W\) as above,
\[
 W=C_2^{(G/\Gamma)}\rtimes G
\]
is sofic and non-MF.

#### Proof

Theorem 34.4 gives non-MF-ness.  UAS implies that \(\Gamma\) is sofic.  Theorem 31.2 gives that \(G\curvearrowright G/\Gamma\) is sofic for arbitrary injective \(\alpha\), and the telescope argument gives group-soficity of \(G\).  Apply Theorem 29.6. ∎

### Corollary 34.7

The conclusion of Theorem 34.6 holds whenever \(\Gamma\) is property \((T)\), LERA, and non-co-Hopfian.  In particular it holds under the stronger hypothesis “property \((T)\), LERF, and non-co-Hopfian.”

This is the cleanest abstract route to the “sofic but non-MF” headline currently justified by the proof package.

### 34.8 What remains open in the broad residual-finite formulation

Suppose merely that \(\Gamma\) is property \((T)\), residually finite, and \(\alpha\) is a proper injective endomorphism of **infinite-index image**.  Then:

- the non-MF conclusion for \(W\) is already proved by Theorem 34.4;
- \(\Gamma\) is sofic, hence the HNN group \(G\) is sofic;
- what is not supplied by the present arguments is soficity of the specific action
  \[
  G\curvearrowright G/\Gamma.
  \]

Residual finiteness alone does not presently imply that every action of \(\Gamma\) is sofic.  Thus the remaining gap is now sharply localized: **it is an action-soficity problem, not an MF-collapse problem.**

---

## 35. Updated proof ledger and new finish lines

The continuation upgrades the status table as follows.

| Claim | Status after continuation |
|---|---|
| Historical max-mover normalization works | **proved at the estimate layer** |
| A subsequence alone kills an element in the norm corona | **false; repaired by finite block amplification for the finite-family obstruction** |
| Current involutive compression theorem | **proved in Section 33; a premise-free Lean proof chain is also present in the audited repository source** |
| Fixed commutator \([\gamma,k]\) is MF-invisible under compression | **proved for every \(\gamma\in L\)** |
| Non-co-Hopfian property \((T)\) suffices to build a finitely generated non-MF group | **proved, Theorem 34.4** |
| Finite-index ascending-HNN coset action is sofic | **proved in Section 13** |
| Generalized wreath theorem “sofic lamp + sofic action + sofic acting group” | **fully proved in Section 29** |
| Every action of a LERF group is sofic | **fully proved in Section 30** |
| Every action of a LERA group is sofic | **proved in Section 30.6** |
| UAS/LERA base \(\Rightarrow\) arbitrary ascending-HNN coset action sofic | **proved, Theorem 31.2** |
| Property \((T)\) + sofic base + proper finite-index self-embedding \(\Rightarrow\) sofic non-MF mod-two wreath | **proved, Theorem 34.5** |
| Property \((T)\) + UAS/LERA + proper self-embedding \(\Rightarrow\) sofic non-MF mod-two wreath | **proved, Theorem 34.6** |
| Mere residual finiteness + arbitrary infinite-index self-embedding \(\Rightarrow\) HNN coset action sofic | **not proved here; remains the genuine frontier** |

### 35.1 The mod-two unconditional endpoint before the torsion generalization

\[
\boxed{
\begin{gathered}
\Gamma\text{ countable, property }(T),\ \alpha:\Gamma\hookrightarrow\Gamma
\text{ proper}\\
\Longrightarrow\quad
C_2^{(G/\Gamma)}\rtimes G\text{ is finitely generated and non-MF},\\
G=\operatorname{HNN}(\Gamma,\alpha),\\
\gamma\notin\alpha(\Gamma)
\Longrightarrow
c_{\gamma t\Gamma}c_{t\Gamma}\in\operatorname{Rad}_{\mathrm{MF}}\setminus\{1\}.
\end{gathered}
}
\]

### 35.2 The mod-two sofic/non-MF endpoint before arbitrary finite lamps

There are two sufficient packages:

\[
\boxed{
\Gamma\text{ property }(T),\ \Gamma\text{ sofic},\
\alpha\text{ proper injective with finite-index image}
}
\]
or, more generally in the self-embedding direction,
\[
\boxed{
\Gamma\text{ property }(T),\ \Gamma\text{ UAS (e.g. LERA)},\
\alpha\text{ any proper injective endomorphism}.
}
\]
In either case
\[
 C_2^{(G/\Gamma)}\rtimes G
\]
is sofic and non-MF.

### 35.3 The conceptual finish line

The complete mechanism can now be written as
\[
\boxed{
\begin{array}{c}
\text{one-sided self-compression}\ sLs^{-1}\le L\\
+\ \text{property }(T)\text{ spectral gap}\\
+\ \text{commuting involutive orbit}\
\end{array}
\Longrightarrow
\text{fixed MF-radical lamp defects}
}
\]
for non-MF-ness, while
\[
\boxed{
\text{sofic acting group}
+\text{sofic set-action}
+\text{sofic lamp group}
\Longrightarrow
\text{sofic generalized wreath product}
}
\]
handles the approximation side.

The two sides are logically independent enough that the remaining research frontier is now visible: after the current compression theorem, the difficult unresolved part of the broadest Francesco program is **not** removing condition (iii); it is deciding when the ascending-HNN coset action is sofic beyond the finite-index and UAS/LERA regimes.

---

## 36. Beyond \(C_2\): projection collapse, arbitrary finite-order lamps, and radical reduction

The current manuscript contains two further deductions from the involutive theorem.  They are short enough to prove completely here and they materially strengthen Theorems 34.4--34.6.

### 36.1 Projection collapse

#### Theorem 36.1

Let \(H\) be countable, \(L\le H\) have property \((T)\), and \(sLs^{-1}\le L\).  Let
\[
 \Theta:H\to U(\mathcal Q)
\]
be a norm-corona representation and let \(p\in\mathcal Q\) be a projection.  Assume

1. \(p\) commutes with \(\Theta(sLs^{-1})\);
2. the projections
   \[
   \Theta(\gamma)p\Theta(\gamma)^*,\qquad\gamma\in L,
   \]
   commute pairwise.

Then \(p\) commutes with \(\Theta(L)\).

#### Proof

Set
\[
 w=1-2p.
\]
Since \(p=p^*=p^2\),
\[
 w^*=w,
 \qquad
 w^2=(1-2p)^2=1-4p+4p^2=1.
\]
Thus \(w\) is a self-adjoint involution.

Let \(H'\) be the subgroup of \(U(\mathcal Q)\) generated by the countable group \(\Theta(H)\) and \(w\).  It is countable.  The image \(\Theta(L)\) is a quotient of \(L\), hence has property \((T)\).  The element \(\Theta(s)\) compresses it because
\[
 \Theta(s)\Theta(L)\Theta(s)^{-1}
 =\Theta(sLs^{-1})\le\Theta(L).
\]

Hypothesis 1 says \(w\) commutes with the compressed copy, because \(w\) is a polynomial in \(p\).  Hypothesis 2 says the \(\Theta(L)\)-conjugates of \(w\) commute: indeed
\[
 \Theta(\gamma)w\Theta(\gamma)^*
 =1-2\Theta(\gamma)p\Theta(\gamma)^*,
\]
and polynomials in pairwise commuting projections commute.

Therefore \(w\) is an involutive compression witness inside \(H'\).  Theorem 28.1 gives
\[
 [\Theta(\gamma),w]\in\operatorname{Rad}_{\mathrm{MF}}(H')
 \qquad(\gamma\in L).
\]
But the inclusion
\[
 H'\hookrightarrow U(\mathcal Q)
\]
is itself a corona representation of \(H'\).  Every element of its MF radical must therefore map to the identity under this inclusion.  Since the inclusion is literally injective as a group map, this means
\[
 [\Theta(\gamma),w]=1
\]
in \(U(\mathcal Q)\).  Thus \(w\) commutes with \(\Theta(\gamma)\), and from
\[
 p=\frac{1-w}{2}
\]
we conclude that \(p\) also commutes with \(\Theta(\gamma)\). ∎

The significance is that the witness need no longer be a group element.  Any corona projection with a commuting \(L\)-orbit and compressed centrality is forced into the full \(L\)-commutant.

### 36.2 Fourier spectral projections for finite-order unitaries

Let \(u\) be a unitary in a unital complex \(C^*\)-algebra with
\[
 u^m=1.
\]
Set
\[
 \zeta=e^{2\pi i/m}
\]
and, for \(j\in\mathbb Z/m\mathbb Z\), define
\[
 p_j=\frac1m\sum_{r=0}^{m-1}\zeta^{-jr}u^r.
\tag{36.1}
\]

#### Lemma 36.2

The \(p_j\) are pairwise orthogonal projections satisfying
\[
 \sum_{j=0}^{m-1}p_j=1,
 \qquad
 u=\sum_{j=0}^{m-1}\zeta^jp_j.
\tag{36.2}
\]

#### Proof

First,
\[
 \begin{aligned}
 p_j^*
 &=\frac1m\sum_{r=0}^{m-1}\zeta^{jr}u^{-r}.
\end{aligned}
\]
Replace \(r\) by \(-r\) modulo \(m\); since \(u^m=1\), this becomes exactly \(p_j\).  Hence \(p_j=p_j^*\).

Next,
\[
 \begin{aligned}
 p_jp_\ell
 &=\frac1{m^2}\sum_{r,s=0}^{m-1}
   \zeta^{-jr-\ell s}u^{r+s}.
\end{aligned}
\]
For each residue \(q=r+s\), put \(s=q-r\).  The coefficient of \(u^q\) is
\[
 \frac1{m^2}\zeta^{-\ell q}
 \sum_{r=0}^{m-1}\zeta^{-(j-\ell)r}.
\]
The finite geometric sum equals \(m\) if \(j=\ell\) and \(0\) otherwise.  Thus
\[
 p_jp_\ell=\delta_{j\ell}p_j.
\]
So the \(p_j\) are pairwise orthogonal projections.

For the sum,
\[
 \sum_jp_j
 =\frac1m\sum_r
 \left(\sum_j\zeta^{-jr}\right)u^r.
\]
The inner sum is \(m\) for \(r=0\) and \(0\) otherwise, yielding \(1\).

Finally,
\[
 \sum_j\zeta^jp_j
 =\frac1m\sum_r
 \left(\sum_j\zeta^{j(1-r)}\right)u^r
 =u,
\]
because only \(r=1\pmod m\) survives. ∎

### 36.3 Torsion collapse

#### Theorem 36.3

Let \(H,L,s\) satisfy the hypotheses of Theorem 28.1.  Let \(k\in H\) have finite order \(m\).  Suppose

1. \(sLs^{-1}\) centralizes \(k\);
2. the conjugates \(\gamma k\gamma^{-1}\), \(\gamma\in L\), commute pairwise.

Then
\[
 [\gamma,k]\in\operatorname{Rad}_{\mathrm{MF}}(H)
 \qquad(\gamma\in L).
\tag{36.3}
\]

#### Proof

Let
\[
 \Theta:H\to U(\mathcal Q)
\]
be an arbitrary corona representation and put
\[
 u=\Theta(k).
\]
Then \(u^m=1\).  Form the Fourier projections \(p_j\) from (36.1).

Because each \(p_j\) is a polynomial in \(u\), every element commuting with \(u\) commutes with every \(p_j\).  Thus the represented compressed subgroup \(\Theta(sLs^{-1})\) commutes with every \(p_j\).

For \(\gamma\in L\),
\[
 \Theta(\gamma)p_j\Theta(\gamma)^*
\]
is the same Fourier polynomial applied to
\[
 \Theta(\gamma)u\Theta(\gamma)^*
 =\Theta(\gamma k\gamma^{-1}).
\]
By hypothesis, the group elements \(\gamma k\gamma^{-1}\) commute pairwise; therefore their represented unitaries commute, and all polynomials in them commute.  Hence the \(L\)-conjugates of each fixed \(p_j\) commute pairwise.

Theorem 36.1 applies to each \(p_j\), giving
\[
 [\Theta(\gamma),p_j]=0
 \qquad(\gamma\in L,\ 0\le j<m).
\]
Fourier reconstruction (36.2) gives
\[
 u=\sum_j\zeta^jp_j,
\]
so \(u\) commutes with \(\Theta(\gamma)\) for every \(\gamma\in L\).  Therefore
\[
 \Theta([\gamma,k])=1.
\]
Since \(\Theta\) was arbitrary, (36.3) follows. ∎

### 36.4 The HNN construction works with every nontrivial finite lamp group

Let \(K\) be **any nontrivial finite group**, not necessarily abelian.  Form
\[
 W_K=K^{(G/\Gamma)}\rtimes G
\]
with the ascending HNN skeleton from Section 34.

Choose any nonidentity \(k_0\in K\).  Since \(K\) is finite, \(k_0\) has finite order.  Let \(k\) be the lamp with value \(k_0\) at
\[
 x_0=t\Gamma
\]
and identity elsewhere.

For \(\gamma\in\Gamma\), the conjugate \(\gamma k\gamma^{-1}\) is the **same lamp value** \(k_0\) moved to the site \(\gamma x_0\).  Two such conjugates either live at distinct sites, in which case the direct-product coordinates commute, or they live at the same site, in which case they are literally the same group element.  Hence the orbit conjugates commute pairwise even if \(K\) itself is nonabelian.

The compressed copy \(t\Gamma t^{-1}=\alpha(\Gamma)\) fixes \(x_0\), so it centralizes \(k\).  Theorem 36.3 gives
\[
 [\gamma,k]\in\operatorname{Rad}_{\mathrm{MF}}(W_K)
 \qquad(\gamma\in\Gamma).
\tag{36.4}
\]
For \(\gamma\notin\alpha(\Gamma)\), the sites \(\gamma x_0\) and \(x_0\) are distinct and
\[
 [\gamma,k]
 =k_{\gamma x_0}k_{x_0}^{-1}\ne1.
\tag{36.5}
\]

#### Theorem 36.4

Every countable non-co-Hopfian property \((T)\) group produces, through any proper injective self-embedding, a finitely generated non-MF permutational wreath product
\[
 K^{(G/\Gamma)}\rtimes G
\]
for **every nontrivial finite lamp group \(K\)**.

#### Proof

Non-MF-ness is (36.4)--(36.5).  Finite generation follows exactly as in Theorem 34.4: \(G\) is finitely generated, the action is transitive, and finitely many generators of the finite group \(K\) placed at one site generate every lamp copy by conjugation. ∎

### Corollary 36.5 (sofic non-MF with arbitrary finite lamps)

Under either soficity package of Theorem 34.5 or Theorem 34.6, the group
\[
 K^{(G/\Gamma)}\rtimes G
\]
is sofic and non-MF for **every nontrivial finite group \(K\)**.

Indeed, every finite \(K\) is sofic, Theorem 29.6 gives soficity, and Theorem 36.4 gives non-MF-ness.

More generally, the same non-MF proof works for any lamp group \(K\) containing a nontrivial finite-order element; finite generation of the total wreath product then additionally requires a finite generating set for \(K\).

### 36.5 Radical pullback through a defect quotient

Let
\[
 \operatorname{Rad}_{\mathrm{MF}}(H)
 =\bigcap_{\pi}\ker\pi,
\]
where \(\pi\) ranges over all norm-matrix-corona representations of \(H\).

#### Lemma 36.6 (exact pullback formula)

If
\[
 N\trianglelefteq H,
 \qquad
 N\le\operatorname{Rad}_{\mathrm{MF}}(H),
\]
and \(q:H\to H/N\) is the quotient map, then
\[
 \operatorname{Rad}_{\mathrm{MF}}(H)
 =q^{-1}\bigl(\operatorname{Rad}_{\mathrm{MF}}(H/N)\bigr).
\tag{36.6}
\]

#### Proof

First let \(x\in\operatorname{Rad}_{\mathrm{MF}}(H)\).  For every corona representation
\[
 \psi:H/N\to U(\mathcal Q),
\]
the composition \(\psi\circ q\) is a corona representation of \(H\), so
\[
 \psi(q(x))=(\psi\circ q)(x)=1.
\]
Hence
\[
 q(x)\in\operatorname{Rad}_{\mathrm{MF}}(H/N),
\]
which proves
\[
 \operatorname{Rad}_{\mathrm{MF}}(H)
 \subseteq q^{-1}(\operatorname{Rad}_{\mathrm{MF}}(H/N)).
\]

Conversely, suppose
\[
 q(x)\in\operatorname{Rad}_{\mathrm{MF}}(H/N).
\]
Let
\[
 \pi:H\to U(\mathcal Q)
\]
be any corona representation.  Because
\[
 N\le\operatorname{Rad}_{\mathrm{MF}}(H)\le\ker\pi,
\]
\(\pi\) factors uniquely through the quotient:
\[
 \pi=\bar\pi\circ q
\]
for some corona representation \(\bar\pi:H/N\to U(\mathcal Q)\).  Then
\[
 \pi(x)=\bar\pi(q(x))=1.
\]
Since \(\pi\) was arbitrary, \(x\in\operatorname{Rad}_{\mathrm{MF}}(H)\). ∎

### Corollary 36.7 (exact radical if the defect quotient is MF)

Let \(D\) be the normal subgroup generated by all involutive or finite-order compression defects covered by Theorems 28.1 and 36.3.  Then
\[
 D\le\operatorname{Rad}_{\mathrm{MF}}(H).
\]
If \(H/D\) is MF, then
\[
 \boxed{\operatorname{Rad}_{\mathrm{MF}}(H)=D.}
\tag{36.7}
\]

#### Proof

An MF group has trivial MF radical because it admits at least one injective matrix-corona representation.  Apply Lemma 36.6. ∎

This is an exact computation principle: once the analytically forced defect quotient can be shown MF, no additional hidden MF-invisible elements exist.

### 36.6 Defect saturation

There is also a useful extreme case.

#### Proposition 36.8

If a normal subgroup
\[
 D\le\operatorname{Rad}_{\mathrm{MF}}(H)
\]
generated by compression defects satisfies \(D=H\), then every corona representation of \(H\) is trivial.  In particular, if \(H\ne1\), then \(H\) is not MF.

#### Proof

Every corona representation kills \(\operatorname{Rad}_{\mathrm{MF}}(H)\), hence kills \(D=H\).  Thus it is trivial.  A nontrivial MF group would possess an injective corona representation, contradiction. ∎

This suggests a further construction program: instead of finding one nontrivial radical element, engineer the normal closure of compression defects to saturate the ambient group.  The uploaded manuscript explicitly identifies this as a possible route toward groups with no nontrivial MF quotients.

---

## 37. Iterating the collapse through the whole HNN telescope

The preceding sections produce more than one nontrivial element of the MF radical.  In the ascending-HNN situation the collapse can be repeated at every telescope level.  This gives a canonical quotient over the height line \(G/N\cong\mathbb Z\), and the entire kernel of that quotient is MF-invisible.

Throughout this section let
\[
 G=\langle \Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma),\ \gamma\in\Gamma\rangle,
\]
where \(\Gamma\) is countable with property \((T)\) and \(\alpha:\Gamma\hookrightarrow\Gamma\) is injective and proper.  Put
\[
 \Gamma_n=t^{-n}\Gamma t^n\qquad(n\ge0),
 \qquad
 N=\bigcup_{n\ge0}\Gamma_n.
\]
Then
\[
 \Gamma_0<\Gamma_1<\Gamma_2<\cdots,
 \qquad
 t\Gamma_n t^{-1}=\Gamma_{n-1}\quad(n\ge1),
 \qquad
 G/N\cong\mathbb Z.
\tag{37.1}
\]
The strictness follows from strictness of \(\alpha(\Gamma)<\Gamma\), after conjugating by powers of \(t\).

Let \(K\ne1\) be a finite group, let
\[
 A=K_{\mathrm{ab}}=K/[K,K],
\]
and define
\[
 X_n=G/\Gamma_n.
\]
Our original wreath product is
\[
 W_0=K^{(X_0)}\rtimes G.
\]
For \(n\ge1\) put
\[
 W_n=A^{(X_n)}\rtimes G.
\]

### 37.1 Pushforward of finitely supported lamps

If \(q:X\twoheadrightarrow Y\) is a map of sets and \(A\) is abelian, there is a canonical pushforward
\[
 q_*:A^{(X)}\longrightarrow A^{(Y)},
 \qquad
 (q_*f)(y)=\prod_{x\in q^{-1}(y)}f(x).
\tag{37.2}
\]
The product is finite because \(f\) has finite support.  Since \(A\) is abelian, its order is immaterial.  If \(q\) is \(G\)-equivariant, then \(q_*\) is \(G\)-equivariant and therefore extends to a homomorphism of semidirect products which is the identity on \(G\).

For the first stage there is also a canonical map
\[
 \Phi_1:K^{(X_0)}\rtimes G\longrightarrow A^{(X_1)}\rtimes G
\tag{37.3}
\]
which first abelianizes each lamp value and then pushes it forward along
\[
 q_1:X_0=G/\Gamma_0\longrightarrow X_1=G/\Gamma_1,
 \qquad
 g\Gamma_0\longmapsto g\Gamma_1.
\]
For \(n\ge1\), let
\[
 \psi_n:W_n\longrightarrow W_{n+1}
\tag{37.4}
\]
be pushforward along \(q_{n+1}:X_n\to X_{n+1}\), and let
\[
 \Phi_n=\psi_{n-1}\circ\cdots\circ\psi_1\circ\Phi_1
 \qquad(n\ge2).
\tag{37.5}
\]
All these maps are onto.

### 37.2 The first collapse quotient is exactly the first pushforward

#### Lemma 37.2

The kernel of \(\Phi_1\) is the normal closure in \(W_0\) of the torsion-collapse commutators
\[
 [\gamma,k_{t\Gamma_0}],
 \qquad
 \gamma\in\Gamma_0,
 \quad k\in K,
\tag{37.6}
\]
where \(k_x\) denotes the copy of \(k\) at the site \(x\in X_0\).  Consequently
\[
 \ker\Phi_1\le \operatorname{Rad}_{\mathrm{MF}}(W_0).
\tag{37.7}
\]

#### Proof

Every \(k\in K\) has finite order.  Section 36.4 showed that \(k_{t\Gamma_0}\) is a torsion compression witness for
\[
 (L,s)=(\Gamma_0,t).
\]
Thus every element in (37.6), and hence its normal closure, lies in the MF radical.

It remains to identify that normal closure with \(\ker\Phi_1\).  Conjugating (37.6) by \(t^{-1}\) gives, up to inversion according to the commutator convention,
\[
 k_{\delta\Gamma_0}k_{\Gamma_0}^{-1},
 \qquad
 \delta=t^{-1}\gamma t\in\Gamma_1.
\tag{37.8}
\]
As \(\gamma\) ranges over \(\Gamma_0\), \(\delta\) ranges over \(\Gamma_1\).  Conjugating further by arbitrary \(g\in G\) gives
\[
 k_{g\delta\Gamma_0}k_{g\Gamma_0}^{-1}
\tag{37.9}
\]
for every \(g\in G\), \(\delta\in\Gamma_1\), and \(k\in K\).  The two sites in (37.9) have the same image in \(G/\Gamma_1\), and conversely every two sites in one fiber of \(q_1\) are connected by such a relation.

Hence the quotient by the normal closure of (37.9) identifies, element by element, all copies of \(K\) lying in one \(q_1\)-fiber.  Each fiber contains at least two sites because \(\Gamma_0<\Gamma_1\).  If \(x\ne y\) lie in one fiber, then distinct lamp copies commute in the restricted direct sum, while the quotient relations say
\[
 a_x=a_y
\qquad(a\in K).
\]
Therefore, for \(a,b\in K\),
\[
 [a_x,b_x]=[a_y,b_x]=1
\]
in the quotient.  Thus the identified copy of \(K\) is automatically abelianized.  One obtains exactly one copy of \(K_{\mathrm{ab}}=A\) for each point of \(X_1\), with distinct copies commuting.  This is precisely \(A^{(X_1)}\), and the \(G\)-action is the natural one.  Therefore the quotient is \(W_1\) and the quotient map is \(\Phi_1\). ∎

### 37.3 Every later telescope step is also radical

#### Lemma 37.3

For every \(n\ge1\),
\[
 \ker\psi_n\le \operatorname{Rad}_{\mathrm{MF}}(W_n).
\tag{37.10}
\]

#### Proof

The subgroup \(\Gamma_n=t^{-n}\Gamma t^n\) has property \((T)\), being isomorphic to \(\Gamma\).  Moreover
\[
 t\Gamma_n t^{-1}=\Gamma_{n-1}\le\Gamma_n.
\]
In the action \(G\curvearrowright X_n=G/\Gamma_n\), choose
\[
 x_n=t\Gamma_n.
\]
The compressed subgroup \(t\Gamma_n t^{-1}=\Gamma_{n-1}\) fixes \(x_n\).  Since \(A\) is finite abelian, every single-site lamp \(a_{x_n}\) has finite order and its \(\Gamma_n\)-conjugates commute pairwise.  Torsion collapse therefore places every commutator
\[
 [\gamma,a_{x_n}],
 \qquad \gamma\in\Gamma_n,
 \quad a\in A,
\]
in \(\operatorname{Rad}_{\mathrm{MF}}(W_n)\).

Conjugating by \(t^{-1}\) changes the mover set from \(\Gamma_n\) to
\[
 t^{-1}\Gamma_n t=\Gamma_{n+1}.
\]
Exactly as in Lemma 37.2, the normal closure of these relations identifies all \(A\)-lamps in each fiber of
\[
 G/\Gamma_n\longrightarrow G/\Gamma_{n+1}.
\]
Because \(A\) is already abelian, the resulting lamp group is simply \(A^{(X_{n+1})}\).  Thus this normal closure is \(\ker\psi_n\), proving (37.10). ∎

### 37.4 Pulling all stages back to the original group

#### Proposition 37.4

For every \(n\ge1\),
\[
 \ker\Phi_n\le\operatorname{Rad}_{\mathrm{MF}}(W_0).
\tag{37.11}
\]

#### Proof

The case \(n=1\) is Lemma 37.2.  Suppose the assertion holds for \(n\).  Since \(\ker\Phi_n\le\operatorname{Rad}_{\mathrm{MF}}(W_0)\), the radical-pullback lemma of Section 36.5 gives
\[
 \operatorname{Rad}_{\mathrm{MF}}(W_0)
 =\Phi_n^{-1}\bigl(\operatorname{Rad}_{\mathrm{MF}}(W_n)\bigr).
\tag{37.12}
\]
By Lemma 37.3,
\[
 \ker\psi_n\le\operatorname{Rad}_{\mathrm{MF}}(W_n).
\]
Taking preimages under \(\Phi_n\) yields
\[
 \ker(\psi_n\Phi_n)=\ker\Phi_{n+1}
 \le\operatorname{Rad}_{\mathrm{MF}}(W_0).
\]
Induction completes the proof. ∎

### 37.5 The limit quotient over \(G/N\cong\mathbb Z\)

Let
\[
 q_\infty:X_0=G/\Gamma_0\longrightarrow G/N,
 \qquad
 g\Gamma_0\longmapsto gN.
\]
Define
\[
 \Phi_\infty:W_0\longrightarrow
 P:=A^{(G/N)}\rtimes G
\tag{37.13}
\]
by the identity on \(G\) and, on a finitely supported lamp configuration \(f:X_0\to K\), by
\[
 \bigl(\Phi_\infty f\bigr)(gN)
 =\prod_{x\in q_\infty^{-1}(gN)}\overline{f(x)}\in A,
\tag{37.14}
\]
where the bar denotes abelianization.  This is well defined, surjective, and \(G\)-equivariant.

#### Theorem 37.5 (telescope-kernel collapse)

\[
 \boxed{
 \ker\Phi_\infty\le\operatorname{Rad}_{\mathrm{MF}}(W_0).
 }
\tag{37.15}
\]
Moreover,
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}(W_0)
 =\Phi_\infty^{-1}\bigl(\operatorname{Rad}_{\mathrm{MF}}(P)\bigr).
 }
\tag{37.16}
\]

#### Proof

The kernels \(\ker\Phi_n\) form an increasing sequence.  We first prove
\[
 \ker\Phi_\infty=\bigcup_{n\ge1}\ker\Phi_n.
\tag{37.17}
\]
The inclusion from right to left is immediate because \(\Gamma_n\le N\).

Conversely, let \(w\in\ker\Phi_\infty\).  Since \(\Phi_\infty\) is the identity on the \(G\)-factor, \(w\) is a pure lamp configuration \(f\) with finite support.  Consider the finitely many support sites.  Whenever two of them, say \(g_i\Gamma_0\) and \(g_j\Gamma_0\), have the same image in \(G/N\),
\[
 g_j^{-1}g_i\in N=\bigcup_n\Gamma_n.
\]
There are only finitely many such pairs, so one can choose \(n\) so large that every such difference belongs to \(\Gamma_n\).  On the finite support of \(f\), the partition into \(G/\Gamma_n\)-fibers is then exactly the partition into \(G/N\)-fibers.  The condition \(\Phi_\infty(f)=1\) says that the product of the abelianized labels in every one of those fibers is \(1\).  Therefore \(\Phi_n(f)=1\), so \(f\in\ker\Phi_n\).  This proves (37.17).

By Proposition 37.4 every \(\ker\Phi_n\) lies in \(\operatorname{Rad}_{\mathrm{MF}}(W_0)\).  Since the kernels are increasing, their union is a subgroup, hence (37.17) gives (37.15).

Finally apply the radical-pullback lemma to the quotient \(W_0/\ker\Phi_\infty\cong P\).  Since the kernel lies in the radical, the lemma gives exactly (37.16). ∎

### 37.6 Interpretation: the entire telescope fiber becomes invisible

Let
\[
 h:G\twoheadrightarrow G/N\cong\mathbb Z
\]
be the height homomorphism, normalized by \(h(t)=1\) and \(h(\Gamma)=0\).  Under \(G/N\cong\mathbb Z\), the group \(P\) is
\[
 P\cong A^{(\mathbb Z)}\rtimes_h G,
\tag{37.18}
\]
where \(g\in G\) shifts the integer-indexed lamps by \(h(g)\).

Thus every corona representation of \(W_0\) forgets, at minimum, all information in a lamp configuration except the **abelianized total lamp value on each height fiber**.  For \(K=C_2\), this says that only the mod-two parity of the lamps in each height fiber can survive the iterated collapse.

A particularly strong special case is immediate.

#### Corollary 37.6A (perfect finite lamps disappear completely)

If \(K\) is finite and perfect, so \(K_{\mathrm{ab}}=1\), then
\[
 K^{(G/\Gamma)}\le\operatorname{Rad}_{\mathrm{MF}}(W_0).
\tag{37.19}
\]
In fact \(P=G\), and
\[
 \operatorname{Rad}_{\mathrm{MF}}(W_0)
 =\Phi_\infty^{-1}\bigl(\operatorname{Rad}_{\mathrm{MF}}(G)\bigr).
\tag{37.20}
\]

So for a perfect finite lamp group, **the entire lamp subgroup is invisible in every matrix-corona representation**.

### 37.7 Exact radical when the HNN skeleton is MF

The limit quotient \(P\) is itself MF whenever the skeleton \(G\) is MF.  We prove this rather than invoking a permanence theorem.

#### Lemma 37.7A (finite abelian lamplighters are residually finite)

If \(A\) is finite abelian, then
\[
 L_A=A^{(\mathbb Z)}\rtimes\mathbb Z
\]
is residually finite.

#### Proof

Take a nonidentity \((f,n)\in L_A\).

If \(n\ne0\), choose \(m\ge2\) with \(n\not\equiv0\pmod m\).  Reduction of the shift coordinate modulo \(m\), together with summing lamp values over residue classes modulo \(m\), gives a homomorphism
\[
 L_A\longrightarrow A^{(\mathbb Z/m\mathbb Z)}\rtimes\mathbb Z/m\mathbb Z
\]
to a finite group, and the image of \((f,n)\) is nontrivial because its shift coordinate is nonzero.

If \(n=0\) and \(f\ne1\), choose \(m\) larger than the diameter of the finite support of \(f\).  Then distinct support integers remain distinct modulo \(m\), so the reduced lamp configuration is still nontrivial in the same finite quotient. ∎

#### Lemma 37.7B (residually finite implies MF)

Every countable residually finite group is MF.

#### Proof

Enumerate the nonidentity elements as \(g_1,g_2,\ldots\).  For each \(j\), choose a finite quotient
\[
 q_j:H\to F_j
\]
with \(q_j(g_j)\ne1\), and let \(\lambda_j:F_j\to U(\mathbb C^{F_j})\) be the left regular permutation representation.  At stage \(n\), take the finite-dimensional genuine representation
\[
 \pi_n=\bigoplus_{j=1}^{n}\lambda_jq_j.
\]
For a fixed nontrivial \(g_r\), every \(n\ge r\) contains the fixed block \(\lambda_rq_r(g_r)\ne1\).  Hence
\[
 \|\pi_n(g_r)-1\|_{\mathrm{op}}
 \ge \|\lambda_rq_r(g_r)-1\|_{\mathrm{op}}>0
\]
for all \(n\ge r\).  Therefore the induced homomorphism into the norm matrix corona is injective. ∎

#### Lemma 37.7C (direct products and subgroups of MF groups are MF)

If \(H_1,H_2\) are MF, then \(H_1\times H_2\) is MF; every subgroup of an MF group is MF.

#### Proof

The subgroup assertion follows by restricting an injective corona representation.  For products, let
\[
 \Theta_i:H_i\to\prod_nU(d_{i,n})/\bigoplus_nU(d_{i,n})
\]
be injective corona representations.  After harmless reindexing, choose unitary representatives and send
\[
 (g,h)\longmapsto
 \left[
 \begin{pmatrix}
 U_n(g)&0\\
 0&V_n(h)
 \end{pmatrix}
 \right].
\]
The block-diagonal construction is multiplicative in the corona.  If \((g,h)\ne(1,1)\), at least one block sequence does not converge to the identity in operator norm; since the norm of a block diagonal is the maximum of the block norms, the full block-diagonal sequence also does not converge to the identity.  Hence the product representation is injective. ∎

#### Proposition 37.7D

If \(G\) is MF, then \(P=A^{(\mathbb Z)}\rtimes_hG\) is MF.

#### Proof

By Lemmas 37.7A and 37.7B, the lamplighter
\[
 L_A=A^{(\mathbb Z)}\rtimes\mathbb Z
\]
is MF.  Define
\[
 \iota:P\longrightarrow G\times L_A,
 \qquad
 \iota(f,g)=\bigl(g,(f,h(g))\bigr).
\tag{37.21}
\]
Because the action of \(g\) on \(A^{(\mathbb Z)}\) is exactly the shift by \(h(g)\), \(\iota\) is a homomorphism.  It is plainly injective from its first and second coordinates.  If \(G\) is MF, then \(G\times L_A\) is MF by Lemma 37.7C, and so its subgroup \(P\) is MF. ∎

Combining this with Theorem 37.5 gives an exact radical computation.

#### Theorem 37.7E (exact telescope radical under an MF skeleton)

If the ascending-HNN skeleton \(G\) is MF, then
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}
 \bigl(K^{(G/\Gamma)}\rtimes G\bigr)
 =\ker\Phi_\infty.
 }
\tag{37.22}
\]
Equivalently, the universal MF quotient of the finite-lamp wreath product is exactly
\[
 \bigl(K^{(G/\Gamma)}\rtimes G\bigr)
 \big/
 \operatorname{Rad}_{\mathrm{MF}}\bigl(K^{(G/\Gamma)}\rtimes G\bigr)
 \ \cong\ 
 K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG.
\tag{37.23}
\]

#### Proof

Proposition 37.7D makes \(P\) MF, hence
\[
 \operatorname{Rad}_{\mathrm{MF}}(P)=1.
\]
Equation (37.16) therefore becomes
\[
 \operatorname{Rad}_{\mathrm{MF}}(W_0)=\Phi_\infty^{-1}(1)=\ker\Phi_\infty.
\]
The quotient description is the first isomorphism theorem together with (37.18). ∎

This is strictly stronger than the original non-MF conclusion: under the additional MF hypothesis on the HNN skeleton, the matrix-corona theory of the entire finite-lamp wreath product is computed exactly.

---

## 38. Independent verification, source synchronization, and the remaining frontier

### 38.1 Wolfram sanity checks

The symbolic proofs above do not depend on computer algebra, but two finite-dimensional identities central to the argument were independently sanity-checked in a Wolfram kernel.

For explicit commuting diagonal self-adjoint involutions \(V,W\), with \(D=V-W\), the kernel returned
\[
 D^3=4D,
 \qquad
 \operatorname{Tr}(D^*D)=4\operatorname{rank}(D),
\]
and in the chosen \(6\times6\) example it computed
\[
 \operatorname{rank}(D)=3,
 \qquad
 \operatorname{Tr}(D^*D)=12.
\]
For a diagonal unitary of order \(5\), it also verified that the discrete Fourier elements
\[
 p_j=\frac15\sum_{r=0}^{4}\zeta^{-jr}u^r
\]
are pairwise orthogonal projections and that
\[
 u=\sum_{j=0}^{4}\zeta^jp_j.
\]
The returned Boolean/value tuple was
\[
 (\mathrm{True},\mathrm{True},3,12,\mathrm{True},\mathrm{True}).
\]
These computations are only cross-checks; Sections 33 and 36 contain the general proofs.

### 38.2 Current GitHub manuscript synchronization

The current repository manuscript contains, in this order, the involutive compression witness, involutive collapse theorem, projection collapse theorem, torsion collapse theorem, commuting-lamp quotient, exact radical pullback, and defect-saturation theorem.  The source also records Lean endpoints for the involutive, projection, and torsion statements.  The proofs in Sections 33 and 36 above reconstruct the mathematics rather than treating those endpoint declarations as black boxes.

In particular, the present manuscript formulation is stronger than the historical finite-mover criterion discussed in the email:

- the historical max-mover argument gives a **finite-family obstruction** sufficient for non-MF-ness;
- the compression theorem gives **fixed-element radical membership** for every commutator attached to a valid torsion witness;
- iterating that theorem through the HNN telescope gives the whole kernel in Theorem 37.5;
- if the skeleton is MF, Theorem 37.7E computes the radical exactly.

### 38.3 What is now fully closed

The following implications have been proved in this dossier rather than merely asserted:

1. A countable property-\((T)\), non-co-Hopfian group produces a finitely generated non-MF group via an ascending HNN extension and any nontrivial finite lamp group.
2. No finite-index hypothesis on the self-embedding is needed for that non-MF conclusion.
3. If the self-embedding has finite-index image and the base is sofic, the natural HNN coset action is sofic, hence the finite-lamp wreath product is sofic and non-MF.
4. More generally, if the base is universally action-sofic -- in particular LERA, hence in particular LERF -- the same sofic/non-MF conclusion holds for an arbitrary proper injective self-embedding.
5. For every finite lamp group, the entire telescope kernel \(\ker\Phi_\infty\) lies in the MF radical.
6. If the HNN skeleton itself is MF, that telescope kernel is the **entire** MF radical.

### 38.4 The clean remaining frontier

The main unresolved branch left by these arguments is now sharply isolated:

> Let \(\Gamma\) be a sofic property-\((T)\) group and \(\alpha:\Gamma\hookrightarrow\Gamma\) a proper injective endomorphism of possibly infinite index.  Must the natural action of the ascending HNN extension \(G\curvearrowright G/\Gamma\) be sofic?

The group \(G\) itself is sofic by the directed-union-plus-amenable-extension argument.  The action is amenable/co-amenable by the explicit HNN Følner construction.  What is missing in this level of generality is a theorem converting those two facts into soficity of the **specific action**.  Sections 13 and 31 close the problem respectively under finite-index and UAS/LERA hypotheses, but the general “sofic stabilizer/base + co-amenable action” implication is not proved here and should not be silently assumed.

That is now the genuine action-theoretic bottleneck; the non-MF half has been pushed past it.

---

## 39. A completely concrete affine matrix base and an unconditional exact-radical family

The abstract statement “take a property-\((T)\) group which is not co-Hopfian” can be made concrete in the uploaded project.  The elementary matrix calculations below also show why the self-embedding has finite index and why its ascending HNN extension is MF, which upgrades Theorem 37.7E from a conditional theorem to an exact computation for this literal family.

### 39.1 The six affine generators and the doubling matrix

Work in \(\mathrm{GL}_4(\mathbb Q)\).  Write matrices in affine block form
\[
 \begin{pmatrix}A&v\\0&1\end{pmatrix},
 \qquad A\in\mathrm{GL}_3(\mathbb Q),\ v\in\mathbb Q^3.
\]
The repository uses the three rotation matrices
\[
 x=
 \begin{pmatrix}
 0&1&0&0\\
 0&0&1&0\\
 1&0&0&0\\
 0&0&0&1
 \end{pmatrix},
\quad
 y=
 \begin{pmatrix}
 1&0&1&0\\
 0&-1&-1&0\\
 0&1&0&0\\
 0&0&0&1
 \end{pmatrix},
\quad
 z=
 \begin{pmatrix}
 0&1&0&0\\
 1&0&0&0\\
 -1&-1&-1&0\\
 0&0&0&1
 \end{pmatrix},
\tag{39.1}
\]
and the three unit translations
\[
 v_1=
 \begin{pmatrix}
 1&0&0&1\\0&1&0&0\\0&0&1&0\\0&0&0&1
 \end{pmatrix},
\quad
 v_2=
 \begin{pmatrix}
 1&0&0&0\\0&1&0&1\\0&0&1&0\\0&0&0&1
 \end{pmatrix},
\quad
 v_3=
 \begin{pmatrix}
 1&0&0&0\\0&1&0&0\\0&0&1&1\\0&0&0&1
 \end{pmatrix}.
\tag{39.2}
\]
Let
\[
 \Gamma_*:=\langle x,y,z,v_1,v_2,v_3\rangle
 \le\mathrm{GL}_4(\mathbb Q).
\tag{39.3}
\]
Finally set
\[
 D=\operatorname{diag}(2,2,2,1).
\tag{39.4}
\]
All six generators in (39.1)--(39.2), and their inverses, have integral entries.

The GitHub source calls this subgroup `gammaBar` and the conjugation map below `conjD`.

### 39.2 Internal semidirect-product normal form

For \(a=(a_1,a_2,a_3)^T\in\mathbb Z^3\), write
\[
 T_a=
 \begin{pmatrix}
 I_3&a\\0&1
 \end{pmatrix}.
\]
Then
\[
 T_aT_b=T_{a+b},
 \qquad
 T_a^{-1}=T_{-a},
\tag{39.5}
\]
and \(v_i=T_{e_i}\).  Thus
\[
 \mathcal T:=\langle v_1,v_2,v_3\rangle
 =\{T_a:a\in\mathbb Z^3\}
 \cong\mathbb Z^3.
\tag{39.6}
\]
Let
\[
 \mathcal R:=\langle x,y,z\rangle.
\]
Every element of \(\mathcal R\) has block form
\[
 R_A=\begin{pmatrix}A&0\\0&1\end{pmatrix}
\]
with \(A\in\mathrm{GL}_3(\mathbb Z)\).  Direct block multiplication gives
\[
 R_AT_aR_A^{-1}=T_{Aa}.
\tag{39.7}
\]
Therefore \(\mathcal R\) normalizes \(\mathcal T\).

Every word in the six generators can consequently be moved, using (39.7), into the form
\[
 T_aR_A.
\tag{39.8}
\]
This form is unique.  Indeed, if
\[
 T_aR_A=T_bR_B,
\]
then comparison of the upper-left \(3\times3\) blocks gives \(A=B\), and comparison of the last columns then gives \(a=b\).  Hence
\[
 \boxed{\Gamma_*=\mathcal T\rtimes\mathcal R.}
\tag{39.9}
\]
No presentation-completeness theorem is needed for this normal form: it follows directly inside the displayed matrix subgroup.

For reference, multiplying the explicit matrices also yields the conjugation rules recorded in the Lean source, for example
\[
 xv_1x^{-1}=v_3,
 \quad xv_2x^{-1}=v_1,
 \quad xv_3x^{-1}=v_2,
\]
and analogous integral translation formulas for \(y\) and \(z\); these are concrete instances of (39.7).

### 39.3 Doubling is a proper injective endomorphism

Because \(D\) is scalar on the first three coordinates,
\[
 DR_AD^{-1}=R_A
\tag{39.10}
\]
for every \(R_A\in\mathcal R\).  On translations,
\[
 DT_aD^{-1}=T_{2a}.
\tag{39.11}
\]
Consequently conjugation by \(D\) preserves \(\Gamma_*\) and defines
\[
 \alpha:\Gamma_*\hookrightarrow\Gamma_*;
 \qquad
 \alpha(T_aR_A)=T_{2a}R_A.
\tag{39.12}
\]
It is injective because it is restriction of conjugation by an invertible matrix.

It is not surjective: \(v_1=T_{e_1}\) cannot equal \(T_{2a}R_A\).  Comparing the upper-left block forces \(A=I\), after which the translation equation would be
\[
 2a=e_1,
\]
impossible for \(a\in\mathbb Z^3\).  Equivalently,
\[
 D^{-1}v_1D=T_{e_1/2}
\]
has a \(1/2\) entry, while every element of \(\Gamma_*\) has integral entries.

Thus \(\Gamma_*\) is non-co-Hopfian once property \((T)\) is established.

### 39.4 The image has index exactly eight

From (39.9) and (39.12),
\[
 \alpha(\Gamma_*)=2\mathcal T\rtimes\mathcal R
 =\{T_{2a}R_A:a\in\mathbb Z^3,\ R_A\in\mathcal R\}.
\tag{39.13}
\]
Every element \(T_aR_A\) has the same right coset modulo \(\alpha(\Gamma_*)\) as \(T_a\), because \(R_A\in\alpha(\Gamma_*)\).  Moreover
\[
 T_a\alpha(\Gamma_*)=T_b\alpha(\Gamma_*)
\]
if and only if
\[
 T_{b-a}\in\alpha(\Gamma_*)\cap\mathcal T=2\mathcal T,
\]
which is equivalent to
\[
 a\equiv b\pmod{2\mathbb Z^3}.
\]
Hence the eight parity vectors
\[
 \{0,1\}^3
\]
give a complete set of coset representatives and
\[
 \boxed{[\Gamma_*:\alpha(\Gamma_*)]=8.}
\tag{39.14}
\]
This supplies the finite-index hypothesis of Section 13 for the literal self-embedding.

### 39.5 Residual finiteness of the affine base

The group \(\Gamma_*\) actually lies in \(\mathrm{GL}_4(\mathbb Z)\): all generators and inverses are integral, hence so is every word and its inverse.

Let \(g\in\Gamma_*\setminus\{1\}\).  Some entry of \(g-I\) is a nonzero integer \(m\).  Choose a prime \(p\nmid m\).  Entrywise reduction modulo \(p\) gives a homomorphism
\[
 \mathrm{GL}_4(\mathbb Z)\longrightarrow\mathrm{GL}_4(\mathbb F_p).
\tag{39.15}
\]
The target is finite, and the chosen entry shows that the image of \(g\) is not the identity.  Thus
\[
 \boxed{\Gamma_*\text{ is residually finite}.}
\tag{39.16}
\]
By Lemma 37.7B it is MF; by the analogous finite-permutation construction it is also sofic.

### 39.6 Property \((T)\): the certified chain

The remaining structural input is property \((T)\).  Here the uploaded project contains an exact, premise-free Lean certificate chain, not merely a literature citation.  I audited the source declarations and their dependency path; I did not independently rerun the Lean kernel in this session.  Its logical chain is as follows.

1. A six-generator, thirteen-relator Steinberg-type group \(P_{13}\) is equipped with an exact rational sum-of-squares/Hodge certificate.  The certificate yields a Laplacian gap
   \[
   \operatorname{spec}(\Delta)\subseteq\{0\}\cup[1/500,\infty)
   \tag{39.17}
   \]
   in every orthogonal representation.  Since \(\ker\Delta\) is exactly the invariant-vector subspace, (39.17) is a Kazhdan spectral gap and proves property \((T)\) for \(P_{13}\).
2. A checked surjection from \(P_{13}\) onto the rotation presentation transfers property \((T)\) to the rotation group.
3. The affine-base bridge then proves property \((T)\) for the full translation-by-rotation group.  Conceptually, given a unit vector which is \(\kappa/64\)-almost fixed on a finite control set, first project it to the rotation-fixed subspace.  The Kazhdan inequality makes that projection move the vector by less than \(1/64\).  The explicit translation-orbit normal form gives a uniform \(1/8\) bound on the orbit of this projected vector under the whole translation lattice.  The Hilbert-space circumcenter of that bounded translation orbit is translation-fixed; normality of the translation subgroup and rotation invariance of the starting projection make the resulting point rotation-fixed as well.  It remains within distance \(<1\) of the original unit vector, so it is nonzero and globally fixed.
4. The checked affine quotient onto the concrete matrix subgroup \(\Gamma_*\) is surjective, and property \((T)\) passes to quotients.

Therefore
\[
 \boxed{\Gamma_*\text{ has property }(T).}
\tag{39.18}
\]

The exact formal endpoint is `gammaBar_hasKazhdanPropertyT` in
`GroupApproximation/Sofic/CommutingLampCollapse.lean`; it is proved from the premise-free theorem `manuscriptBaseHasKazhdanPropertyT`.  The latter is itself obtained from `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT` via explicit surjective transfers.  The raw certificate coefficients are proof data rather than a new conceptual step, so they are not duplicated as thousands of numerical entries in this Markdown note.  The audited Lean source performs the certificate arithmetic exactly; the present session verifies the source chain and absence of placeholders, not a fresh kernel execution.

Combining (39.12), (39.14), and (39.18), \(\Gamma_*\) is an explicit residually finite property-\((T)\) group with a proper injective self-embedding of index \(8\).

### 39.7 The HNN skeleton embeds in \(\mathrm{GL}_4(\mathbb Z[1/2])\)

Form the ascending HNN extension
\[
 G_*=
 \langle\Gamma_*,t\mid t\gamma t^{-1}=\alpha(\gamma),\ \gamma\in\Gamma_*\rangle.
\tag{39.19}
\]
We prove that the assignment
\[
 \gamma\longmapsto\gamma,
 \qquad
 t\longmapsto D
\tag{39.20}
\]
gives an injective homomorphism
\[
 G_*\hookrightarrow\mathrm{GL}_4(\mathbb Z[1/2]).
\tag{39.21}
\]

The relation is satisfied because \(D\gamma D^{-1}=\alpha(\gamma)\).  For injectivity, use the direct-limit description from Section 9.  Let
\[
 N_{\mathrm{abs}}=\varinjlim
 (\Gamma_*\xrightarrow{\alpha}\Gamma_*\xrightarrow{\alpha}\cdots).
\]
Represent a direct-limit element by \((\gamma,n)\) and define
\[
 j[(\gamma,n)]=D^{-n}\gamma D^n.
\tag{39.22}
\]
This is well defined because
\[
 D^{-(n+1)}\alpha(\gamma)D^{n+1}
 =D^{-n}\gamma D^n.
\]
It is injective.  If
\[
 D^{-n}\gamma D^n=D^{-m}\eta D^m
\]
and \(m\ge n\), then multiplying by \(D^m\) on the left and \(D^{-m}\) on the right gives
\[
 \eta=D^{m-n}\gamma D^{-(m-n)}=\alpha^{m-n}(\gamma),
\]
which is exactly the equivalence relation in the direct limit.

The ascending HNN extension is
\[
 G_*\cong N_{\mathrm{abs}}\rtimes\mathbb Z.
\]
The matrix \(D\) implements exactly the conjugation action of the stable letter on the embedded direct limit.  Indeed, the class \([(\gamma,n)]\) represents \(t^{-n}\gamma t^n\), and for \(n\ge1\)
\[
 D\,j[(\gamma,n)]\,D^{-1}
 =D^{-(n-1)}\gamma D^{n-1}
 =j[(\gamma,n-1)],
\]
which is the matrix image of
\(t(t^{-n}\gamma t^n)t^{-1}=t^{-(n-1)}\gamma t^{n-1}\).  For \(n=0\), the same compatibility is precisely
\(D\gamma D^{-1}=\alpha(\gamma)\), the defining HNN relation.  Thus \(j\) and \(1\mapsto D\) define the claimed semidirect-product homomorphism.

To prove that this homomorphism is injective, it remains only to see that no nonzero height disappears.  Every element of \(j(N_{\mathrm{abs}})\) has determinant \(\pm1\), since it is conjugate to an element of \(\Gamma_*\), while
\[
 \det D=8.
\]
If \(j(n)D^r=I\), determinants give
\[
 \pm 8^r=1,
\]
so \(r=0\), and then injectivity of \(j\) gives \(n=1\).  This proves (39.21).

Every entry of the image lies in \(\mathbb Z[1/2]\), as does every inverse, because the group is generated by integral matrices and \(D^{\pm1}\).

### 39.8 The HNN skeleton is residually finite, hence MF

Take a nonidentity \(g\in G_*\), viewed through (39.21).  Some entry of \(g-I\) is a nonzero dyadic rational
\[
 \frac{a}{2^r},
 \qquad a\in\mathbb Z\setminus\{0\}.
\]
Choose an odd prime \(p\nmid a\).  Since \(2\) is invertible in \(\mathbb F_p\), reduction modulo \(p\) defines a ring homomorphism
\[
 \mathbb Z[1/2]\longrightarrow\mathbb F_p
\]
and hence a group homomorphism
\[
 \mathrm{GL}_4(\mathbb Z[1/2])
 \longrightarrow
 \mathrm{GL}_4(\mathbb F_p).
\tag{39.23}
\]
The chosen entry remains nonzero, so \(g\) survives in the finite target.  Therefore
\[
 \boxed{G_*\text{ is residually finite}.}
\tag{39.24}
\]
In particular \(G_*\) is both sofic and MF.

This conclusion is stronger than what the abstract HNN soficity argument alone supplied: for the literal affine-doubling skeleton, the extra MF hypothesis in Theorem 37.7E is automatically satisfied.

### 39.9 Concrete sofic non-MF groups for every finite lamp

Let \(K\ne1\) be any finite group and let
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*.
\tag{39.25}
\]
Then all desired properties are now unconditional.

#### Theorem 39.9

For every nontrivial finite \(K\):

1. \(W_K\) is finitely generated;
2. \(W_K\) is sofic;
3. \(W_K\) is not MF;
4. its MF radical is exactly the kernel of the telescope pushforward
   \[
   \Phi_\infty:W_K\longrightarrow
   K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG_*.
   \tag{39.26}
   \]

#### Proof

The group \(\Gamma_*\) is finitely generated, and \(G_*\) is generated by \(\Gamma_*\cup\{t\}\).  The action \(G_*\curvearrowright G_*/\Gamma_*\) is transitive, so a finite generating set of the single lamp copy \(K_{\Gamma_*}\), together with generators of \(G_*\), generates all of \(W_K\).  Thus \(W_K\) is finitely generated.

By (39.14), the self-embedding has finite-index image.  Section 13 therefore proves that
\[
 G_*\curvearrowright G_*/\Gamma_*
\]
is a sofic action.  By (39.24), \(G_*\) is sofic; the finite group \(K\) is sofic.  The generalized-wreath theorem proved in Section 29 gives soficity of \(W_K\).

By (39.18) and properness of \(\alpha\), the torsion-compression theorem of Section 36 applies and supplies a nontrivial element of \(\operatorname{Rad}_{\mathrm{MF}}(W_K)\).  Hence \(W_K\) is not MF.

Finally (39.24) says that the HNN skeleton \(G_*\) is MF.  The exact telescope-radical theorem 37.7E therefore applies and gives precisely (39.26). ∎

### 39.10 Two explicit radical descriptions

For \(K=C_2\), the abelianization is again \(C_2\).  Under the height map
\[
 G_*/N\cong\mathbb Z,
\]
Theorem 39.9 says
\[
 \operatorname{Rad}_{\mathrm{MF}}(W_{C_2})
 =\left\{
 f\in C_2^{(G_*/\Gamma_*)}:
 \prod_{x\mapsto n}f(x)=1\text{ for every }n\in\mathbb Z
 \right\}.
\tag{39.27}
\]
In additive \(\mathbb F_2\)-notation: a finitely supported lamp configuration is MF-invisible exactly when it has **even parity in every height fiber**.

If \(K\) is finite perfect, then \(K_{\mathrm{ab}}=1\), so the quotient in (39.26) is simply \(G_*\).  Hence
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}(W_K)=K^{(G_*/\Gamma_*)}.
 }
\tag{39.28}
\]
Thus every lamp element is invisible to every norm-matrix-corona representation, while the HNN skeleton survives faithfully in the universal MF quotient.

This concrete family simultaneously realizes the main themes of the email: the ambient HNN group is not property \((T)\) (it surjects onto \(\mathbb Z\)), its coset action is amenable and sofic, the finite-lamp generalized wreath product is sofic but non-MF, and in fact its MF radical can be written down exactly.

### 39.11 Independent Wolfram check of the displayed matrix identities

As a second independent computation, the matrices in (39.1)--(39.4) were entered directly into a Wolfram kernel.  It verified all seven statements
\[
 DxD^{-1}=x,
\quad DyD^{-1}=y,
\quad DzD^{-1}=z,
\]
\[
 Dv_iD^{-1}=v_i^2\quad(i=1,2,3),
\qquad
 (D^{-1}v_1D)_{1,4}=\frac12,
\]
and returned the determinant list
\[
 (\det x,\det y,\det z,\det v_1,\det v_2,\det v_3,\det D)
 =(1,1,1,1,1,1,8).
\]
The Boolean output for the seven conjugation/half-entry tests was `True` in every coordinate.  Again, this is only a computational cross-check; Sections 39.2--39.4 prove the identities symbolically by block multiplication.

---

## 40. Exact comparison with Kun--Thom: the ambient property-\((T)\) hypothesis cannot simply be dropped

A fresh 2026 comparison makes the role of the ascending HNN skeleton especially transparent.  Kun and Thom's preprint **Nonsofic wreath products of residually finite groups** (arXiv:2608.06222, submitted 2026-08-06, <https://arxiv.org/abs/2608.06222>) gives a nonsoficity criterion for the mod-two generalized wreath product over \(G/\Gamma\).  Its hypotheses require: the semigroup of elements satisfying \(g\Gamma g^{-1}\le\Gamma\) to generate \(G\); property \((T)\) for both \(\Gamma\) and \(G\); and nonnormality of \(\Gamma\) in \(G\).

The concrete affine HNN pair of Section 39 satisfies every displayed structural condition **except** property \((T)\) of the ambient group \(G_*\), and its mod-two wreath product is sofic.  Thus the ambient-rigidity assumption is not a dispensable artifact of that theorem.

### Theorem 40.1

Let \((G_*,\Gamma_*)\) be the explicit affine-doubling HNN pair of Section 39.  Then:

1. \(\Gamma_*\) has property \((T)\);
2. both \(\Gamma_*\) and \(G_*\) are residually finite;
3. \(\Gamma_*\) is not normal in \(G_*\);
4. the set
   \[
   \mathcal C=
   \{g\in G_*:g\Gamma_*g^{-1}\le\Gamma_*\}
   \tag{40.1}
   \]
   generates \(G_*\);
5. \(G_*\) does **not** have property \((T)\);
6. nevertheless
   \[
   C_2^{(G_*/\Gamma_*)}\rtimes G_*
   \tag{40.2}
   \]
   is sofic (and, by Section 39, non-MF).

Consequently, if one deletes the hypothesis “\(G\) has property \((T)\)” from the Kun--Thom criterion while leaving the other displayed hypotheses unchanged, the resulting statement is false.

#### Proof

Items 1 and 2 are (39.18), (39.16), and (39.24).

For item 3,
\[
 t\Gamma_*t^{-1}=\alpha(\Gamma_*)<\Gamma_*.
\tag{40.3}
\]
If \(\Gamma_*\) were normal in \(G_*\), conjugation by \(t\) would satisfy
\[
 t\Gamma_*t^{-1}=\Gamma_*,
\]
contradicting the strict inclusion in (40.3).

For item 4, every \(\gamma\in\Gamma_*\) belongs to \(\mathcal C\), because
\[
 \gamma\Gamma_*\gamma^{-1}=\Gamma_*.
\]
Also \(t\in\mathcal C\) by (40.3).  Since the ascending HNN extension is generated by \(\Gamma_*\cup\{t\}\),
\[
 \langle\mathcal C\rangle=G_*.
\tag{40.4}
\]

For item 5, the height homomorphism
\[
 h:G_*\twoheadrightarrow\mathbb Z,
 \qquad
 h(\Gamma_*)=0,
 \quad h(t)=1,
\tag{40.5}
\]
is onto.  Property \((T)\) passes to quotients, while \(\mathbb Z\) does not have property \((T)\).  For completeness, here is a direct proof of the latter assertion.  Given any finite set \(F\subset\mathbb Z\) and \(\varepsilon>0\), choose \(m\) so large that
\[
 |e^{2\pi i n/m}-1|<\varepsilon
 \qquad(n\in F).
\]
The nontrivial one-dimensional unitary representation
\[
 \chi_m(n)=e^{2\pi i n/m}
\]
has a unit vector which is \(\varepsilon\)-fixed on \(F\), but it has no nonzero globally invariant vector because \(\chi_m\) is nontrivial.  Hence no finite Kazhdan pair exists for \(\mathbb Z\).  Therefore (40.5) rules out property \((T)\) for \(G_*\).

Finally, item 6 is Theorem 39.9 with \(K=C_2\).  This gives a sofic group satisfying all the remaining structural assumptions, so the Kun--Thom conclusion “nonsofic” cannot survive the deletion of ambient property \((T)\). ∎

### 40.2 Conceptual separation of the two mechanisms

This also clarifies the mathematical contrast in Francesco's message.

- **Kun--Thom nonsoficity** uses rigidity in both the stabilizer/base \(\Gamma\) and the ambient group \(G\).  Their explicit examples can therefore remain entirely inside the Kazhdan world.
- **The compression non-MF mechanism here** needs property \((T)\) only in the compressed subgroup \(\Gamma\).  The ambient HNN group may have a large amenable quotient; indeed \(G_*\twoheadrightarrow\mathbb Z\).
- That loss of ambient rigidity is not a defect for the present goal.  In the finite-index affine example it is compatible with a sofic coset action, so the generalized wreath product becomes **sofic but non-MF** rather than nonsofic.

Thus the ascending-HNN example is not merely a weaker version of the Kun--Thom construction.  It occupies a genuinely different approximation-theoretic regime and shows exactly where ambient property \((T)\) changes the outcome.

---

## 41. In the concrete family, the MF radical, finite-dimensional residual, and finite residual all coincide

The exact quotient from Section 39 is not only MF.  It is residually finite.  This identifies three natural approximation-theoretic radicals which need not coincide for a general group.

For a group \(H\), define the **finite residual**
\[
 \operatorname{Res}_{\mathrm{fin}}(H)
 =\bigcap_{F\text{ finite}}\ \bigcap_{\phi:H\to F}\ker\phi,
\tag{41.1}
\]
and the **finite-dimensional unitary residual**
\[
 \operatorname{Rad}_{\mathrm{fd}}(H)
 =\bigcap_{d\ge1}\ \bigcap_{\pi:H\to U(d)}\ker\pi.
\tag{41.2}
\]
Every finite quotient has a faithful finite-dimensional permutation representation, and every finite-dimensional unitary representation gives a constant-sequence matrix-corona representation.  Therefore, for every group,
\[
 \operatorname{Rad}_{\mathrm{MF}}(H)
 \le
 \operatorname{Rad}_{\mathrm{fd}}(H)
 \le
 \operatorname{Res}_{\mathrm{fin}}(H).
\tag{41.3}
\]

### 41.1 The universal quotient is residually finite

Let \(W_K\) be the concrete group (39.25), let \(A=K_{\mathrm{ab}}\), and let
\[
 P=A^{(\mathbb Z)}\rtimes_hG_*
\tag{41.4}
\]
be the quotient in (39.26).

#### Proposition 41.1

\(P\) is residually finite.

#### Proof

Section 39.8 proves that \(G_*\) is residually finite.  Lemma 37.7A proves that
\[
 L_A=A^{(\mathbb Z)}\rtimes\mathbb Z
\]
is residually finite.

A direct product of residually finite groups is residually finite: if \((g_1,g_2)\ne1\), one nontrivial coordinate survives in some finite quotient of its factor, and composing the coordinate projection with that finite quotient separates \((g_1,g_2)\).

Every subgroup of a residually finite group is residually finite: if \(h\ne1\) in a subgroup \(H\le Q\), a finite quotient of \(Q\) separating \(h\) restricts to a finite quotient map on \(H\) whose image still separates \(h\).

By (37.21),
\[
 P\hookrightarrow G_*\times L_A,
 \qquad
 (f,g)\longmapsto\bigl(g,(f,h(g))\bigr).
\]
The target is residually finite, hence so is \(P\). ∎

### 41.2 Equality of the three radicals

#### Theorem 41.2

For every nontrivial finite group \(K\),
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K)
 =\ker\Phi_\infty.
 }
\tag{41.5}
\]

#### Proof

Theorem 39.9 gives
\[
 \operatorname{Rad}_{\mathrm{MF}}(W_K)=\ker\Phi_\infty.
\tag{41.6}
\]
By (41.3),
\[
 \ker\Phi_\infty
 \le\operatorname{Rad}_{\mathrm{fd}}(W_K)
 \le\operatorname{Res}_{\mathrm{fin}}(W_K).
\tag{41.7}
\]
It remains to prove the reverse inclusion
\[
 \operatorname{Res}_{\mathrm{fin}}(W_K)\le\ker\Phi_\infty.
\]
Take \(w\notin\ker\Phi_\infty\).  Its image
\[
 \Phi_\infty(w)\ne1
\]
in \(P\).  By Proposition 41.1, some homomorphism
\[
 q:P\to F
\]
to a finite group satisfies
\[
 q(\Phi_\infty(w))\ne1.
\]
Thus the finite quotient map
\[
 q\Phi_\infty:W_K\to F
\]
separates \(w\), so \(w\notin\operatorname{Res}_{\mathrm{fin}}(W_K)\).  Hence
\[
 \operatorname{Res}_{\mathrm{fin}}(W_K)\le\ker\Phi_\infty.
\]
Together with (41.7), all inclusions are equalities. ∎

### 41.3 Consequences

For \(K=C_2\), the common radical is the even-parity-per-height subgroup from (39.27).  Thus a mod-two lamp configuration is killed by **every finite quotient** if and only if it has even parity in each telescope-height fiber.

For a finite perfect group \(K\), (39.28) and (41.5) give
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K)
 =K^{(G_*/\Gamma_*)}.
 }
\tag{41.8}
\]
So **every finite quotient and every finite-dimensional unitary representation kills the entire lamp subgroup**, while the quotient by that subgroup is the residually finite HNN skeleton \(G_*\).

This gives a precise algebraic description of the obstruction: in the concrete affine family, the failure of MF is not hiding beyond finite-dimensional representation theory.  The same explicitly described subgroup is invisible simultaneously to finite quotients, finite-dimensional unitary representations, and norm-matrix-corona representations.

---

## 42. Referee-strengthened universal quotient theorem

Section 41 identifies three kernels in the concrete affine family.  That equality has a stronger universal meaning which is worth stating explicitly.

Fix a nontrivial finite group \(K\), let
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*,
 \qquad
 A=K_{\mathrm{ab}},
\]
and let
\[
 \Phi_\infty:W_K\twoheadrightarrow
 P_K:=A^{(\mathbb Z)}\rtimes_hG_*
\tag{42.1}
\]
be the telescope quotient of Sections 37 and 39.  By Theorem 41.2,
\[
 R_K:=\ker\Phi_\infty
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K).
\tag{42.2}
\]
Moreover \(P_K\) is residually finite, hence MF.

### 42.1 Unique factorization of every corona representation

#### Theorem 42.1

Let \(\mathcal Q_{\mathbf d}\) be any norm matrix corona.  Precomposition with \(\Phi_\infty\) gives a bijection
\[
 \operatorname{Hom}\bigl(P_K,U(\mathcal Q_{\mathbf d})\bigr)
 \xrightarrow{\ \cong\ }
 \operatorname{Hom}\bigl(W_K,U(\mathcal Q_{\mathbf d})\bigr).
\tag{42.3}
\]
Equivalently, **every matrix-corona representation of \(W_K\) factors uniquely through \(P_K\)**.

#### Proof

Let
\[
 \Theta:W_K\to U(\mathcal Q_{\mathbf d})
\]
be a homomorphism.  By definition, \(\operatorname{Rad}_{\mathrm{MF}}(W_K)\) is contained in the kernel of every homomorphism from \(W_K\) to a norm matrix corona.  Equation (42.2) therefore gives
\[
 R_K\le\ker\Theta.
\]
The universal property of the quotient \(W_K/R_K\) produces a unique homomorphism
\[
 \overline\Theta:W_K/R_K\to U(\mathcal Q_{\mathbf d})
\]
with \(\Theta=\overline\Theta\circ q\), where \(q\) is the quotient map.  The first isomorphism theorem and (42.1)--(42.2) identify \(W_K/R_K\) with \(P_K\), yielding the required factorization through \(\Phi_\infty\).

Conversely, any homomorphism from \(P_K\) to the corona composes with \(\Phi_\infty\) to give a homomorphism from \(W_K\).  Surjectivity of \(\Phi_\infty\) makes the factorization unique.  Hence (42.3) is a bijection. ∎

This is stronger than saying merely that \(P_K\) is the universal MF quotient: it says the **entire representation functor into each individual norm matrix corona** is unchanged by passing from \(W_K\) to \(P_K\).

### 42.2 Unique factorization of finite-dimensional unitary representations

#### Theorem 42.2

For every \(d\ge1\), precomposition with \(\Phi_\infty\) gives a bijection
\[
 \operatorname{Hom}(P_K,U(d))
 \xrightarrow{\ \cong\ }
 \operatorname{Hom}(W_K,U(d)).
\tag{42.4}
\]

#### Proof

If \(\pi:W_K\to U(d)\), then by definition of the finite-dimensional residual,
\[
 \operatorname{Rad}_{\mathrm{fd}}(W_K)\le\ker\pi.
\]
Using (42.2), \(R_K\le\ker\pi\), so \(\pi\) factors uniquely through \(W_K/R_K\cong P_K\).  The converse and uniqueness follow exactly as in Theorem 42.1. ∎

Thus **finite-dimensional representation theory cannot distinguish \(W_K\) from the explicit quotient \(P_K\)** at the level of homomorphisms.

### 42.3 Unique factorization of finite quotients

#### Theorem 42.3

For every finite group \(F\), precomposition with \(\Phi_\infty\) gives a bijection
\[
 \operatorname{Hom}(P_K,F)
 \xrightarrow{\ \cong\ }
 \operatorname{Hom}(W_K,F).
\tag{42.5}
\]

#### Proof

Let \(q:W_K\to F\) be a homomorphism.  Since
\[
 R_K=\operatorname{Res}_{\mathrm{fin}}(W_K)
\]
is the intersection of the kernels of all homomorphisms from \(W_K\) to finite groups, \(R_K\le\ker q\).  Therefore \(q\) factors uniquely through \(W_K/R_K\cong P_K\).  Conversely every homomorphism \(P_K\to F\) pulls back along \(\Phi_\infty\), and surjectivity gives uniqueness. ∎

An immediate extension is useful.

#### Corollary 42.4

Every homomorphism from \(W_K\) to a residually finite group kills \(R_K\) and therefore factors uniquely through \(P_K\).

#### Proof

Let \(f:W_K\to R\) with \(R\) residually finite.  Suppose \(x\in R_K\) but \(f(x)\ne1\).  Residual finiteness gives a homomorphism \(\rho:R\to F\) to a finite group with \(\rho(f(x))\ne1\).  Then \(\rho f:W_K\to F\) is a finite quotient representation which does not kill \(x\), contradicting \(x\in\operatorname{Res}_{\mathrm{fin}}(W_K)\).  Hence \(R_K\le\ker f\), and quotient factorization follows. ∎

The corresponding MF statement is equally clean for countable MF targets.

#### Corollary 42.5

Every homomorphism from \(W_K\) to a countable MF group kills \(R_K\) and factors uniquely through \(P_K\).

#### Proof

Let \(f:W_K\to M\) and assume \(M\) is countable and MF.  Restrict an injective corona representation of \(M\) to the subgroup \(f(W_K)\).  The composite with \(f\) is a corona representation of \(W_K\), so it kills \(R_K=\operatorname{Rad}_{\mathrm{MF}}(W_K)\).  Injectivity on \(f(W_K)\) then implies \(f(R_K)=1\).  Factor through the quotient. ∎

So \(P_K\) is not merely one convenient MF quotient: among quotients detectable by these approximation theories, it is the canonical terminal information retained from \(W_K\).

### 42.4 The profinite completion is unchanged

Write \(\widehat H\) for the profinite completion of a group \(H\).

#### Theorem 42.6

The quotient map \(\Phi_\infty\) induces a canonical isomorphism
\[
 \boxed{\widehat{W_K}\cong\widehat{P_K}.}
\tag{42.6}
\]

#### Proof

It is enough to compare the directed systems of finite-index normal subgroups.  Because
\[
 R_K=\operatorname{Res}_{\mathrm{fin}}(W_K),
\]
every finite-index normal subgroup \(N\trianglelefteq W_K\) contains \(R_K\).  Hence
\[
 N\longmapsto N/R_K
\]
is a finite-index normal subgroup of \(W_K/R_K\cong P_K\).  Conversely, if \(M\trianglelefteq P_K\) has finite index, then \(\Phi_\infty^{-1}(M)\trianglelefteq W_K\) has finite index and contains \(R_K\).  These two operations are inverse, inclusion-preserving bijections, and for corresponding subgroups the quotient groups are canonically isomorphic:
\[
 W_K/N\cong P_K/(N/R_K).
\]
The transition maps between quotients are respected under these identifications.  The two inverse systems defining the profinite completions are therefore canonically isomorphic, and so are their inverse limits. ∎

No finite quotient can see the telescope kernel, and **there are no additional profinite relations beyond it**, because \(P_K\) itself is residually finite.

### 42.5 Intersection of all finite-index subgroups

For an arbitrary group \(H\), let
\[
 \operatorname{Core}_{\mathrm{fi}}(H)
 =\bigcap_{[H:L]<\infty}L
\tag{42.7}
\]
be the intersection of all finite-index subgroups, not assumed normal.

#### Lemma 42.7

For every group \(H\),
\[
 \operatorname{Core}_{\mathrm{fi}}(H)
 =\operatorname{Res}_{\mathrm{fin}}(H).
\tag{42.8}
\]

#### Proof

Every finite-index normal subgroup \(N\trianglelefteq H\) is itself a finite-index subgroup, so
\[
 \operatorname{Core}_{\mathrm{fi}}(H)
 \le \bigcap_{N\trianglelefteq H,\ [H:N]<\infty}N
 =\operatorname{Res}_{\mathrm{fin}}(H).
\]
For the reverse inclusion, let \(L\le H\) have finite index.  Its normal core
\[
 \operatorname{core}_H(L)=\bigcap_{h\in H}hLh^{-1}
\]
has finite index: the action of \(H\) on the finite coset set \(H/L\) gives a homomorphism to a finite symmetric group whose kernel is exactly \(\operatorname{core}_H(L)\).  Hence
\[
 \operatorname{Res}_{\mathrm{fin}}(H)
 \le\operatorname{core}_H(L)\le L.
\]
As this holds for every finite-index \(L\),
\[
 \operatorname{Res}_{\mathrm{fin}}(H)\le\operatorname{Core}_{\mathrm{fi}}(H).
\]
Thus equality holds. ∎

Combining Lemma 42.7 with (42.2),
\[
 \boxed{
 R_K
 =\bigcap_{[W_K:L]<\infty}L.
 }
\tag{42.9}
\]
So the telescope kernel is contained in **every finite-index subgroup** of \(W_K\), not just every finite-index normal subgroup.

---

## 43. Perfect lamps, mod-two lamps, and exact information loss

The universal factorization theorem becomes especially concrete at the two extremes already important in the project.

### 43.1 Perfect finite lamps

Assume \(K=[K,K]\).  Then \(K_{\mathrm{ab}}=1\), so
\[
 P_K=G_*.
\tag{43.1}
\]
Theorem 41.2 becomes
\[
 R_K=K^{(G_*/\Gamma_*)}.
\tag{43.2}
\]
Hence:

#### Theorem 43.1

If \(K\) is a nontrivial finite perfect group, then the quotient map
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*
 \twoheadrightarrow G_*
\tag{43.3}
\]
has the following simultaneous universal properties.

1. Every norm-matrix-corona representation of \(W_K\) kills the entire lamp subgroup and factors uniquely through \(G_*\).
2. Every finite-dimensional unitary representation of \(W_K\) kills the entire lamp subgroup and factors uniquely through \(G_*\).
3. Every homomorphism from \(W_K\) to a finite group kills the entire lamp subgroup and factors uniquely through \(G_*\).
4. Every homomorphism from \(W_K\) to a residually finite group kills the entire lamp subgroup.
5. Every homomorphism from \(W_K\) to a countable MF group kills the entire lamp subgroup.
6. The profinite completions are canonically isomorphic:
   \[
   \boxed{\widehat{W_K}\cong\widehat{G_*}.}
   \tag{43.4}
   \]
7. Every finite-index subgroup of \(W_K\) contains \(K^{(G_*/\Gamma_*)}\).

#### Proof

Equation (43.2) identifies the lamp subgroup with all three radicals in (42.2).  Items 1--5 are Theorems 42.1--42.3 and Corollaries 42.4--42.5 with \(P_K=G_*\).  Item 6 is Theorem 42.6.  Item 7 is (42.9). ∎

This is a particularly transparent form of approximation blindness: the lamps are an infinite normal subgroup which is **simultaneously invisible to every finite quotient, every finite-dimensional unitary representation, and every matrix-corona representation**.

### 43.2 Mod-two lamps

For \(K=C_2\), abelianization does nothing.  The radical is the parity-per-height kernel
\[
 R_{C_2}
 =\left\{f\in C_2^{(G_*/\Gamma_*)}:
   \prod_{x\mapsto n}f(x)=1
   \text{ for every }n\in\mathbb Z\right\}.
\tag{43.5}
\]
Thus the three approximation theories established at this stage---MF, finite-dimensional unitary, and finite-quotient---retain exactly one bit per occupied height and forget every even rearrangement inside a height fiber.  Section 46 proves that the all-fields linear and compact/Bohr theories have exactly the same kernel.

#### Corollary 43.2

For the concrete mod-two group, the following are equivalent for a finitely supported lamp configuration \(f\).

1. \(f\) dies in every norm-matrix-corona representation.
2. \(f\) dies in every finite-dimensional unitary representation.
3. \(f\) dies in every finite quotient.
4. \(f\) belongs to every finite-index subgroup of \(W_{C_2}\).
5. Every height fiber contains an even number of lit lamps.

#### Proof

The equivalence of 1--4 follows from (42.2), (42.9), and the equality of the three radicals.  Section 39.10 identifies that common kernel with the parity condition in 5. ∎

### 43.3 The groups are finitely generated, with an explicit bound

The construction does not hide infinite generation in the lamp subgroup.

#### Proposition 43.3

Suppose \(\Gamma\) is generated by \(r\) elements and \(K\) by \(q\) elements.  Then
\[
 K^{(G/\Gamma)}\rtimes G
\]
is generated by at most
\[
 r+1+q
\tag{43.6}
\]
elements.

#### Proof

The ascending HNN group \(G\) is generated by the \(r\) chosen generators of \(\Gamma\) together with the stable letter \(t\).  Fix the base site \(x_0=\Gamma\in G/\Gamma\), and let \(k_1,\dots,k_q\) generate the lamp copy \(K_{x_0}\).

Because the action of \(G\) on \(G/\Gamma\) is transitive, for every site \(x=g\Gamma\), conjugation by \(g\) sends \(K_{x_0}\) onto \(K_x\).  Thus the subgroup generated by \(G\) and \(K_{x_0}\) contains every single-site lamp copy \(K_x\).  The restricted direct sum \(K^{(G/\Gamma)}\) is generated by those single-site copies.  Hence the \(r+1+q\) displayed generators generate the full semidirect product. ∎

For the concrete affine base, the displayed generating set has six base generators.  Therefore
\[
 d(W_K)\le7+d(K),
\tag{43.7}
\]
where \(d(K)\) denotes the minimum number of generators of \(K\).  In particular the concrete \(C_2\) example is generated by **eight explicit elements**: six affine base generators, the stable letter, and one root lamp.

### 43.4 Explicit non-residual-finiteness

The exact finite residual gives a direct algebraic witness that the sofic groups constructed here are not residually finite.

#### Proposition 43.4

For every nontrivial finite \(K\), the group \(W_K\) has nontrivial finite residual and hence is not residually finite.

#### Proof

Choose distinct sites \(x,y\in G_*/\Gamma_*\) in the same height fiber; such sites exist because the self-embedding is proper, so already the first telescope fiber has at least two points.

If \(K_{\mathrm{ab}}\ne1\), choose \(k\in K\) with nontrivial image \(\bar k\in K_{\mathrm{ab}}\).  Then
\[
 u=k_xk_y^{-1}
\]
is nontrivial in the restricted direct sum because its two coordinates are nontrivial and supported at different sites, while its abelianized total on that height fiber is \(\bar k\bar k^{-1}=1\).  Hence \(u\in R_K\setminus\{1\}\).

If \(K_{\mathrm{ab}}=1\), then \(K\) is perfect and (43.2) gives
\[
 R_K=K^{(G_*/\Gamma_*)}\ne1.
\]
Thus in all cases
\[
 \operatorname{Res}_{\mathrm{fin}}(W_K)=R_K\ne1.
\]
A residually finite group has trivial finite residual, so \(W_K\) is not residually finite. ∎

---

## 44. Formal-proof synchronization and exact status boundary

The strongest version of a research dossier is one whose prose and formal status agree.  This section records that boundary explicitly.

### 44.1 What formal proof source is present in the current repository snapshot

At the audited `main` head
\[
\texttt{7df16bbaa925c55a95b39996e9938b3b91311ac1},
\]
the repository contains the following proof chain for the involutive collapse:

- `ExactInvolutionLifts.lean`: exact commuting involution correction;
- `InvolutionOrbitMicrostates.lean`: diagonal extraction of corrected orbit microstates;
- `InvolutionCollapseMetric.lean` and `InvolutionCollapseProfile.lean`: rank metric, word bounds, normalized profile, and the exact generator-mass anchor;
- `InvolutionCollapseCocycle.lean`: rank/operator/Frobenius control of the cocycle defect;
- Kazhdan ultralimit/approximate-circumcenter modules: boundedness and an approximate primitive;
- `InvolutionCollapseIndexCapture.lean` and `ScaledKazhdanTransport.lean`: one-stage Kazhdan corner capture and one-sided compression transport;
- `InvolutionCollapseEndpoint.lean`: `actualCoronaMFInvisible_commutator`, `actualCoronaMFInvisible_of_involutiveWitness`, radical containment, and exact radical reduction when the quotient is MF;
- `ProjectionCompressionCollapse.lean`: projection collapse;
- `TorsionSpectralCollapse.lean`: Fourier reduction from finite-order witnesses to spectral projections.

The concrete property-\((T)\) input has a similarly closed source chain:

- `LiteralP13HodgeCertificate.lean` defines the exact rational certificate `cleanP13Certificate`, proves `p13_hodge_gap` and `p13_generatorLaplacian_quadratic_gap`, and exposes the premise-free theorem `p13_hasKazhdanPropertyT`;
- `LiteralBaseP13PropertyTBridge.lean` transfers this through the checked P13-to-rotation quotient and affine bridge and exposes the premise-free theorem `manuscriptBaseHasKazhdanPropertyT`;
- `CommutingLampCollapse.lean` pushes that theorem through the concrete affine quotient to `gammaBar_hasKazhdanPropertyT`.

A static source scan of both the collapse chain and these property-\((T)\) bridge/certificate files found **no `sorry` and no declared `axiom`**.  `Endpoint/Audit.lean` also contains `#print axioms` audit commands for the public P13 certificate and the literal-base property-\((T)\) theorem; this session confirms those audit commands are present but, without a Lean executable, does not claim to have observed their kernel output.  In particular, the decisive collapse and property-\((T)\) endpoints are not merely theorem names wrapping unproved analytic hypotheses: their source dependencies discharge the conclusions.

### 44.2 What this audit does not claim

The GitHub API returned neither a combined CI status nor a workflow run for the audited head.  The local ZIP does not include a configured Lean toolchain cache, and this environment has no `lean`/`lake` executable available.  Therefore the correct verification statement is:

> **The repository contains an assumption-free Lean proof chain at source level, and the exact endpoint declarations are present; this audit did not independently rerun the Lean kernel or observe a hosted CI pass.**

This distinction is deliberately stronger scientifically than writing “verified” without saying what was actually checked.

### 44.3 Proof-status taxonomy for this dossier

The main claims now fall into four clean classes.

| Class | Meaning | Principal examples |
|---|---|---|
| **F** | formal source proof present in the audited Lean repository | involutive collapse; projection/torsion collapse endpoints; exact P13/property-\((T)\) certificate chain; explicit affine self-embedding/properness; concrete non-MF endpoints |
| **P** | complete paper-level proof given in this dossier | metric bridge; HNN normal form; explicit Følner sets; finite-index action soficity; telescope radical; exact residual/profinite factorization; all-fields linear residual and nonlinearity |
| **R** | published primary-source theorem, with the needed argument reconstructed here or explicitly identified | GKEP generalized-wreath soficity; Gao LERF action soficity; Monod--Popa co-amenability context |
| **O** | genuinely open in the generality stated | arbitrary residually finite/sofic base plus arbitrary infinite-index self-embedding implies the HNN coset action is sofic |

No theorem in Classes F, P, or R should be presented as depending on the Class O frontier.

---

## 45. Final strengthened theorem package

All of the preceding work can be compressed into the following theorem without losing the important distinctions.

### Theorem 45.1 (explicit finitely generated sofic non-MF groups with completely computed approximation kernel)

There exists an explicit finitely generated residually finite group \(G_*\), an explicit property-\((T)\) subgroup \(\Gamma_*<G_*\), and a proper finite-index self-embedding of \(\Gamma_*\) implemented by the stable letter of an ascending HNN decomposition, with the following property.

For every nontrivial finite group \(K\), the generalized permutational wreath product
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*
\tag{45.1}
\]
satisfies:

1. \(W_K\) is finitely generated; indeed \(d(W_K)\le7+d(K)\).
2. The action \(G_*\curvearrowright G_*/\Gamma_*\) is amenable and sofic.
3. \(W_K\) is sofic.
4. \(W_K\) is not MF.
5. If \(A=K_{\mathrm{ab}}\) and \(h:G_*\twoheadrightarrow\mathbb Z\) is the HNN height map, then the explicit map
   \[
   \Phi_\infty:W_K\twoheadrightarrow A^{(\mathbb Z)}\rtimes_hG_*
   \]
   has kernel
   \[
   \boxed{
   \ker\Phi_\infty
   =\operatorname{Rad}_{\mathrm{MF}}(W_K)
   =\operatorname{Rad}_{\mathrm{fd}}(W_K)
   =\operatorname{Res}_{\mathrm{fin}}(W_K).
   }
   \tag{45.2}
   \]
6. The target of \(\Phi_\infty\) is residually finite and MF.
7. Every norm-matrix-corona representation, every finite-dimensional unitary representation, every finite quotient, every homomorphism to a residually finite group, and every homomorphism to a countable MF group kills \(\ker\Phi_\infty\) and factors uniquely through \(\Phi_\infty\) whenever uniqueness is meaningful for the specified target.
8. The quotient map induces
   \[
   \widehat{W_K}\cong
   \widehat{A^{(\mathbb Z)}\rtimes_hG_*}.
   \tag{45.3}
   \]
9. The common kernel (45.2) is the intersection of all finite-index subgroups of \(W_K\).
10. If \(K\) is perfect, then the common kernel is the entire lamp subgroup and the universal quotient in all the senses above is simply \(G_*\).
11. If \(K=C_2\), then the common kernel consists exactly of the finitely supported configurations having even parity in every HNN-height fiber.

#### Proof

The explicit affine base, proper index-eight self-embedding, property \((T)\), and residual finiteness of \(G_*\) are proved in Section 39.  Finite generation is Proposition 43.3.  Amenability of the coset action is Section 10, and finite-index action soficity is Theorem 13.5; generalized-wreath soficity is Theorem 29.6.  Non-MF-ness follows from the torsion compression collapse at the moved site, Sections 34 and 36.  The telescope iteration and exact MF radical are Theorems 37.5 and 37.7E.  Residual finiteness of the target and equality with the finite-dimensional and finite residuals are Proposition 41.1 and Theorem 41.2.  Universal factorization, profinite completion, and the finite-index intersection are Theorems 42.1--42.6 and Lemma 42.7.  The perfect-lamp and mod-two descriptions are Section 43. ∎

### 45.2 The exact conceptual answer to the original email

The cleanest final picture is now:

\[
\boxed{
\begin{array}{c}
\text{one-sided compression of a Kazhdan subgroup}\\[2mm]
+\ \text{finite-order commuting-orbit lamp witness}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{fixed MF-radical defects}\\
\text{(no distinguished mover needed)}
\end{array}}
\tag{45.4}
\]

and, in the finite-index affine HNN example,

\[
\boxed{
\begin{array}{c}
\text{finite-index telescope}\\
+\ \text{residually finite linear skeleton}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{sofic action and sofic wreath product}\\
\text{with an exactly computable nontrivial radical.}
\end{array}}
\tag{45.5}
\]

The three matrix metrics are no longer mysterious in this organization:

- operator norm enforces the group relations and covariance;
- rank records the discrete disagreement support that survives normalization;
- Frobenius/Hilbert--Schmidt norm converts that support into Hilbert energy for property \((T)\).

The HNN extension is not a technical afterthought either.  It supplies, simultaneously, the one-sided compressor that creates the MF obstruction, the height quotient that organizes the iterated radical, and—when the self-embedding has finite index—the finite-orbit telescope that supplies sofic action models.

This was the strongest endpoint before adding the all-fields linear and compact/Bohr layers.  Sections 46--48 continue the same exact-kernel computation and give the final strengthened package.


---

## 46. A fourth residual: all linear representations, plus nonlinearity

The equality in (45.2) can be strengthened beyond complex unitary representations.  The point is that the image of a finitely generated group under **any** finite-dimensional linear representation is again finitely generated, and every finitely generated linear group is residually finite.  We include the algebraic proof so that the conclusion does not rest on an unexpanded citation to Mal'cev's theorem.

### 46.1 Finite residue fields separate nonzero elements

#### Lemma 46.1

Let \(R\) be a finitely generated integral domain and let \(0\ne r\in R\).  Then there exist a finite field \(k\) and a ring homomorphism
\[
 \theta:R\longrightarrow k
\]
such that \(\theta(r)\ne0\).

#### Proof

Localize at the powers of \(r\):
\[
 R_r=R[1/r].
\]
This is a nonzero finitely generated ring.  Choose a maximal ideal \(\mathfrak m'\lhd R_r\), and put
\[
 k=R_r/\mathfrak m'.
\]
Then \(k\) is a field finitely generated as a ring.  We claim that every field finitely generated as a ring is finite.

If \(\operatorname{char}k=p>0\), then \(k\) is a finitely generated \(\mathbb F_p\)-algebra which is a field.  By Zariski's lemma it is a finite algebraic extension of \(\mathbb F_p\), hence a finite field.

Suppose instead that \(\operatorname{char}k=0\).  Write
\[
 k=\mathbb Z[a_1,\dots,a_m].
\]
After adjoining rational scalars, \(k\) is a finitely generated \(\mathbb Q\)-algebra which is a field, so Zariski's lemma makes \(k/\mathbb Q\) a finite algebraic extension.  Choose a nonzero integer \(N\) clearing the denominators of monic equations for the finitely many algebraic generators \(a_i\).  Then every \(a_i\) is integral over \(\mathbb Z[1/N]\), and therefore every element of the ring \(\mathbb Z[a_1,\dots,a_m]=k\) is integral over \(\mathbb Z[1/N]\).  Choose a prime \(p\nmid N\).  Since \(k\) is a field of characteristic zero, \(1/p\in k\).  We now verify directly that \(1/p\) is **not** integral over \(\mathbb Z[1/N]\).  If it satisfied a monic equation
\[
 (1/p)^m+c_{m-1}(1/p)^{m-1}+\cdots+c_0=0,
 \qquad c_i\in\mathbb Z[1/N],
\]
choose \(M\) so that every \(N^M c_i\) is an integer and multiply by \(p^mN^M\).  The resulting integer equation has first term \(N^M\), while every remaining term is divisible by \(p\).  Reducing modulo \(p\) gives
\[
 N^M\equiv0\pmod p,
\]
contradicting \(p\nmid N\).  Hence \(1/p\) is not integral over \(\mathbb Z[1/N]\).  This contradiction excludes characteristic zero.  Thus \(k\) is finite.

Let \(\mathfrak m=\mathfrak m'\cap R\).  Because \(r\) is a unit in \(R_r\), it cannot lie in \(\mathfrak m'\), so \(r\notin\mathfrak m\).  The composite
\[
 R\longrightarrow R_r\longrightarrow k
\]
therefore sends \(r\) to a nonzero element of the finite field \(k\). ∎

### 46.2 Finitely generated linear groups are residually finite

#### Theorem 46.2 (Mal'cev's residual-finiteness theorem, proved here)

Let \(F\) be any field and let
\[
 H\le \mathrm{GL}_d(F)
\]
be finitely generated.  Then \(H\) is residually finite.

#### Proof

Choose a finite symmetric generating set \(S\) of \(H\).  Let \(R\subseteq F\) be the subring generated by all matrix entries of all matrices in \(S\).  Because \(S\) is symmetric, the entries of the inverses of the chosen generators are already included; hence every word in \(S\) lies in \(\mathrm{GL}_d(R)\).  The ring \(R\) is a finitely generated integral domain.

Take \(1\ne h\in H\).  Some matrix entry \(r\) of \(h-I\) is nonzero.  By Lemma 46.1 there is a finite field \(k\) and a homomorphism
\[
 \theta:R\to k
\]
with \(\theta(r)\ne0\).  Applying \(\theta\) entrywise gives a group homomorphism
\[
 \theta_*:H\longrightarrow \mathrm{GL}_d(k).
\]
Every matrix in \(H\) remains invertible after applying \(\theta\): if \(uv=I\) in \(M_d(R)\), then \(\theta(u)\theta(v)=I\).  The target \(\mathrm{GL}_d(k)\) is finite, while the chosen entry shows
\[
 \theta_*(h)\ne I.
\]
Thus every nonidentity element of \(H\) survives in a finite quotient, and \(H\) is residually finite. ∎

### 46.3 The all-fields linear residual is exactly the telescope kernel

For a group \(W\), define its **linear residual** by the elementwise condition
\[
 \operatorname{Rad}_{\mathrm{lin}}(W)
 =\{w\in W:\rho(w)=1\text{ for every field }F,
      \ d\ge1,\ \rho:W\to\mathrm{GL}_d(F)\}.
\tag{46.1}
\]
Equivalently one may write the usual intersection-of-kernels notation; the elementwise formulation avoids any irrelevant set-theoretic issue about indexing over a proper class of fields.

#### Theorem 46.3

For every nontrivial finite \(K\) in the concrete family,
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{lin}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\ker\Phi_\infty.
 }
\tag{46.2}
\]
Moreover every finite-dimensional linear representation of \(W_K\), over every field, factors uniquely through
\[
 P_K=K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG_*.
\]

#### Proof

Put \(R_K=\ker\Phi_\infty\).  By Theorem 41.2,
\[
 R_K=\operatorname{Res}_{\mathrm{fin}}(W_K).
\tag{46.3}
\]
Let
\[
 \rho:W_K\to\mathrm{GL}_d(F)
\]
be any linear representation.  Since \(W_K\) is finitely generated, its image \(\rho(W_K)\) is a finitely generated linear group.  Theorem 46.2 makes \(\rho(W_K)\) residually finite.  If \(x\in R_K\) and \(\rho(x)\ne1\), residual finiteness of the image would provide a finite quotient
\[
 \rho(W_K)\to Q
\]
which does not kill \(\rho(x)\).  Composing with \(\rho\) would give a finite quotient of \(W_K\) not killing \(x\), contradicting (46.3).  Hence
\[
 R_K\le\ker\rho
\]
for every \(F,d,\rho\), so
\[
 R_K\le\operatorname{Rad}_{\mathrm{lin}}(W_K).
\tag{46.4}
\]

Conversely, every finite quotient
\[
 q:W_K\to Q
\]
has a faithful finite-dimensional complex linear realization via the left regular representation
\[
 \lambda_Q:Q\hookrightarrow\mathrm{GL}_{|Q|}(\mathbb C).
\]
Therefore any element killed by every finite-dimensional linear representation is killed by every finite quotient:
\[
 \operatorname{Rad}_{\mathrm{lin}}(W_K)
 \le \operatorname{Res}_{\mathrm{fin}}(W_K)=R_K.
\tag{46.5}
\]
Combining (46.4) and (46.5) gives
\[
 \operatorname{Rad}_{\mathrm{lin}}(W_K)=R_K.
\]
The remaining equalities are Theorem 41.2.

Finally, \(R_K\le\ker\rho\) is precisely the criterion for \(\rho\) to descend through the quotient \(W_K/R_K\cong P_K\); surjectivity of \(\Phi_\infty\) makes the descended representation unique. ∎

#### Corollary 46.4 (explicit sofic groups that are nonlinear over every field)

For every nontrivial finite \(K\), the group \(W_K\) is not isomorphic to a subgroup of \(\mathrm{GL}_d(F)\) for any field \(F\) and any finite \(d\).

#### Proof

Proposition 43.4 gives \(R_K\ne1\).  A faithful finite-dimensional linear representation would have trivial kernel, contradicting Theorem 46.3. ∎

### 46.4 The groups are not even virtually linear

We record the finite-extension argument as well.

#### Lemma 46.5

Let \(G\) be finitely generated.  If \(G\) has a finite-index residually finite subgroup, then \(G\) is residually finite.

#### Proof

Let \(H\le G\) be finite index and residually finite.  Replacing \(H\) by its core
\[
 C=\bigcap_{g\in G}gHg^{-1},
\]
we may assume \(C\trianglelefteq G\); it is still finite index, finitely generated, and residually finite.

Take \(1\ne x\in G\).  If \(x\notin C\), the finite quotient \(G/C\) separates \(x\).  Suppose \(x\in C\).  Since \(C\) is residually finite, choose a finite-index normal subgroup \(L\trianglelefteq C\) with \(x\notin L\).  Let \(m=[C:L]\).  A finitely generated group has only finitely many subgroups of any fixed finite index: a subgroup of index \(m\) determines a transitive homomorphism to \(\operatorname{Sym}(m)\), and there are only finitely many homomorphisms from a fixed finite generating set to this finite group.  Hence the intersection
\[
 D=\bigcap\{M\le C:[C:M]\le m\}
\]
is finite index in \(C\).  It is characteristic in \(C\), and \(D\le L\), so \(x\notin D\).  Because \(C\trianglelefteq G\) and \(D\) is characteristic in \(C\), we have \(D\trianglelefteq G\).  The finite quotient \(G/D\) therefore separates \(x\).  Thus \(G\) is residually finite. ∎

#### Corollary 46.6

For every nontrivial finite \(K\), \(W_K\) is **not virtually linear over any field**.

#### Proof

If a finite-index subgroup \(H\le W_K\) were linear, then \(H\) would be finitely generated by Schreier's lemma and residually finite by Theorem 46.2.  Lemma 46.5 would then make \(W_K\) residually finite, contradicting Proposition 43.4. ∎

### 46.5 Compact targets and the Bohr kernel

There is one further classical consequence.  Define
\[
 \operatorname{Rad}_{\mathrm{Bohr}}(W)
 =\{w\in W:f(w)=1\text{ for every homomorphism }f:W\to C
     \text{ with }C\text{ compact Hausdorff}\}.
\]
(The discrete topology on \(W\) makes every such homomorphism continuous.)  Peter--Weyl says that finite-dimensional continuous unitary representations separate the points of every compact Hausdorff group.  Since a homomorphism from a discrete group to \(U(d)\) is a homomorphism to a compact group, Peter--Weyl gives
\[
 \operatorname{Rad}_{\mathrm{Bohr}}(W)
 =\operatorname{Rad}_{\mathrm{fd}}(W).
\tag{46.6}
\]
This is the one place in this section where we deliberately use a named classical theorem rather than reproving its full harmonic-analysis proof.

#### Corollary 46.7

For the concrete groups \(W_K\),
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{Bohr}}(W_K)
 =\ker\Phi_\infty.
 }
\tag{46.7}
\]
Every homomorphism from \(W_K\) to a compact group factors uniquely through \(P_K\), and the quotient map induces an isomorphism of Bohr compactifications
\[
 bW_K\cong bP_K.
\tag{46.8}
\]
In particular \(W_K\) is not maximally almost periodic.

#### Proof

Equation (46.7) is (46.6) together with Theorem 41.2.  Hence every compact-target homomorphism kills \(R_K=\ker\Phi_\infty\), so it factors uniquely through \(P_K\).  Conversely every compact-target homomorphism of \(P_K\) pulls back along \(\Phi_\infty\).  Thus precomposition with \(\Phi_\infty\) gives the same compact-target homomorphism functor for \(W_K\) and \(P_K\).  By the universal property of the Bohr compactification their Bohr compactifications are canonically isomorphic.  Finally \(R_K\ne1\) by Proposition 43.4, so the canonical map \(W_K\to bW_K\) is not injective. ∎

For a perfect finite lamp group \(K\), all of (46.2) and (46.7) equal the full lamp subgroup.  Thus the entire lamp kernel is invisible simultaneously to matrix coronas, finite quotients, finite-dimensional unitary representations, finite-dimensional linear representations over every field, and compact-group representations.

---

## 47. Consolidated strengthened endpoint

A consolidated compact statement supported by all of the preceding audits is the following.

### Theorem 47.1 (explicit sofic non-MF groups with one kernel governing five approximation theories)

For every nontrivial finite group \(K\), there is an explicit finitely generated construction
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*
\]
(with \(d(W_K)\le7+d(K)\), hence eight generators when \(K=C_2\)) such that:

1. \(G_*\) is explicit, finitely generated, residually finite, linear over \(\mathbb Z[1/2]\), and surjects onto \(\mathbb Z\); \(\Gamma_*<G_*\) is explicit, residually finite, has property \((T)\), and is compressed by an index-eight proper self-embedding.
2. The action \(G_*\curvearrowright G_*/\Gamma_*\) is amenable and sofic.
3. \(W_K\) is finitely generated and sofic but is not MF and is not residually finite.
4. With \(A=K_{\mathrm{ab}}\) and
   \[
   P_K=A^{(\mathbb Z)}\rtimes_hG_*,
   \]
   the canonical telescope map \(\Phi_\infty:W_K\twoheadrightarrow P_K\) has nontrivial kernel \(R_K\) satisfying
   \[
   \boxed{
   R_K
   =\operatorname{Rad}_{\mathrm{MF}}(W_K)
   =\operatorname{Rad}_{\mathrm{fd}}(W_K)
   =\operatorname{Rad}_{\mathrm{lin}}(W_K)
   =\operatorname{Rad}_{\mathrm{Bohr}}(W_K)
   =\operatorname{Res}_{\mathrm{fin}}(W_K).
   }
   \tag{47.1}
   \]
5. Every homomorphism from \(W_K\) to any of the following targets kills exactly the forced kernel \(R_K\) and therefore factors uniquely through \(P_K\):
   - a norm matrix corona unitary group;
   - a finite-dimensional complex unitary group;
   - \(\mathrm{GL}_d(F)\) for any field \(F\);
   - a finite group;
   - a residually finite group;
   - a countable MF group;
   - a compact Hausdorff group.
   Here “exactly” means that \(R_K\) is the intersection of the kernels over the indicated class; an individual homomorphism may of course have a larger kernel.
6. The profinite and Bohr compactifications are unchanged by the quotient:
   \[
   \widehat{W_K}\cong\widehat{P_K},
   \qquad
   bW_K\cong bP_K.
   \tag{47.2}
   \]
7. \(R_K\) is the intersection of all finite-index subgroups of \(W_K\).
8. \(W_K\) is not linear and not virtually linear over any field.
9. If \(K\) is perfect, then
   \[
   R_K=K^{(G_*/\Gamma_*)},
   \qquad
   P_K=G_*;
   \]
   every approximation theory listed above completely forgets the lamp subgroup.
10. If \(K=C_2\), then \(R_K\) is exactly the subgroup of finitely supported configurations having even parity in every HNN-height fiber.

#### Proof

Items 1--4 combine Sections 39, 41, 43, and 46.  The action statements in item 2 are Sections 10 and 13.  Soficity is Theorem 29.6; non-MF-ness and the exact MF radical are Sections 36--37.  The factorization statements in item 5 are Sections 42 and 46.  The profinite completion is Theorem 42.6 and the Bohr completion is Corollary 46.7.  Item 7 is Lemma 42.7 together with (42.2).  Item 8 is Corollaries 46.4 and 46.6.  The final two cases are Sections 43.1--43.2. ∎

### 47.2 What “fully proved” means in this file

No mathematical dossier can literally reprove all of mathematics from set theory upward.  The standard here is therefore explicit and reproducible:

- every new implication specific to this project is proved in the text;
- every delicate approximation step is either proved in the text or matched to a premise-free formal-source endpoint;
- imported deep classical facts are named at the exact point of use (for example Zariski's lemma and Peter--Weyl), rather than being hidden inside phrases such as “standard”; 
- primary-source theorems are separated from new deductions;
- formal-source evidence is separated from hosted-CI/kernel-rerun claims;
- the one remaining general action-soficity question is labelled open instead of being used as a premise.

Under that standard, Theorem 47.1 is the consolidated exact-kernel package, and Section 48 is its strongest present structural consequence: finite targets, finite-index subgroups, finite actions, and profinite completion all factor through the same quotient, with an explicit perfect-lamp pair exhibiting opposite MF behavior.

---

## 48. Finite-target rigidity and explicit profinite twins with opposite MF behavior

The exact-kernel theorem has one more consequence which is stronger than the bare isomorphism of profinite completions.  The quotient does not merely preserve finite quotients: it preserves the **entire finite-index subgroup lattice** and the **entire category of finite actions**.  In the perfect-lamp case this produces an explicit finitely generated pair with identical finite data but opposite MF behavior.

Throughout, keep the concrete group
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*,
 \qquad
 P_K=K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG_*,
\]
and the quotient
\[
 q=\Phi_\infty:W_K\twoheadrightarrow P_K,
 \qquad
 R_K=\ker q.
\]
By Theorems 41.2 and 46.3,
\[
 R_K=\operatorname{Res}_{\mathrm{fin}}(W_K)
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Rad}_{\mathrm{lin}}(W_K)
 =\operatorname{Rad}_{\mathrm{Bohr}}(W_K),
\tag{48.1}
\]
and \(P_K\) is residually finite.

### 48.1 The finite-index subgroup lattice is exactly preserved

#### Theorem 48.1

The maps
\[
 \mathcal L_{\mathrm{fi}}(P_K)
 \longrightarrow
 \mathcal L_{\mathrm{fi}}(W_K),
 \qquad
 M\longmapsto q^{-1}(M),
\tag{48.2}
\]
and
\[
 \mathcal L_{\mathrm{fi}}(W_K)
 \longrightarrow
 \mathcal L_{\mathrm{fi}}(P_K),
 \qquad
 L\longmapsto q(L)=L/R_K
\tag{48.3}
\]
are mutually inverse inclusion-preserving bijections between finite-index subgroups.  They preserve index and normality:
\[
 [W_K:L]=[P_K:q(L)],
\tag{48.4}
\]
and
\[
 L\trianglelefteq W_K
 \quad\Longleftrightarrow\quad
 q(L)\trianglelefteq P_K.
\tag{48.5}
\]

#### Proof

By (42.9), every finite-index subgroup \(L\le W_K\) contains \(R_K\).  Hence the correspondence theorem for the quotient \(q:W_K\to W_K/R_K\cong P_K\) applies to **every** finite-index subgroup of \(W_K\), not merely to the normal ones.  It gives
\[
 q^{-1}(q(L))=L
\]
and, for every subgroup \(M\le P_K\),
\[
 q(q^{-1}(M))=M.
\]
Thus (48.2)--(48.3) are inverse and preserve inclusions.

The quotient map induces a bijection of left-coset sets
\[
 W_K/L\longrightarrow P_K/q(L),
 \qquad
 wL\longmapsto q(w)q(L).
\]
It is well defined because \(R_K\le L\), injective by the same containment, and surjective because \(q\) is surjective.  This proves (48.4).  Normality is preserved by the standard quotient correspondence, giving (48.5). ∎

This is strictly more information than (42.6): the profinite completion remembers only the inverse system of finite-index **normal** subgroups, while Theorem 48.1 identifies every finite-index subgroup.

### 48.2 Every finite action factors uniquely through the telescope quotient

Let \(\mathbf{FinAct}(H)\) denote the category of finite sets equipped with an \(H\)-action, with equivariant maps as morphisms.

#### Theorem 48.2

Inflation along \(q\) gives an equivalence
\[
 q^*:\mathbf{FinAct}(P_K)\simeq \mathbf{FinAct}(W_K).
\tag{48.6}
\]
More concretely, every action of \(W_K\) on a finite set has \(R_K\) acting trivially and therefore factors **uniquely** through \(P_K\); a map between two such finite actions is \(W_K\)-equivariant if and only if it is \(P_K\)-equivariant for the descended actions.

#### Proof

Let \(\Omega\) be finite and let
\[
 \rho:W_K\to\operatorname{Sym}(\Omega)
\]
be the permutation homomorphism of a \(W_K\)-action.  The target is finite, so Theorem 42.3 gives
\[
 R_K\le\ker\rho.
\]
Therefore there is a unique
\[
 \bar\rho:P_K\to\operatorname{Sym}(\Omega)
\]
with \(\rho=\bar\rho q\).  This proves essential surjectivity at the level of action structures, in fact on the same underlying finite set.

Now let \(\Omega,\Lambda\) be two descended actions and let
\[
 f:\Omega\to\Lambda.
\]
If \(f\) is \(P_K\)-equivariant then it is plainly \(W_K\)-equivariant after precomposition with \(q\).  Conversely, suppose it is \(W_K\)-equivariant.  Given \(p\in P_K\), choose \(w\in W_K\) with \(q(w)=p\).  Then
\[
 f(p\cdot x)
 =f(w\cdot x)
 =w\cdot f(x)
 =p\cdot f(x).
\]
Hence \(f\) is \(P_K\)-equivariant.  Thus inflation is fully faithful as well. ∎

#### Corollary 48.3

The quotient \(q\) preserves, bijectively:

1. finite transitive actions up to isomorphism;
2. conjugacy classes of finite-index subgroups;
3. finite permutation representations of each degree;
4. finite quotient actions with any prescribed finite underlying set.

#### Proof

Transitive finite actions are exactly coset actions by finite-index subgroups.  Theorem 48.2 preserves transitivity because it does not change the underlying orbit relation: \(q(W_K)=P_K\).  The remaining statements follow from Theorems 48.1--48.2. ∎

### 48.3 Subgroup growth is identical

Because \(W_K\) is finitely generated, so is its quotient \(P_K\).  A finitely generated group has only finitely many subgroups of any prescribed finite index, as proved inside Lemma 46.5.

For \(H\) finitely generated write
\[
 a_n(H)=\#\{L\le H:[H:L]=n\},
 \qquad
 a_n^{\triangleleft}(H)
 =\#\{L\trianglelefteq H:[H:L]=n\}.
\]

#### Corollary 48.4

For every \(n\ge1\),
\[
 \boxed{
 a_n(W_K)=a_n(P_K),
 \qquad
 a_n^{\triangleleft}(W_K)=a_n^{\triangleleft}(P_K).
 }
\tag{48.7}
\]
Consequently every subgroup-growth invariant determined by these sequences is identical for \(W_K\) and \(P_K\); in particular their subgroup zeta functions agree wherever the corresponding Dirichlet series is considered.

#### Proof

Theorem 48.1 is an index-preserving bijection of all finite-index subgroups and preserves normality. ∎

### 48.4 The whole profinite topology is pulled back from the quotient

Give a group its profinite topology, whose neighborhoods of the identity are the finite-index normal subgroups.

#### Proposition 48.5

The profinite topology on \(W_K\) is exactly the inverse-image topology under
\[
 q:W_K\to P_K.
\]
Its identity closure is
\[
 \overline{\{1\}}^{\mathrm{prof}}=R_K.
\tag{48.8}
\]
The quotient \(P_K=W_K/R_K\) is therefore the Hausdorff reflection of \(W_K\) for the profinite topology, and completion gives again
\[
 \widehat{W_K}\cong\widehat{P_K}.
\tag{48.9}
\]

#### Proof

By Theorem 48.1, every finite-index normal subgroup of \(W_K\) is uniquely of the form \(q^{-1}(M)\) for a finite-index normal subgroup \(M\trianglelefteq P_K\).  These subgroups form neighborhood bases at the identity on the two sides, proving the inverse-image assertion.

The closure of the identity in any group with its profinite topology is the intersection of all finite-index normal subgroups, namely the finite residual.  By (48.1) this is \(R_K\), proving (48.8).  Since \(P_K\) is residually finite, its profinite topology is Hausdorff, so quotienting by exactly the closure of the identity gives the Hausdorff reflection.  The completion statement is Theorem 42.6, now seen at the level of the entire topology. ∎

### 48.5 Perfect lamps give an MF/profinite twin pair

Now suppose \(K\) is nontrivial and perfect.  Then
\[
 K_{\mathrm{ab}}=1,
 \qquad
 P_K=G_*,
 \qquad
 R_K=K^{(G_*/\Gamma_*)}.
\tag{48.10}
\]

#### Theorem 48.6 (explicit profinite twins with opposite MF behavior)

For every nontrivial finite perfect group \(K\), the pair
\[
 \boxed{
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_* ,
 \qquad
 G_*
 }
\tag{48.11}
\]
has all of the following properties.

1. Both groups are finitely generated and sofic.
2. \(G_*\) is residually finite and MF.
3. \(W_K\) is neither residually finite nor MF.
4. The quotient \(W_K\twoheadrightarrow G_*\) induces an isomorphism
   \[
   \widehat{W_K}\cong\widehat{G_*}.
   \tag{48.12}
   \]
5. It induces an inclusion- and index-preserving bijection
   \[
   \{L\le W_K:[W_K:L]<\infty\}
   \longleftrightarrow
   \{M\le G_*:[G_*:M]<\infty\}.
   \tag{48.13}
   \]
   Explicitly,
   \[
   M\longmapsto K^{(G_*/\Gamma_*)}\rtimes M.
   \tag{48.14}
   \]
6. The categories of finite actions are equivalent:
   \[
   \mathbf{FinAct}(W_K)\simeq\mathbf{FinAct}(G_*).
   \tag{48.15}
   \]
7. For every field \(F\) and every \(d\ge1\), precomposition with the quotient gives a bijection
   \[
   \operatorname{Hom}(G_*,\mathrm{GL}_d(F))
   \xrightarrow{\ \cong\ }
   \operatorname{Hom}(W_K,\mathrm{GL}_d(F)).
   \tag{48.16}
   \]
   The same holds with \(\mathrm{GL}_d(F)\) replaced by \(U(d)\), any norm matrix corona unitary group, any finite group, any residually finite target, any countable MF target, or any compact Hausdorff group.
8. The Bohr compactifications are canonically isomorphic:
   \[
   bW_K\cong bG_*.
   \tag{48.17}
   \]
9. Every finite-index subgroup of \(W_K\) contains the **entire** lamp subgroup.

#### Proof

Items 1--3 are Sections 39, 43, and 46.  Equation (48.10) specializes Theorems 42.6, 48.1, and 48.2 to \(P_K=G_*\), proving items 4--6 and 9.  Formula (48.14) is simply the inverse image of \(M\le G_*\) under the semidirect-product projection.

For item 7, Theorem 46.3 gives the all-fields linear statement; Theorems 42.1--42.5 and Corollary 46.7 give the remaining target classes.  Item 8 is (46.8) with \(P_K=G_*\). ∎

Taking, for example, \(K=A_5\) makes (48.11) completely explicit: \(A_5\) is finite, nonabelian simple, hence perfect because its commutator subgroup is a nontrivial normal subgroup.

#### Corollary 48.7 (MF is not determined by profinite completion)

Among finitely generated groups, without requiring both members of the pair to be residually finite, the MF property is **not determined by the isomorphism type of the profinite completion**.

#### Proof

For a nontrivial finite perfect \(K\), Theorem 48.6 gives
\[
 \widehat{W_K}\cong\widehat{G_*},
\]
while \(G_*\) is MF and \(W_K\) is not MF. ∎

The qualification about residual finiteness is essential: every residually finite group in this countable setting is MF by Lemma 37.7B, so no pair of residually finite groups can witness opposite MF behavior in this way.

### 48.6 The finite-dimensional representation categories agree as well

The targetwise bijections can be upgraded from objects to intertwiners.

#### Proposition 48.8

Fix a field \(F\).  Precomposition with \(q\) gives an equivalence between the categories of finite-dimensional \(F\)-linear representations of \(P_K\) and \(W_K\).  For \(F=\mathbb C\), the same statement holds for finite-dimensional unitary representations.

#### Proof

Theorem 46.3 gives a unique descended representation for every finite-dimensional \(W_K\)-representation.  Thus precomposition is bijective on objects once a vector space is fixed.

Suppose
\[
 \rho_i=\bar\rho_i q
 \qquad(i=1,2)
\]
are two such representations and \(T\) is a linear map between their representation spaces.  Then
\[
 T\rho_1(w)=\rho_2(w)T
 \qquad(w\in W_K)
\]
if and only if
\[
 T\bar\rho_1(p)=\bar\rho_2(p)T
 \qquad(p\in P_K),
\]
because every \(p\in P_K\) is \(q(w)\) for some \(w\).  Hence the intertwiner spaces are identical.  The unitary case is the same argument. ∎

For perfect \(K\), this says that \(W_K\) and the MF group \(G_*\) have the same finite-dimensional representation theory in this precise categorical sense, even though one admits a faithful norm-corona representation and the other does not.  The difference is not in which finite-dimensional representations exist; it is in the nontrivial subgroup of \(W_K\) that **all** of them, and indeed all compact and finite targets, necessarily forget.

### 48.7 Final conceptual compression

The construction now separates three levels of information with unusual sharpness:

\[
\boxed{
\begin{array}{c}
W_K\\[1mm]
\downarrow\;\text{kill }R_K\\[1mm]
P_K
\end{array}
\qquad
R_K=
\operatorname{Rad}_{\mathrm{MF}}
=\operatorname{Rad}_{\mathrm{fd}}
=\operatorname{Rad}_{\mathrm{lin}}
=\operatorname{Rad}_{\mathrm{Bohr}}
=\operatorname{Res}_{\mathrm{fin}}.
}
\tag{48.18}
\]

- **Finite/compact/linear information:** all of it already factors through \(P_K\).
- **Profinite information:** even the full finite-index subgroup lattice and finite-action category are unchanged by passing to \(P_K\).
- **MF faithfulness:** nevertheless \(W_K\) is not MF because the common invisible kernel \(R_K\) is nontrivial, while the explicit quotient \(P_K\) is residually finite and MF.

For perfect lamps, \(P_K=G_*\).  Thus the same concrete HNN skeleton is simultaneously the maximal residually finite quotient, the universal MF quotient, the universal finite-dimensional-linear quotient in the representation-functor sense, and the compact/Bohr-visible quotient of a finitely generated sofic non-MF group.

---

## 49. Finite-index induction: the approximation radical survives every finite-index passage

The previous sections compute the approximation kernels of the concrete groups themselves.  There is a stronger general fact which is useful well beyond this example: the MF radical, the finite-dimensional residual, and the all-fields linear residual are **exactly inherited by finite-index subgroups**.  This is the missing mechanism needed to decide whether passing to finite index can repair the approximation failure.

### 49.1 Inducing a corona representation from a finite-index subgroup

Let \(H\le G\) have finite index \(m\), and let
\[
 \Theta:H\longrightarrow U(\mathcal Q_{\mathbf d})
\tag{49.1}
\]
be a homomorphism to a norm matrix corona.  Choose left-coset representatives
\[
 r_1=1,r_2,\ldots,r_m,
 \qquad
 G=\bigsqcup_{i=1}^m r_iH.
\]
For \(g\in G\) and \(i\in\{1,\ldots,m\}\), there are unique
\[
 \sigma_g(i)\in\{1,\ldots,m\},
 \qquad
 h_{g,i}\in H
\]
such that
\[
 g r_i=r_{\sigma_g(i)}h_{g,i}.
\tag{49.2}
\]
Then \(\sigma_g\) is a permutation and the cocycle identity is
\[
 h_{g_1g_2,i}
 =h_{g_1,\sigma_{g_2}(i)}h_{g_2,i}.
\tag{49.3}
\]

The fixed matrix amplification of a norm matrix corona is again a norm matrix corona:
\[
 M_m(\mathcal Q_{\mathbf d})
 \cong
 \frac{\prod_nM_m(M_{d_n}(\mathbb C))}
      {\bigoplus_nM_m(M_{d_n}(\mathbb C))}
 \cong
 \mathcal Q_{(m d_n)}.
\tag{49.4}
\]
The first isomorphism follows because, for fixed \(m\), a sequence of
\(m\times m\) block matrices tends to zero in operator norm exactly when each
of its finitely many block-entry sequences tends to zero.

Define \(\operatorname{Ind}_H^G\Theta(g)\in U(M_m(\mathcal Q_{\mathbf d}))\) to be the block-monomial matrix which sends the \(i\)-th block to the \(\sigma_g(i)\)-th block by the unitary \(\Theta(h_{g,i})\).  Equivalently its only nonzero block in column \(i\) is
\[
 \bigl(\operatorname{Ind}_H^G\Theta(g)\bigr)_{\sigma_g(i),i}
 =\Theta(h_{g,i}).
\tag{49.5}
\]

#### Lemma 49.1

The map
\[
 \operatorname{Ind}_H^G\Theta:
 G\longrightarrow U(\mathcal Q_{(m d_n)})
\tag{49.6}
\]
is a homomorphism.  Moreover, for every \(h\in H\), the \((1,1)\)-block of
\(\operatorname{Ind}_H^G\Theta(h)\) is exactly \(\Theta(h)\).

#### Proof

Every block-monomial matrix in (49.5) is unitary because every row and column contains exactly one unitary block.  For multiplication, the block starting in column \(i\) under \(g_2\) lands in row \(\sigma_{g_2}(i)\), and the subsequent \(g_1\)-block contributes
\[
 \Theta(h_{g_1,\sigma_{g_2}(i)})\Theta(h_{g_2,i})
 =\Theta(h_{g_1g_2,i})
\]
by (49.3).  The final row is
\(\sigma_{g_1}(\sigma_{g_2}(i))=\sigma_{g_1g_2}(i)\).  Thus the product is exactly the block-monomial matrix for \(g_1g_2\).

If \(h\in H\), then
\[
 h r_1=h=r_1h,
\]
so \(\sigma_h(1)=1\) and \(h_{h,1}=h\).  Formula (49.5) therefore gives the claimed \((1,1)\)-block. ∎

### 49.2 Exact finite-index heredity of the MF radical

#### Theorem 49.2

For every finite-index subgroup \(H\le G\),
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}(H)
 =H\cap\operatorname{Rad}_{\mathrm{MF}}(G).
 }
\tag{49.7}
\]

#### Proof

If \(x\in\operatorname{Rad}_{\mathrm{MF}}(H)\), then every corona representation of \(G\), restricted to \(H\), kills \(x\).  Hence
\[
 \operatorname{Rad}_{\mathrm{MF}}(H)
 \le H\cap\operatorname{Rad}_{\mathrm{MF}}(G).
\]

Conversely, let
\[
 x\in H\cap\operatorname{Rad}_{\mathrm{MF}}(G)
\]
and let \(\Theta:H\to U(\mathcal Q_{\mathbf d})\) be arbitrary.  By Lemma 49.1, \(\Theta\) induces a corona representation
\[
 \widetilde\Theta=
 \operatorname{Ind}_H^G\Theta:G\to U(\mathcal Q_{(m d_n)}).
\]
Since \(x\in\operatorname{Rad}_{\mathrm{MF}}(G)\),
\[
 \widetilde\Theta(x)=1.
\]
Taking the \((1,1)\)-block and using Lemma 49.1 gives
\[
 \Theta(x)=1.
\]
Because \(\Theta\) was arbitrary, \(x\in\operatorname{Rad}_{\mathrm{MF}}(H)\). ∎

#### Corollary 49.2A (MF is invariant under finite-index commensurability)

If \(H\le G\) has finite index, then
\[
 H\text{ is MF}\quad\Longleftrightarrow\quad G\text{ is MF}.
\tag{49.7A}
\]
Consequently the MF property is invariant under abstract commensurability.

#### Proof

If \(G\) is MF, every subgroup is MF by restriction of a faithful corona representation.

Conversely, suppose \(H\) is MF and let
\[
 \Theta:H\hookrightarrow U(\mathcal Q_{\mathbf d})
\]
be injective.  We claim the induced representation from Lemma 49.1 is injective on \(G\).  If \(1\ne g\in H\), its \((1,1)\)-block is \(\Theta(g)\ne1\).  If \(g\notin H\), then
\[
 g r_1H=gH\ne H=r_1H,
\]
so \(\sigma_g(1)\ne1\); the induced block-monomial matrix moves the first block and therefore is not the identity.  Thus \(\operatorname{Ind}_H^G\Theta\) is faithful and \(G\) is MF.

If two groups are abstractly commensurable, they have isomorphic finite-index subgroups, so applying the equivalence in both groups proves commensurability invariance. ∎

The same phenomenon holds for the other classical approximation properties used later.

#### Corollary 49.2B

For a finite-index inclusion \(H\le G\):

1. \(H\) is residually finite if and only if \(G\) is residually finite;
2. for every field \(F\), \(H\) is linear over \(F\) if and only if \(G\) is linear over \(F\);
3. \(H\) is MAP if and only if \(G\) is MAP.

Hence residual finiteness, linearity over a specified field, linearity over some field, and MAP are all abstract-commensurability invariants.

#### Proof

Subgroups inherit all three properties, so only finite extensions require proof.

For residual finiteness, assume \(H\) is residually finite and let
\[
 C=\bigcap_{g\in G}gHg^{-1}\trianglelefteq G
\]
be the finite-index core.  Then \(C\le H\) is residually finite.  Let \(1\ne x\in G\).  If \(x\notin C\), the finite quotient \(G/C\) separates it.  If \(x\in C\), choose a finite-index normal subgroup \(L\trianglelefteq C\) with \(x\notin L\).  Since \(L\trianglelefteq C\) and \(C\trianglelefteq G\), the conjugates \(gLg^{-1}\) depend only on the finitely many cosets \(gC\).  Hence
\[
 D=\bigcap_{g\in G}gLg^{-1}
\]
is a finite-index normal subgroup of \(G\).  It is contained in \(L\), so \(x\notin D\), and \(G/D\) separates \(x\).

For linearity, let \(\rho:H\hookrightarrow\mathrm{GL}_d(F)\) be faithful.  The block-monomial induction used in Lemma 49.1, now over \(F\), gives
\[
 \operatorname{Ind}_H^G\rho:G\to\mathrm{GL}_{md}(F).
\]
The same distinguished-block argument used in Corollary 49.2A proves it is faithful.

For MAP, take again the finite-index normal core \(C\).  If \(x\notin C\), the finite permutation representation on \(G/C\) separates \(x\).  If \(1\ne x\in C\), the subgroup \(C\le H\) is MAP, so some finite-dimensional unitary representation \(\rho:C\to U(d)\) satisfies \(\rho(x)\ne1\).  Inducing \(\rho\) from \(C\) to \(G\) gives a finite-dimensional unitary representation whose distinguished block is \(\rho(x)\), so it separates \(x\).  Thus finite-dimensional unitary representations separate all points of \(G\). ∎

The same induction is purely algebraic and therefore works for finite-dimensional representations over every field.

#### Corollary 49.3

If \(H\le G\) has finite index, then
\[
 \operatorname{Rad}_{\mathrm{fd}}(H)
 =H\cap\operatorname{Rad}_{\mathrm{fd}}(G),
\tag{49.8}
\]
and
\[
 \operatorname{Rad}_{\mathrm{lin}}(H)
 =H\cap\operatorname{Rad}_{\mathrm{lin}}(G).
\tag{49.9}
\]
Here \(\operatorname{Rad}_{\mathrm{lin}}\) is the intersection of the kernels of all finite-dimensional linear representations over all fields, as in Section 46.

#### Proof

For a representation \(\rho:H\to U(d)\), the same block-monomial construction gives the usual finite-dimensional induced unitary representation
\[
 \operatorname{Ind}_H^G\rho:G\to U(md),
\]
with \(\rho(h)\) as the \((1,1)\)-block for \(h\in H\).  The proof of (49.8) is therefore word-for-word the proof of Theorem 49.2.

For \(\rho:H\to\mathrm{GL}_d(F)\), with \(F\) an arbitrary field, replace unitary blocks by invertible blocks.  The resulting block-monomial matrices lie in \(\mathrm{GL}_{md}(F)\), and the same proof gives (49.9). ∎

The finite residual has the same finite-index heredity.

#### Lemma 49.4

For \(H\le G\) of finite index,
\[
 \operatorname{Res}_{\mathrm{fin}}(H)
 =H\cap\operatorname{Res}_{\mathrm{fin}}(G).
\tag{49.10}
\]

#### Proof

The inclusion from left to right follows by restricting every finite quotient of \(G\) to \(H\).

For the reverse inclusion, let
\[
 x\in H\cap\operatorname{Res}_{\mathrm{fin}}(G)
\]
and suppose \(\phi:H\to F\) is a homomorphism to a finite group with \(\phi(x)\ne1\).  Put \(L=\ker\phi\).  Then \(L\) has finite index in \(H\), hence also in \(G\).  Its core
\[
 C=\bigcap_{g\in G}gLg^{-1}
\tag{49.11}
\]
is the intersection of only finitely many distinct conjugates, because a finite-index subgroup has only finitely many conjugates.  Thus \(C\trianglelefteq G\) has finite index.  Since \(C\le L\) and \(x\notin L\), we have \(x\notin C\).  The finite quotient \(G/C\) therefore separates \(x\), contradicting
\(x\in\operatorname{Res}_{\mathrm{fin}}(G)\).  Hence every finite quotient of \(H\) kills \(x\), proving (49.10). ∎

By Section 46.5 the Bohr kernel equals the finite-dimensional unitary residual, so (49.8) also gives
\[
 \operatorname{Rad}_{\mathrm{Bohr}}(H)
 =H\cap\operatorname{Rad}_{\mathrm{Bohr}}(G).
\tag{49.12}
\]

### 49.3 No finite-index subgroup repairs the concrete examples

Return to the concrete groups
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*,
 \qquad K\ne1\text{ finite},
\]
and write
\[
 R_K=\ker\Phi_\infty.
\]
Theorems 41.2, 46.3, and 46.7 give
\[
 R_K
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Rad}_{\mathrm{lin}}(W_K)
 =\operatorname{Rad}_{\mathrm{Bohr}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K).
\tag{49.13}
\]
Lemma 42.7 says that \(R_K\) is also the intersection of **all** finite-index subgroups of \(W_K\), not only the normal ones.

#### Theorem 49.5 (finite-index hereditary approximation failure)

Let \(H\le W_K\) have finite index.  Then
\[
 \boxed{
 \operatorname{Rad}_{\mathrm{MF}}(H)
 =\operatorname{Rad}_{\mathrm{fd}}(H)
 =\operatorname{Rad}_{\mathrm{lin}}(H)
 =\operatorname{Rad}_{\mathrm{Bohr}}(H)
 =\operatorname{Res}_{\mathrm{fin}}(H)
 =R_K.
 }
\tag{49.14}
\]
In particular, every finite-index subgroup of \(W_K\) is **sofic but non-MF**, and no such subgroup is residually finite, linear over any field, or maximally almost periodic.

#### Proof

Because \(R_K\) is the intersection of all finite-index subgroups of \(W_K\),
\[
 R_K\le H.
\tag{49.15}
\]
Apply Theorem 49.2, Corollary 49.3, Lemma 49.4, and (49.12) to the finite-index inclusion \(H\le W_K\).  In every case the residual of \(H\) is
\[
 H\cap R_K=R_K.
\]
This proves (49.14).

The subgroup \(R_K\) is nontrivial: Section 39 exhibits a nontrivial two-site lamp defect in it.  Therefore \(H\) has nontrivial MF radical and is not MF; it has nontrivial finite residual and is not residually finite; it has nontrivial all-fields linear residual and is not linear over any field; and it has nontrivial Bohr kernel and is not maximally almost periodic.  Finally, soficity passes to subgroups: a finite sofic test for a subgroup is already a finite sofic test in the ambient group, so one simply restricts the ambient approximation.  Since \(W_K\) is sofic, \(H\) is sofic. ∎

Thus the pathology is not a finite-index artifact.  It survives **every** passage to finite index with the *same explicit kernel*.

#### Corollary 49.6 (no commensurability with an MF group)

No \(W_K\) is abstractly commensurable with an MF group.  More strongly, it is not abstractly commensurable with any residually finite group, any group linear over a field, or any MAP group.

Since \(P_K\) is residually finite and MF while Theorem 42.6 gives
\[
 \widehat{W_K}\cong\widehat{P_K},
\tag{49.16}
\]
this produces, for every nontrivial finite \(K\), a pair of finitely generated groups with isomorphic profinite completions which are **not abstractly commensurable**.

For perfect \(K\), \(P_K=G_*\).  Thus although \(W_K\) and \(G_*\) have isomorphic profinite completions and isomorphic finite-index subgroup lattices with preserved indices, **no finite-index subgroup of \(W_K\) is isomorphic to any subgroup of \(G_*\)**.

#### Proof

Suppose \(W_K\) were abstractly commensurable with a group \(M\) having one of the listed properties.  Then some finite-index subgroup \(H\le W_K\) would be isomorphic to a finite-index subgroup \(J\le M\).  Each listed property passes to subgroups: MF by restriction of a faithful corona representation; residual finiteness by restriction of finite quotients; linearity by restriction of a faithful linear representation; and MAP because any separating family of finite-dimensional unitary representations restricts to a separating family on a subgroup.  Hence \(H\) would have that property, contradicting Theorem 49.5.

If \(K\) is perfect, every subgroup of the MF group \(G_*\) is MF.  Theorem 49.5 says every finite-index subgroup of \(W_K\) is non-MF.  Therefore none can be isomorphic to a subgroup of \(G_*\). ∎

---

## 50. Functoriality: the telescope kernel is fully invariant and every homomorphism descends

The equality with the finite residual makes the telescope kernel intrinsic in a stronger sense than characteristicity.

### 50.1 The finite residual is functorial under arbitrary homomorphisms

#### Lemma 50.1

For every group homomorphism \(f:G\to H\),
\[
 f\bigl(\operatorname{Res}_{\mathrm{fin}}(G)\bigr)
 \le
 \operatorname{Res}_{\mathrm{fin}}(H).
\tag{50.1}
\]

#### Proof

Let \(x\in\operatorname{Res}_{\mathrm{fin}}(G)\), and let
\(q:H\to F\) be any homomorphism to a finite group.  Then
\[
 qf:G\to F
\]
is a finite-target homomorphism, so by definition of the finite residual,
\[
 q(f(x))=(qf)(x)=1.
\]
This holds for every finite-target homomorphism \(q\), hence
\(f(x)\in\operatorname{Res}_{\mathrm{fin}}(H)\). ∎

In particular, the finite residual is **fully invariant**: every endomorphism sends it into itself.

The proof did not use finiteness except to specify the target class.  More generally, if \(\mathcal C\) is any class of target groups and
\[
 \operatorname{Rad}_{\mathcal C}(G)
 =\bigcap_{C\in\mathcal C}\ \bigcap_{\phi:G\to C}\ker\phi,
\tag{50.2}
\]
then every homomorphism \(f:G\to H\) satisfies
\[
 f(\operatorname{Rad}_{\mathcal C}(G))
 \le \operatorname{Rad}_{\mathcal C}(H),
\tag{50.3}
\]
because any map \(H\to C\) can be precomposed with \(f\).  Thus the MF radical, finite-dimensional unitary residual, all-fields linear residual, and Bohr kernel are themselves functorial and fully invariant for **every** group.  In the concrete family they happen to coincide with the finite residual.

### 50.2 Canonical descent in the concrete family

#### Theorem 50.2

For finite nontrivial lamp groups \(K,L\), every homomorphism
\[
 f:W_K\longrightarrow W_L
\]
satisfies
\[
 f(R_K)\le R_L.
\tag{50.4}
\]
Consequently there is a unique induced homomorphism
\[
 \bar f:P_K=W_K/R_K
 \longrightarrow
 P_L=W_L/R_L
\tag{50.5}
\]
such that
\[
 \bar f\,\Phi_{\infty,K}
 =\Phi_{\infty,L}f.
\tag{50.6}
\]

#### Proof

By (49.13), \(R_K=\operatorname{Res}_{\mathrm{fin}}(W_K)\) and
\(R_L=\operatorname{Res}_{\mathrm{fin}}(W_L)\).  Equation (50.4) is therefore Lemma 50.1.  Since \(\Phi_{\infty,L}\) kills \(R_L\), the composite
\(\Phi_{\infty,L}f\) kills \(R_K\), so the universal property of the quotient gives the unique map \(\bar f\). ∎

#### Corollary 50.3

For every \(K\), \(R_K\) is fully invariant, hence characteristic, in \(W_K\).  Every endomorphism of \(W_K\) descends uniquely to an endomorphism of \(P_K\), and every automorphism descends to an automorphism of \(P_K\).

#### Proof

Apply Theorem 50.2 with \(K=L\).  If \(f\) is an automorphism, apply the same construction to \(f^{-1}\).  The descended maps are inverse because their composites agree with the identity after precomposition with the surjective quotient map. ∎

For a perfect finite lamp \(K\), Section 43 gives
\[
 R_K=K^{(G_*/\Gamma_*)}.
\tag{50.7}
\]
Hence the entire lamp subgroup is not merely normal: it is **fully invariant**.  No endomorphism of the abstract group can move any lamp information out of the invisible kernel.

---

## 51. A single invisible torsion relation generates the entire radical for simple lamps

The perfect-lamp case can be sharpened dramatically when the finite lamp is nonabelian simple.

Let \(S\) be a finite nonabelian simple group, put
\[
 X=G_*/\Gamma_*,
 \qquad
 L_S=S^{(X)},
 \qquad
 W_S=L_S\rtimes G_*.
\tag{51.1}
\]
Since \(S\) is nonabelian simple, its commutator subgroup is a nontrivial normal subgroup, hence
\[
 S_{\mathrm{ab}}=1.
\]
Thus Section 43 gives
\[
 R_S=L_S.
\tag{51.2}
\]

Fix a site \(x_0\in X\) and a nonidentity element \(s\in S\).  Let
\[
 r=\delta_{x_0}(s)\in L_S
\tag{51.3}
\]
be the lamp configuration supported at \(x_0\) with value \(s\).

### 51.1 One element normally generates the whole invisible kernel

#### Theorem 51.1

\[
 \boxed{
 R_S=L_S=\langle\!\langle r\rangle\!\rangle_{W_S}.
 }
\tag{51.4}
\]

#### Proof

Let
\[
 N=\langle\!\langle r\rangle\!\rangle_{W_S}.
\]
Because \(L_S\trianglelefteq W_S\) and \(r\in L_S\), we have
\[
 N\le L_S.
\tag{51.5}
\]

Inside the site subgroup \(S_{x_0}\cong S\), the normal closure of \(s\) is a nontrivial normal subgroup of the simple group \(S\); therefore it is all of \(S\).  Since conjugation by elements of \(S_{x_0}\) is also conjugation inside \(W_S\),
\[
 S_{x_0}\le N.
\tag{51.6}
\]

The action of \(G_*\) on \(X=G_*/\Gamma_*\) is transitive.  Hence for every \(x\in X\) there exists \(g\in G_*\) with \(gx_0=x\), and
\[
 gS_{x_0}g^{-1}=S_x.
\]
Normality of \(N\) and (51.6) give \(S_x\le N\) for every site.  The restricted direct sum \(L_S\) is generated by the site subgroups \(S_x\), so
\[
 L_S\le N.
\]
Together with (51.5), this proves \(N=L_S=R_S\). ∎

#### Corollary 51.1A

The radical \(R_S\) is not finitely generated as an abstract group, even though it is normally generated in \(W_S\) by the single element \(r\).

#### Proof

The cosets
\[
 t^n\Gamma_*\qquad(n\ge0)
\]
are pairwise distinct in \(G_*/\Gamma_*\): if \(t^n\Gamma_*=t^m\Gamma_*\), then \(t^{m-n}\in\Gamma_*\), but the height homomorphism is zero on \(\Gamma_*\) and takes \(t^{m-n}\) to \(m-n\), so \(m=n\).  Hence \(X\) is infinite.

A finite subset of the restricted direct sum \(S^{(X)}\) is supported on only finitely many sites, and the subgroup it generates remains supported on their finite union.  It therefore cannot equal \(S^{(X)}\).  Thus \(R_S=L_S\) is not finitely generated.  Theorem 51.1 proves that it is nevertheless singly normally generated in the ambient group. ∎

### 51.2 A split quotient obtained by adding one relation

The permutational wreath product is a semidirect product, so the quotient
\[
 q_S:W_S=L_S\rtimes G_*\twoheadrightarrow G_*
\tag{51.7}
\]
has the canonical section \(g\mapsto(1,g)\).  Combining (51.4) with (51.7) yields:

#### Corollary 51.2 (single invisible relation)

For every nonidentity \(r\) as in (51.3),
\[
 \boxed{
 W_S/\langle\!\langle r\rangle\!\rangle
 \cong G_*.
 }
\tag{51.8}
\]
The quotient map is split and induces:

- an isomorphism of profinite completions;
- an inclusion- and index-preserving bijection of all finite-index subgroups;
- an equivalence of finite-action categories;
- an isomorphism of Bohr compactifications;
- bijections on homomorphisms into every finite group, residually finite group, finite-dimensional linear group over any field, finite-dimensional unitary group, countable MF group, compact Hausdorff group, and every norm matrix corona unitary group.

#### Proof

Equation (51.8) is Theorem 51.1 and the first isomorphism theorem.  All listed consequences are exactly Theorems 42.1--42.6, Corollary 46.7, and Theorem 48.1 specialized to the perfect-lamp identity \(P_S=G_*\). ∎

Thus **adding one nontrivial torsion relation changes MF behavior but changes none of the finite/compact/finite-dimensional/corona target functors treated above**: every such target already forces that relation.  Equivalently, profinite completion sends the noninjective split epimorphism \(q_S\) to an isomorphism.  The same is true of Bohr compactification.

### 51.3 An invisible involution

Take \(S=A_5\).  Lemma 52.1 below proves simplicity of \(A_n\) for all \(n\ge5\).  The element
\[
 s=(1\ 2)(3\ 4)\in A_5
\]
is a nontrivial involution.  Therefore the corresponding lamp
\[
 r=\delta_{x_0}((1\ 2)(3\ 4))
\tag{51.9}
\]
has order two and satisfies
\[
 \boxed{
 \langle\!\langle r\rangle\!\rangle
 =\operatorname{Rad}_{\mathrm{MF}}(W_{A_5})
 =\operatorname{Res}_{\mathrm{fin}}(W_{A_5})
 =A_5^{(X)}.
 }
\tag{51.10}
\]
In particular, this single nontrivial involution belongs to **every finite-index subgroup** of \(W_{A_5}\), is killed by every finite-dimensional linear representation over every field and every compact-group representation, and is killed by every norm-matrix-corona representation.

By Theorem 49.5, the same involution remains in all five radicals of **every finite-index subgroup** of \(W_{A_5}\).

---

## 52. An infinite family invisible to every finite, compact, linear, and matrix-corona target in the dossier

The previous section hides one finite simple group in the common radical.  Varying the simple lamp produces infinitely many abstractly different groups while leaving all the visible quotient data fixed.

### 52.1 Elementary proof that the alternating groups give infinitely many simple lamps

#### Lemma 52.1

For every \(n\ge5\), the alternating group \(A_n\) is nonabelian simple.  Moreover
\[
 |A_n|=\frac{n!}{2},
\tag{52.1}
\]
so the groups \(A_n\), \(n\ge5\), are pairwise nonisomorphic.

#### Proof

We use right-to-left composition of permutations.

**Step 1: \(A_n\) is generated by 3-cycles.**  Every even permutation is a product of an even number of transpositions.  Pair the transpositions.  If two paired transpositions share one point, their product is a 3-cycle (or the identity if they are equal).  If they are disjoint, then
\[
 (a\ b)(c\ d)=(a\ b\ c)(b\ c\ d).
\tag{52.2}
\]
Thus every element of \(A_n\) is a product of 3-cycles.

**Step 2: all 3-cycles are conjugate in \(A_n\).**  Given
\((a\ b\ c)\) and \((a'\ b'\ c')\), choose \(\pi\in S_n\) sending
\(a,b,c\) to \(a',b',c'\).  If \(\pi\) is even, it already lies in \(A_n\).  If \(\pi\) is odd, there are at least two points outside
\(\{a',b',c'\}\) because \(n\ge5\); compose \(\pi\) on the left with the transposition of those two unused points.  This changes the parity but not the images of \(a,b,c\).  Hence an element of \(A_n\) conjugates one 3-cycle to the other.

**Step 3: every nontrivial normal subgroup contains a 3-cycle.**  Let
\(1\ne N\trianglelefteq A_n\), and choose \(1\ne\sigma\in N\).

If the cycle decomposition of \(\sigma\) contains a cycle of length at least four, choose four consecutive points
\[
 \sigma(a)=b,\qquad \sigma(b)=c,\qquad \sigma(c)=d
\]
in that cycle and set \(\tau=(a\ b\ c)\).  Then
\[
 [\sigma,\tau]
 =\sigma\tau\sigma^{-1}\tau^{-1}
 =(b\ c\ d)(a\ c\ b),
\tag{52.3}
\]
which is a 3-cycle by direct calculation.  Normality gives
\([\sigma,\tau]\in N\).

Suppose next that every cycle of \(\sigma\) has length at most three and that \(\sigma\) contains a 3-cycle \((a\ b\ c)\) together with another nontrivial cycle.  Choose \(d\) in the second cycle and put \(e=\sigma(d)\ne d\).  For \(\tau=(a\ b\ d)\),
\[
 [\sigma,\tau]
 =(b\ c\ e)(a\ d\ b),
\tag{52.4}
\]
which is the 5-cycle
\[
 (a\ d\ c\ e\ b).
\]
Thus \(N\) contains an element with a cycle of length at least four, and the previous paragraph produces a 3-cycle in \(N\).  If the original \(\sigma\) is itself a single 3-cycle, there is nothing to prove.

It remains to consider the case where \(\sigma\) is a product of disjoint transpositions.  Because \(\sigma\in A_n\), their number is even.  If \(\sigma\) fixes a point \(e\), choose a transposition \((a\ b)\) occurring in \(\sigma\) and put \(\tau=(a\ b\ e)\).  Conjugation by \(\sigma\) reverses the first two entries and fixes \(e\), so
\[
 \sigma\tau\sigma^{-1}=\tau^{-1}.
\]
Hence
\[
 [\sigma,\tau]=\tau^{-2}=\tau,
\]
a 3-cycle in \(N\).

If \(\sigma\) has no fixed point, then \(n\ge6\) and at least three transpositions occur.  Choose two of them, \((a\ b)\) and \((c\ d)\), and put \(\tau=(a\ b\ c)\).  A direct calculation gives
\[
 [\sigma,\tau]=(a\ c)(b\ d).
\tag{52.5}
\]
This element belongs to \(N\) and fixes at least \(n-4\ge2\) points, so the preceding fixed-point subcase applied to (52.5) produces a 3-cycle in \(N\).

Thus every nontrivial normal subgroup of \(A_n\) contains a 3-cycle.

**Step 4: simplicity.**  By Step 2, a normal subgroup containing one 3-cycle contains every 3-cycle.  By Step 1, the 3-cycles generate \(A_n\).  Therefore every nontrivial normal subgroup is all of \(A_n\).

The group is nonabelian; for example suitable overlapping 3-cycles do not commute.  Hence its commutator subgroup is nontrivial and normal, so simplicity also implies \(A_n\) is perfect.

Finally \(|A_n|=n!/2\) because the sign map \(S_n\to\{\pm1\}\) is onto with kernel \(A_n\).  These orders are strictly increasing for \(n\ge2\), so the \(A_n\) are pairwise nonisomorphic. ∎

### 52.2 The hidden simple type is recoverable from the invisible kernel

#### Lemma 52.2

Let \(S\) be a nonabelian simple group and let
\[
 L=\bigoplus_{i\in I}S_i
\]
be a nonzero restricted direct sum of copies of \(S\).  If \(T\) is a nonabelian simple quotient of \(L\), then
\[
 T\cong S.
\tag{52.6}
\]
Conversely, \(S\) is a quotient of \(L\) by any coordinate projection.

#### Proof

Let \(\phi:L\twoheadrightarrow T\).  Each coordinate subgroup \(S_i\) is normal in \(L\), so \(\phi(S_i)\trianglelefteq T\).  Since \(T\) is simple, each image is either \(1\) or \(T\).  The coordinate subgroups generate \(L\), and \(\phi\) is onto, so at least one coordinate has \(\phi(S_i)=T\).  The restriction
\[
 \phi|_{S_i}:S\twoheadrightarrow T
\]
has normal kernel in the simple group \(S\).  It is not the whole group, hence the kernel is trivial.  Therefore \(T\cong S\).

The converse is the obvious projection onto any chosen coordinate. ∎

Consequently the isomorphism type of the direct sum remembers the simple lamp type: if
\[
 \bigoplus_I S\cong\bigoplus_J T
\]
for nonempty index sets and nonabelian simple \(S,T\), then \(S\cong T\).

### 52.3 The approximation-indistinguishable family

For every \(n\ge5\), define
\[
 W_n:=A_n^{(G_*/\Gamma_*)}\rtimes G_*.
\tag{52.7}
\]

#### Theorem 52.3 (infinitely many pairwise noncommensurable groups with the same visible approximation theory)

The family \((W_n)_{n\ge5}\) has the following properties.

1. Every \(W_n\) is finitely generated, sofic, hyperlinear, and non-MF.
2. Its common approximation kernel is
   \[
   R_n=A_n^{(G_*/\Gamma_*)}.
   \tag{52.8}
   \]
   This subgroup is fully invariant and is the MF radical, finite-dimensional unitary residual, all-fields linear residual, Bohr kernel, and finite residual.
3. Every quotient
   \[
   q_n:W_n\twoheadrightarrow G_*
   \tag{52.9}
   \]
   is split, has kernel \(R_n\), and is the universal quotient seen by residually finite groups, countable MF groups, and finite-dimensional linear groups over arbitrary fields.
4. All \(W_n\) have canonically isomorphic profinite completions and Bohr compactifications:
   \[
   \widehat{W_n}\cong\widehat{G_*},
   \qquad
   bW_n\cong bG_*.
   \tag{52.10}
   \]
5. For every pair \(m,n\ge5\), the groups \(W_m\) and \(W_n\) have equivalent finite-action categories, inclusion- and index-preserving isomorphic finite-index subgroup lattices, and equivalent finite-dimensional representation categories over every field.  For every norm matrix corona \(\mathcal Q_{\mathbf d}\),
   \[
   \operatorname{Hom}(W_n,U(\mathcal Q_{\mathbf d}))
   \cong
   \operatorname{Hom}(G_*,U(\mathcal Q_{\mathbf d}))
   \tag{52.11}
   \]
   by precomposition with \(q_n\).
6. The groups \(W_n\) are pairwise not abstractly commensurable; in particular they are pairwise nonisomorphic.
7. Every finite-index subgroup of every \(W_n\) is again non-MF, non-residually-finite, nonlinear over every field, and non-MAP, with the same residual \(R_n\).

#### Proof

By Lemma 52.1 each \(A_n\) is finite, nontrivial, and perfect.  Items 1--5 follow from Theorems 39.9, 47.1, 48.6, 50.3, and the perfect-lamp specialization \(P_{A_n}=G_*\).

For completeness, soficity implies hyperlinearity directly.  If \(\sigma,\tau\in\operatorname{Sym}(d)\) and \(P_\sigma,P_\tau\) are their permutation matrices, then
\[
 \|P_\sigma-P_\tau\|_{2,d}^2
 =2-2\frac{|\operatorname{Fix}(\sigma^{-1}\tau)|}{d}
 =2d_{\mathrm{Ham}}(\sigma,\tau).
\tag{52.12}
\]
Indeed \(P_\sigma^*P_\tau=P_{\sigma^{-1}\tau}\), whose normalized trace is the proportion of fixed points.  Thus a Hamming-asymptotic permutation model becomes a Hilbert--Schmidt-asymptotic unitary model, and Hamming separation becomes Hilbert--Schmidt separation.  Hence every sofic \(W_n\) is hyperlinear.

For pairwise noncommensurability, suppose finite-index subgroups
\[
 H_m\le_f W_m,
 \qquad
 H_n\le_f W_n
\]
are isomorphic by \(f:H_m\xrightarrow{\cong}H_n\).  The finite residual is
intrinsic under isomorphism, while Theorem 49.5 gives
\[
 \operatorname{Res}_{\mathrm{fin}}(H_m)=R_m,
 \qquad
 \operatorname{Res}_{\mathrm{fin}}(H_n)=R_n.
\]
Therefore \(f(R_m)=R_n\), so
\[
 A_m^{(G_*/\Gamma_*)}\cong A_n^{(G_*/\Gamma_*)}.
\]
By Lemma 52.2, the nonabelian simple quotients of the left-hand radical are
precisely copies of \(A_m\), while those of the right-hand radical are
precisely copies of \(A_n\).  Hence \(A_m\cong A_n\), and Lemma 52.1 gives
\(m=n\).  Thus distinct members are not abstractly commensurable, proving
item 6.

Item 7 is Theorem 49.5. ∎

This family shows that the invisible kernel can carry genuinely different finite simple algebra while **every finite, profinite, compact, finite-dimensional-linear, and matrix-corona target functor considered in this dossier sees exactly the same quotient**.  In particular, even an index-preserving isomorphism of the entire finite-index subgroup lattice does not force abstract commensurability.

No claim of literature priority is made here.  This is a deduction from the proved kernel computation; I did not identify a prior statement in this exact form among the sources searched for this dossier, but establishing priority would require a dedicated literature investigation.

### 52.4 Two explicit generators for \(A_5\)

The nine-generator count used later can also be justified without a database.
Put
\[
 a=(1\ 2\ 3),
 \qquad
 b=(1\ 2\ 3\ 4\ 5),
\]
and let \(H=\langle a,b\rangle\le A_5\).  Since \(H\) contains elements of
orders \(3\) and \(5\), Lagrange's theorem implies that \(15\mid |H|\).  By
Lemma 52.1, \(|A_5|=60\), so
\[
 |H|\in\{15,30,60\}.
\]
The case \(|H|=30\) is impossible: an index-two subgroup is normal, while
\(A_5\) is simple.  A group of order \(15\) is cyclic: Sylow gives a unique
5-Sylow subgroup and a unique 3-Sylow subgroup, and their product is the whole
group.  But \(a\) and \(b\) do not commute; for example
\(ab(2)=1\) whereas \(ba(2)=4\) under right-to-left composition.  Hence
\(|H|\ne15\).  Therefore \(|H|=60\) and
\[
 A_5=\langle(1\ 2\ 3),(1\ 2\ 3\ 4\ 5)\rangle.
\tag{52.13}
\]
Thus Proposition 43.3 gives the explicit bound \(d(W_{A_5})\le9\).

### 52.5 Independent Wolfram sanity check for the alternating-lamp base case

The proof of Lemma 52.1 and (52.13) does not depend on computation.  As an
independent check of the smallest case used repeatedly above, a Wolfram
Language kernel was asked to form the subgroup generated by
\((1\ 2\ 3)\) and \((1\ 2\ 3\ 4\ 5)\).  It returned order \(60\), the same
order as `AlternatingGroup[5]`, and equality of the two enumerated groups.
Separate permutation-product checks also returned the 3-cycle, 5-cycle, and
double-transposition cycle types used in the case analysis of Step 3.  These
computations are sanity checks only; simplicity and perfectness are proved in
Lemma 52.1.

---

## 53. A single four-dimensional rational representation realizes the entire hidden kernel for perfect lamps

The perfect-lamp examples are nonlinear, but their entire all-fields linear residual is nevertheless the kernel of one very small explicit representation.

Let
\[
 \rho_*:G_*\hookrightarrow\mathrm{GL}_4(\mathbb Q)
\tag{53.1}
\]
be the faithful representation of Section 39.7, whose image actually lies in \(\mathrm{GL}_4(\mathbb Z[1/2])\).  For a finite perfect lamp \(K\), let
\[
 q_K:W_K\twoheadrightarrow G_*
\]
be the semidirect-product projection and define
\[
 \rho_K=\rho_*q_K:
 W_K\longrightarrow\mathrm{GL}_4(\mathbb Q).
\tag{53.2}
\]

#### Theorem 53.1 (four-dimensional rational envelope)

For every nontrivial finite perfect \(K\),
\[
 \boxed{
 \ker\rho_K
 =K^{(G_*/\Gamma_*)}
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Rad}_{\mathrm{lin}}(W_K)
 =\operatorname{Rad}_{\mathrm{Bohr}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K).
 }
\tag{53.3}
\]
Moreover
\[
 \rho_K(W_K)=\rho_*(G_*)
\tag{53.4}
\]
for every such \(K\).

#### Proof

Because \(\rho_*\) is injective,
\[
 \ker(\rho_*q_K)=\ker q_K.
\]
For perfect \(K\), \(\ker q_K\) is the full lamp subgroup by (48.10).  The equality with all five residuals is Theorem 47.1 specialized to perfect lamps.  Surjectivity of \(q_K\) gives (53.4). ∎

Thus a group can fail to be linear over every field because of a large common residual even though that entire residual is already the kernel of one explicit **four-dimensional rational** representation.

### 53.1 Universal factorization through the fixed four-dimensional image

Put
\[
 \Lambda:=\rho_*(G_*)\le\mathrm{GL}_4(\mathbb Q).
\tag{53.5}
\]
Since \(\rho_*:G_*\to\Lambda\) is an isomorphism, Theorem 42.5 and Theorem 46.3 immediately sharpen as follows.

#### Corollary 53.2

For every finite perfect \(K\), every homomorphism from \(W_K\) to a residually finite group, a countable MF group, or a finite-dimensional linear group over any field factors uniquely through the single quotient
\[
 \rho_K:W_K\twoheadrightarrow\Lambda\le\mathrm{GL}_4(\mathbb Q).
\tag{53.6}
\]
In particular, for the whole family \((W_n)_{n\ge5}\), the **same concrete matrix group \(\Lambda\)** is the universal visible quotient for all these target classes.

#### Proof

Every such homomorphism factors uniquely through \(q_K:W_K\to G_*\) by Sections 42 and 46.  Transport that factorization across the isomorphism \(\rho_*:G_*\to\Lambda\). ∎

For \(K=A_5\), combine this with (51.10): the kernel of the four-dimensional map (53.2) is the normal closure of **one involution**.

### 53.2 Restricted-target equivalence: all approximation targets see the quotient map as an isomorphism

Let \(\mathscr T\) be the collection of target groups consisting of:

- finite groups;
- residually finite groups;
- countable MF groups;
- finite-dimensional linear groups \(\mathrm{GL}_d(F)\) over arbitrary fields;
- compact Hausdorff groups;
- unitary groups of norm matrix coronas.

Call a homomorphism \(q:A\to B\) a **\(\mathscr T\)-equivalence** if for every \(T\in\mathscr T\), precomposition is a bijection
\[
 q^*:\operatorname{Hom}(B,T)
 \xrightarrow{\cong}
 \operatorname{Hom}(A,T).
\tag{53.7}
\]

#### Theorem 53.3 (a split nonisomorphism invisible to all target classes in the dossier)

For every nontrivial finite perfect \(K\), the split quotient
\[
 q_K:W_K\twoheadrightarrow G_*
\tag{53.8}
\]
is a \(\mathscr T\)-equivalence but is not an isomorphism.  For the family
\(W_n\) of Section 52, every map \(q_n:W_n\to G_*\) is such an equivalence.

#### Proof

The kernel of \(q_K\) is the nontrivial lamp subgroup, so \(q_K\) is not injective and hence not an isomorphism.  It is split because \(W_K\) is a semidirect product.

For finite targets, bijectivity is Theorem 42.3.  For residually finite targets it is Corollary 42.4.  For countable MF targets it is Corollary 42.5.  For finite-dimensional linear targets over arbitrary fields it is Theorem 46.3.  For compact targets it is Corollary 46.7.  For norm matrix corona unitary groups it is Theorem 42.1.  In the perfect-lamp case every one of those theorems has quotient \(P_K=G_*\), so all the required maps are precisely precomposition by \(q_K\). ∎

Thus the entire collection of approximation targets used in this dossier is **not jointly conservative** on finitely generated groups: it sends the nonisomorphism (53.8) to bijections on every represented Hom-set.  The MF difference survives because MF asks whether one of those corona maps is injective on the *original domain*; the targetwise factorization data alone forgets the nontrivial common kernel.


### 53.3 The canonical section is equally invisible

For perfect \(K\), write
\[
 q_K:W_K=R_K\rtimes G_*\twoheadrightarrow G_*,
 \qquad
 s_K:G_*\hookrightarrow W_K
\tag{53.9}
\]
for the projection and the canonical semidirect-product section.  Thus
\(q_Ks_K=\operatorname{id}_{G_*}\).

#### Corollary 53.4 (restriction and inflation are inverse on every visible target)

Let \(K\) be a nontrivial finite perfect group and let \(T\in\mathscr T\), where
\(\mathscr T\) is the target collection of Section 53.2.  Then
\[
 q_K^*:\operatorname{Hom}(G_*,T)
 \xrightarrow{\cong}
 \operatorname{Hom}(W_K,T)
\tag{53.10}
\]
and
\[
 s_K^*:\operatorname{Hom}(W_K,T)
 \xrightarrow{\cong}
 \operatorname{Hom}(G_*,T)
\tag{53.11}
\]
are inverse bijections.  In particular the proper inclusion \(s_K(G_*)<W_K\)
and the noninjective split epimorphism \(q_K\) are both invisible to all target
classes in \(\mathscr T\).

#### Proof

Theorem 53.3 says that \(q_K^*\) is bijective.  Since
\(q_Ks_K=\operatorname{id}_{G_*}\), contravariance of Hom gives
\[
 s_K^*q_K^*=\operatorname{id}_{\operatorname{Hom}(G_*,T)}.
\]
Because \(q_K^*\) is bijective, its left inverse is its inverse.  Hence
\(s_K^*=(q_K^*)^{-1}\), proving both assertions. ∎

This is stronger than an isomorphism of profinite completions: every visible
representation of the larger group is *uniquely determined by its restriction
to the proper retract* \(G_*\), and every visible representation of the retract
extends uniquely across the whole lamp extension by killing \(R_K\).

### 53.4 Hereditary target twins at every finite index

The phenomenon persists simultaneously throughout the finite-index subgroup
lattice.

#### Theorem 53.5 (finite-index twin tower)

Let \(K\) be nontrivial, finite, and perfect.  For every finite-index subgroup
\(H\le W_K\), put
\[
 J=q_K(H)\le G_*.
\tag{53.12}
\]
Then:

1. \(J\) has finite index in \(G_*\), and
   \[
   H=q_K^{-1}(J)=R_K\rtimes J.
   \tag{53.13}
   \]
2. The restriction
   \[
   q_H:=q_K|_H:H\twoheadrightarrow J
   \tag{53.14}
   \]
   is split by the canonical inclusion \(J\hookrightarrow R_K\rtimes J\).
3. For every \(T\in\mathscr T\), precomposition with \(q_H\) is a bijection
   \[
   q_H^*:\operatorname{Hom}(J,T)
   \xrightarrow{\cong}
   \operatorname{Hom}(H,T),
   \tag{53.15}
   \]
   and restriction along \(J\hookrightarrow H\) is its inverse.
4. \(J\) is residually finite and MF, whereas \(H\) is sofic and non-MF.
5. The quotient \(q_H\) induces an index-preserving bijection between all
   finite-index subgroups of \(H\) and all finite-index subgroups of \(J\), an
   equivalence of finite-action categories, and canonical isomorphisms
   \[
   \widehat H\cong\widehat J,
   \qquad
   bH\cong bJ.
   \tag{53.16}
   \]
6. The assignment \(H\mapsto J\) is exactly the index-preserving lattice
   bijection of Theorem 48.6.  Thus **every node** of the finite-index lattice
   of \(W_K\) has a canonically paired MF node on the \(G_*\) side with the
   same finite/compact/linear/corona target theory.

#### Proof

By Theorem 49.5, \(R_K\le H\).  Therefore if \(w\in q_K^{-1}(J)\), choose
\(h\in H\) with \(q_K(h)=q_K(w)\).  Then \(wh^{-1}\in R_K\le H\), so
\(w\in H\).  Hence \(H=q_K^{-1}(J)\).  Since \(q_K\) is the semidirect-product
projection, this preimage is exactly \(R_K\rtimes J\), proving (1) and (2).
The index identity
\([W_K:H]=[G_*:J]\) follows from the quotient correspondence; in
particular \(J\le_fG_*\).

For (3), let \(f:H\to T\).  We show \(R_K\le\ker f\) in each target class.
For a finite or residually finite target this follows from
\(R_K=\operatorname{Res}_{\mathrm{fin}}(H)\) and functoriality of the finite
residual.  For a finite-dimensional linear target it follows from
\(R_K=\operatorname{Rad}_{\mathrm{lin}}(H)\); for a compact target from
\(R_K=\operatorname{Rad}_{\mathrm{Bohr}}(H)\); for a countable MF target from
\(R_K=\operatorname{Rad}_{\mathrm{MF}}(H)\) together with the triviality of
the MF radical of an MF group; and for a norm matrix corona unitary group it
is exactly the definition of \(R_K=\operatorname{Rad}_{\mathrm{MF}}(H)\).
Thus \(f\) factors uniquely through \(H/R_K\cong J\), which is (53.15).
The section gives the inverse exactly as in Corollary 53.4.

Finally \(J\le G_*\) is residually finite and MF because these properties pass
to subgroups, while Theorem 49.5 says that \(H\) is sofic and non-MF.

For item (5), Theorem 49.5 gives
\(R_K=\operatorname{Res}_{\mathrm{fin}}(H)=\operatorname{Rad}_{\mathrm{Bohr}}(H)\).
Hence every finite-index subgroup of \(H\) contains \(R_K\), so ordinary
quotient correspondence through \(H/R_K\cong J\) gives the finite-index
lattice bijection with preservation of indices and normality.  The finite-action
category equivalence follows exactly as in Proposition 48.2.  Passing to the
inverse systems of finite quotients gives \(\widehat H\cong\widehat J\), and
the targetwise equivalence for compact groups identifies the Bohr
compactifications, giving (53.16).  Item (6) is Theorem 48.6 together with
(53.13). ∎

This hereditary form makes the noncommensurability conclusion of Corollary
49.6 particularly rigid: the finite-index lattices correspond perfectly, but
**corresponding subgroups always lie on opposite sides of MF**.

---

## 54. Terminal strengthened endpoint: advances obtained here and the next possible finish lines

The preceding sections permit a final theorem which packages the strongest fully proved conclusions of this dossier.

### 54.1 Master theorem

#### Theorem 54.1

There is an explicit finitely generated residually finite group
\[
 G_*\le\mathrm{GL}_4(\mathbb Z[1/2])
\]
containing a property-\((T)\) subgroup \(\Gamma_*\) with an index-eight proper self-embedding, such that for every nontrivial finite group \(K\) the permutational wreath product
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*
\tag{54.1}
\]
is sofic and non-MF and has a completely explicit normal subgroup \(R_K\) satisfying
\[
 \boxed{
 R_K
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Rad}_{\mathrm{lin}}(W_K)
 =\operatorname{Rad}_{\mathrm{Bohr}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K).
 }
\tag{54.2}
\]
The quotient is
\[
 W_K/R_K
 \cong
 K_{\mathrm{ab}}^{(\mathbb Z)}\rtimes_hG_*,
\tag{54.3}
\]
which is residually finite and MF.

The kernel \(R_K\) is fully invariant.  Every finite-index subgroup \(H\le W_K\) contains \(R_K\) and has exactly the same five residuals:
\[
 \operatorname{Rad}_{\mathrm{MF}}(H)
 =\operatorname{Rad}_{\mathrm{fd}}(H)
 =\operatorname{Rad}_{\mathrm{lin}}(H)
 =\operatorname{Rad}_{\mathrm{Bohr}}(H)
 =\operatorname{Res}_{\mathrm{fin}}(H)
 =R_K.
\tag{54.4}
\]
Hence no finite-index subgroup is MF, residually finite, linear over any field, or MAP.

If \(K=S\) is finite nonabelian simple, then
\[
 R_S=S^{(G_*/\Gamma_*)}
\tag{54.5}
\]
and \(R_S\) is the normal closure of any single nonidentity lamp element.  Thus
\[
 W_S/\langle\!\langle r\rangle\!\rangle\cong G_*
\tag{54.6}
\]
for any nontrivial one-site lamp \(r\), while this quotient changes none of the finite, profinite, compact, finite-dimensional-linear, or norm-matrix-corona target functors described above.

Finally the groups
\[
 W_n=A_n^{(G_*/\Gamma_*)}\rtimes G_*\qquad(n\ge5)
\tag{54.7}
\]
form an infinite pairwise noncommensurable family of finitely generated sofic non-MF groups with the same profinite completion, the same Bohr compactification, the same finite-index subgroup lattice with indices, the same finite-action category, the same finite-dimensional representation categories over every field, and the same homomorphism sets into every norm matrix corona.  Their different finite simple lamp types are stored entirely inside the invisible fully invariant radicals.

For every perfect finite \(K\), both the split quotient \(q_K:W_K\twoheadrightarrow G_*\) and the canonical proper section \(G_*\hookrightarrow W_K\) induce inverse bijections on Hom-sets into every target class \(\mathscr T\) of Section 53.2.  Moreover every finite-index \(H\le W_K\) is uniquely
\[
 H=R_K\rtimes J
 \qquad(J\le_fG_*),
\]
and the split quotient \(H\twoheadrightarrow J\) has the same targetwise equivalence while \(H\) is non-MF and \(J\) is MF.

#### Proof

The construction of \(G_*\), the index-eight embedding, property \((T)\), residual finiteness, and the sofic/non-MF wreath products are Sections 39--40.  Equation (54.2) is Theorem 47.1.  Equation (54.3) is Theorem 39.9.  Full invariance is Section 50.  The finite-index statement (54.4) is Theorem 49.5.  The simple-lamp statements (54.5)--(54.6) are Theorem 51.1 and Corollary 51.2.  The infinite family (54.7), including pairwise noncommensurability, is Theorem 52.3.  The targetwise equivalence of the quotient and section and its finite-index hereditary form are Corollary 53.4 and Theorem 53.5. ∎

### 54.2 A split-extension failure package

The concrete \(C_2\)-lamp instance makes a useful permanence-theoretic
contrast with Section 49.

Put
\[
 A:=(C_2)^{(G_*/\Gamma_*)}.
\tag{54.8}
\]
Then
\[
 1\longrightarrow A\longrightarrow W_{C_2}
 \overset{q}{\longrightarrow}G_*\longrightarrow1
\tag{54.9}
\]
is split.

#### Theorem 54.2 (MF is not closed under split extensions, even with an elementary abelian kernel)

In the split exact sequence (54.9):

1. \(A\) is elementary abelian of exponent two, locally finite, amenable,
   residually finite, MF, MAP, and linear over a field;
2. \(G_*\) is finitely generated, residually finite, MF, MAP, and linear over
   \(\mathbb Q\);
3. \(W_{C_2}\) is finitely generated, sofic, and hyperlinear, but is not MF,
   not residually finite, not MAP, and not linear over any field.

Consequently:

- MF is **not closed under split extensions**, even when the kernel is
  elementary abelian, locally finite, amenable, and residually finite and the
  quotient is residually finite and linear;
- residual finiteness and MAP are likewise not closed under such split
  extensions;
- the property “linear over some field” is not closed under split extensions
  (the two factors may use different fields).

#### Proof

Every finitely generated subgroup of \(A\) is supported on finitely many sites,
so it is a finite elementary abelian 2-group.  Hence \(A\) is locally finite.
To see amenability directly, given a finite set \(F\subset A\), the finite subgroup
\(L=\langle F\rangle\) is exactly invariant under left multiplication by every
element of \(F\); thus \(L\) is a Følner set for \(F\).  It is residually finite: if \(1\ne a\in A\), some
site coordinate of \(a\) is nontrivial, and projection to that copy of \(C_2\)
separates \(a\).  Residual finiteness implies MF and MAP by the finite-quotient
representations used earlier in the dossier.

For linearity of \(A\), enumerate the countable site set as \(X=\{x_1,x_2,\ldots\}\)
and take
\[
 F=\mathbb F_2(t_1,t_2,\ldots).
\]
The elements \(t_i\) are linearly independent over \(\mathbb F_2\).  If
\(a=(a_i)\in A\) has finite support, put
\[
 \lambda(a)=\sum_i a_i t_i\in F
\]
and define
\[
 \iota_A(a)=
 \begin{pmatrix}
 1&\lambda(a)\\
 0&1
 \end{pmatrix}
 \in\mathrm{GL}_2(F).
\tag{54.10}
\]
Because \(F\) has characteristic two,
\(\iota_A(a)\iota_A(b)=\iota_A(a+b)\), and linear independence of the
\(t_i\) makes \(\iota_A\) injective.  Thus \(A\) is linear over \(F\).

Section 39 gives the faithful embedding
\(G_*\hookrightarrow\mathrm{GL}_4(\mathbb Q)\) and residual finiteness of
\(G_*\); hence \(G_*\) is MF and MAP as well.

Finally \(W_{C_2}\) is the concrete finite-lamp wreath group of Sections 39--47.
It is finitely generated and sofic, hence hyperlinear by (52.12), while
Theorem 47.1 gives a nontrivial MF radical, finite residual, all-fields linear
residual, and Bohr kernel.  Therefore it has none of MF, residual finiteness,
linearity over any field, or MAP.  This proves every assertion. ∎

The contrast is worth recording explicitly:

\[
\boxed{
\text{MF is stable under finite-index passage (Corollary 49.2A),
 but fails for split extensions (Theorem 54.2).}
}
\tag{54.11}
\]

#### Corollary 54.2A (the MF radical can itself be residually finite and MF)

For every nontrivial finite \(K\), the explicit subgroup \(R_K\) is nontrivial,
normal in \(W_K\), locally finite, amenable, and residually finite.  Hence
intrinsically
\[
 \operatorname{Rad}_{\mathrm{MF}}(R_K)
 =\operatorname{Rad}_{\mathrm{fd}}(R_K)
 =\operatorname{Rad}_{\mathrm{lin}}(R_K)
 =\operatorname{Rad}_{\mathrm{Bohr}}(R_K)
 =\operatorname{Res}_{\mathrm{fin}}(R_K)
 =1,
\tag{54.12}
\]
while ambiently
\[
 R_K
 =\operatorname{Rad}_{\mathrm{MF}}(W_K)
 =\operatorname{Rad}_{\mathrm{fd}}(W_K)
 =\operatorname{Rad}_{\mathrm{lin}}(W_K)
 =\operatorname{Rad}_{\mathrm{Bohr}}(W_K)
 =\operatorname{Res}_{\mathrm{fin}}(W_K).
\tag{54.13}
\]
Thus the finite-index intersection theorem of Section 49 is genuinely sharp:
none of these radical identities is hereditary under arbitrary subgroup
intersection, even for a normal amenable residually finite subgroup.

#### Proof

The map \(\Phi_\infty\) of Section 37 preserves the \(G_*\)-coordinate.
Therefore its kernel \(R_K\) is contained in the restricted direct sum
\(K^{(G_*/\Gamma_*)}\).  Any finitely generated subgroup of that direct sum is
supported on the finite union of the supports of its generators and is
therefore contained in a finite direct product of copies of the finite group
\(K\).  Hence the lamp group, and thus \(R_K\), is locally finite.  As in the
proof of Theorem 54.2, local finiteness gives amenability directly.

The restricted direct sum is residually finite: if a finitely supported
configuration is nontrivial, projection to any site on which it is nontrivial
separates it in the finite group \(K\).  Residual finiteness passes to
subgroups, so \(R_K\) is residually finite.  Consequently finite quotients
separate every nonidentity element of \(R_K\).  Their finite regular
representations also separate points in finite-dimensional complex unitary
representations and in finite-dimensional linear representations; the same
finite quotient maps separate points in the Bohr compactification and in norm
matrix coronas.  This proves (54.12).

Nontriviality of \(R_K\) is the two-site torsion defect used to prove non-MF-ness
in Sections 34, 36, and 39.  Equation (54.13) is Theorem 47.1. ∎

The phenomenon is conceptually useful: the obstruction is not that the hidden
subgroup is intrinsically hard to approximate.  **It is exceptionally easy to
approximate on its own.**  What fails is extension of those separating models
through the ambient compressed action.

### 54.3 Exact non-finite-presentability of every finite-lamp example

We now close a presentation-theoretic point which earlier versions of this
dossier left as a future problem.

Let a finitely generated group \(G\) act transitively on a set \(X=G/\Gamma\),
let \(1\ne K\) be finite, and write
\[
 W=K^{(X)}\rtimes G.
\tag{54.14}
\]

#### Lemma 54.3 (finite presentation forces finitely many diagonal pair-orbits)

Assume the stabilizer \(\Gamma\) is finitely generated.  If the transitive
permutational wreath product \(W\) in (54.14) is finitely presented, then the
diagonal action of \(G\) on \(X\times X\) has only finitely many orbits.

#### Proof

Choose a finite generating set \(A\) of the finite group \(K\).  Since the
action on \(X\) is transitive, the whole lamp subgroup \(K^{(X)}\) is the
normal closure in \(W\) of the root copy \(K_{\Gamma}\), hence of the finite
set \(A_{\Gamma}\).  Therefore
\[
 G\cong W/\langle\!\langle A_{\Gamma}\rangle\!\rangle.
\tag{54.15}
\]
If \(W\) is finitely presented, adding the finitely many relations
\(a_{\Gamma}=1\) gives a finite presentation of \(G\).  Thus under the
hypothesis of the lemma, \(G\) is finitely presented.

Consider the **free permutational precursor**
\[
 E:=\Bigl(*_{x\in X}K_x\Bigr)\rtimes G,
\tag{54.16}
\]
where \(G\) permutes the free factors.  This group is finitely presented.  To
see this directly, choose finite presentations
\(G=\langle S\mid R_G\rangle\) and \(K=\langle A\mid R_K\rangle\), and choose
a finite generating set \(U\) of \(\Gamma\), written as words in \(S\).  Then
\[
 E\cong
 \left\langle
 S,A\ \middle|\ R_G,R_K,
 [u,a]=1\ (u\in U,\ a\in A)
 \right\rangle.
\tag{54.17}
\]
Indeed the relations say exactly that the root copy of \(K\) is centralized by
its stabilizer \(\Gamma\); its conjugates by representatives of the cosets
\(G/\Gamma\) then give well-defined copies \(K_x\), and no relation is imposed
between distinct copies.  This is precisely the universal property of the free
product in (54.16).

There is a natural quotient
\[
 E\twoheadrightarrow W
\tag{54.18}
\]
whose kernel \(C\) is the normal closure of all cross-site commutators
\[
 [k_x,\ell_y],
 \qquad x\ne y,
 \quad k,\ell\in K.
\tag{54.19}
\]
Since both \(E\) and \(W\) are finitely presented and the displayed finite
set \(S\cup A\) generates both, \(C\) is finitely normally generated.  Indeed,
finite Tietze transformations give a finite presentation of \(W\) on the
generating set \(S\cup A\); lift its finitely many defining relators to the
free group on \(S\cup A\) and compare with the finite relator set (54.17).

Choose finite normal generators \(c_1,\ldots,c_r\) of \(C\).  Each \(c_j\),
being in the normal closure of (54.19), is a finite product of conjugates of
finitely many cross-site commutators.  Across all \(j\), only finitely many
\(G\)-orbits of unordered pairs \(\{x,y\}\), \(x\ne y\), occur.  Let
\(\mathcal O\) be their finite union.

Form the \(G\)-invariant graph \(\mathcal G\) on vertex set \(X\) whose edges
are exactly the pairs in \(\mathcal O\), and let \(B_{\mathcal G}\) be the graph
product of the vertex groups \(K_x\): distinct vertex groups commute exactly
when their vertices are adjacent.  The \(G\)-action preserves \(\mathcal G\),
so we have the semidirect product
\[
 E_{\mathcal G}:=B_{\mathcal G}\rtimes G
\tag{54.20}
\]
and a quotient \(E\twoheadrightarrow E_{\mathcal G}\).  By construction every
commutator used in an expression for every \(c_j\) vanishes in
\(E_{\mathcal G}\).  Thus every \(c_j\) vanishes, hence the whole normal
closure \(C\) vanishes.  Therefore (54.18) factors through a homomorphism
\[
 W=E/C\longrightarrow E_{\mathcal G}.
\tag{54.21}
\]
On the other hand, imposing the remaining cross-site commutators gives a
surjection \(E_{\mathcal G}\twoheadrightarrow W\).  Both maps are induced by
the identity on the generators \(S\cup A\), so they are inverse.  Hence
\(E_{\mathcal G}\cong W\).

If the diagonal action on \(X\times X\) had an orbit of distinct pairs not
represented in \(\mathcal O\), choose a nonedge \(x\ne y\) of
\(\mathcal G\) and nonidentity \(k,\ell\in K\).  Killing every vertex group
except \(K_x\) and \(K_y\) defines a retraction of the graph-product base
onto the free product \(K_x*K_y\), because there is no edge between \(x\) and
\(y\).  The reduced free-product word
\[
 k_x\ell_y k_x^{-1}\ell_y^{-1}
\tag{54.22}
\]
is nontrivial.  Thus \([k_x,\ell_y]\ne1\) in \(E_{\mathcal G}\), contradicting
\(E_{\mathcal G}\cong W\), where all different-site lamp groups commute.
Therefore only finitely many diagonal pair-orbits can exist. ∎

This is the necessity direction of the classical finite-presentation criterion
for permutational wreath products, specialized and proved here in the exact
form needed below.

#### Lemma 54.4 (the HNN coset square has infinitely many orbits)

For the concrete ascending HNN group \(G_*\) and
\(X=G_*/\Gamma_*\), the diagonal action on \(X\times X\) has infinitely many
orbits.

#### Proof

For a transitive action on \(G_*/\Gamma_*\), diagonal orbits are classified by
double cosets \(\Gamma_*\backslash G_*/\Gamma_*\): translate the first
coordinate of a pair to \(\Gamma_*\); the residual stabilizer is
\(\Gamma_*\), whose orbits on the second coordinate are exactly double cosets.

Let \(\chi:G_*\to\mathbb Z\) be the height homomorphism of Section 9, with
\(\chi(\Gamma_*)=0\) and \(\chi(t)=1\).  Every element of the double coset
\(\Gamma_*t^n\Gamma_*\) has height \(n\).  Consequently
\[
 \Gamma_*t^m\Gamma_*\ne\Gamma_*t^n\Gamma_*
 \qquad(m\ne n).
\tag{54.23}
\]
Thus there are infinitely many double cosets and hence infinitely many
diagonal orbits. ∎

#### Theorem 54.5 (the concrete finite-lamp witnesses are never finitely presented)

For every nontrivial finite group \(K\),
\[
 W_K=K^{(G_*/\Gamma_*)}\rtimes G_*
\tag{54.24}
\]
is finitely generated but **not finitely presented**.

#### Proof

Finite generation was proved in Proposition 43.3 (indeed
\(d(W_K)\le7+d(K)\)).  The stabilizer of the base coset is \(\Gamma_*\), which
is finitely generated because it has property \((T)\).  If \(W_K\) were
finitely presented, Lemma 54.3 would force finitely many diagonal orbits on
\((G_*/\Gamma_*)^2\), contradicting Lemma 54.4. ∎

#### Corollary 54.6 (no virtual finite presentation and no finitely presented commensurable model)

Every finite-index subgroup of every \(W_K\) is not finitely presented.
Consequently no \(W_K\) is abstractly commensurable with a finitely presented
group.

#### Proof

Finite presentability is invariant under passage to finite-index subgroups and
finite-index supergroups.  For completeness, the downward direction is the
Reidemeister--Schreier rewriting theorem: a finite presentation and a finite
coset transversal produce finitely many generators and relators for a
finite-index subgroup.  For the upward direction, if \(H\le_fG\) is finitely
presented, replace \(H\) by its finite-index normal core \(C\trianglelefteq G\).
The downward direction makes \(C\) finitely presented.  The quotient \(G/C\) is
finite.  Choose finitely many lifts of its elements.  A presentation of \(C\),
together with finitely many relations recording multiplication among the
chosen quotient lifts and their conjugation action on a finite generating set
of \(C\), gives a finite presentation of \(G\).  Thus if any finite-index
subgroup of \(W_K\) were finitely presented, \(W_K\) would be finitely
presented, contradicting Theorem 54.5.

If \(W_K\) were commensurable with a finitely presented group \(M\), isomorphic
finite-index subgroups of \(W_K\) and \(M\) would exist.  The finite-index
subgroup of \(M\) would be finitely presented by the downward direction, while
the corresponding subgroup of \(W_K\) is not, a contradiction. ∎

In particular the eight-generator \(C_2\) example and the \(A_5\) example with its explicit
nine-element generating set are both finitely generated, sofic, non-MF, and not finitely
presented.  The presentation-theoretic obstruction is now exact: it is the
infinite height family of double cosets, not an unspecified defect of the
construction.

### 54.4 New advances obtained in the final strengthening pass

The following deductions were not needed for the original email and arise only after combining the exact telescope radical with the concrete affine model.

1. **Finite-index induction for the MF radical.**  The block-monomial induction proof gives the general identity
   \(\operatorname{Rad}_{\mathrm{MF}}(H)=H\cap\operatorname{Rad}_{\mathrm{MF}}(G)\) for every finite-index inclusion \(H\le G\).
2. **No virtual repair.**  Every finite-index subgroup of every concrete \(W_K\) has the same nontrivial MF, finite, linear, unitary, and Bohr residual \(R_K\).  The groups are not merely non-MF and non-linear; they are **not virtually MF, not virtually residually finite, not virtually linear over any field, and not virtually MAP**.
3. **Intrinsic functoriality.**  The explicit telescope kernel is fully invariant, and every homomorphism between two groups in the family descends canonically to the corresponding visible quotients.
4. **One invisible torsion relation.**  For a finite simple lamp, the entire approximation kernel is the normal closure of one nontrivial lamp element.  For \(A_5\) it may be chosen to be an involution.  Adding that single relation turns the group into the residually finite MF skeleton while preserving all the finite/compact/linear/corona target data in the dossier.
5. **Infinite invisible family.**  The groups \(W_n\) with alternating lamps \(A_n\) are pairwise noncommensurable but are indistinguishable by every approximation target functor computed here.  The hidden simple type is recovered only by looking inside the common residual itself.
6. **A four-dimensional rational visible envelope.**  For perfect lamps, one explicit homomorphism to \(\mathrm{GL}_4(\mathbb Q)\) has kernel equal to all five residuals, and its image is the same fixed group \(\Lambda\) for the entire infinite family.
7. **MF is an abstract-commensurability invariant.**  The finite-index induction construction proves both upward and downward permanence of MF.  Residual finiteness, MAP, and linearity over a specified field admit parallel finite-index proofs.  The concrete same-profinite pairs are nevertheless not abstractly commensurable.
8. **Restricted target non-conservativity.**  For perfect lamps the split quotient and the proper section are inverse equivalences on Hom-sets into every finite, residually finite, countable MF, compact, all-fields finite-dimensional linear, and norm-corona target used in the dossier, despite neither map being an isomorphism of groups.
9. **Hereditary target twins.**  The previous equivalence persists at every finite-index node: \(H=R_K\rtimes J\) is non-MF, \(J\) is MF, and \(H\twoheadrightarrow J\) preserves all of the same visible target theory, together with the finite-index and profinite data.
10. **Split-extension failure.**  The \(C_2\)-lamp example proves that MF is not closed under split extensions even with an elementary abelian locally finite residually finite amenable kernel and a residually finite linear quotient.  The same exact sequence witnesses split-extension failure for residual finiteness and MAP, and—using the explicit characteristic-two embedding of the lamp kernel—for linearity over some field.
11. **Radical non-heredity outside finite index.**  The common ambient radical \(R_K\) is itself locally finite and residually finite, so all five of its intrinsic residuals are trivial.  It nevertheless equals all five residuals of \(W_K\).  This makes the finite-index theorem sharp even among normal amenable subgroups.
12. **Exact non-finite-presentability.**  A direct free-permutational/graph-product proof shows that finite presentation would force finitely many diagonal pair-orbits; HNN height supplies infinitely many.  Thus every nontrivial finite-lamp witness is finitely generated but not finitely presented; finite-index invariance of finite presentability then shows that none is virtually finitely presented or commensurable with a finitely presented group.
13. **Same finite-index lattice does not imply commensurability.**  The alternating-lamp groups have mutually isomorphic, index-preserving finite-index subgroup lattices through the common quotient \(G_*\), yet are pairwise noncommensurable because every finite-index subgroup retains the lamp-type finite residual.

These are mathematical deductions proved in this note.  They are **not** asserted here as literature-priority claims.

### 54.5 The next possible finish lines

The proof now makes the remaining research frontier unusually concrete.

- **Finitely presented profinite/MF twins.**  The strongest next target is to replace the present finitely generated wreath groups by finitely presented groups while retaining a split quotient inducing the same profinite completion and opposite MF behavior.  This requires genuine presentation engineering; it does not follow formally from the current wreath construction.
- **Torsion-free invisible kernels.**  The current sharpest examples hide finite simple torsion in the common radical.  A torsion-free analogue would separate the compression mechanism from all finite-order witnesses and would connect directly to the repository's routing/small-cancellation program.
- **The unrestricted infinite-index HNN action problem.**  Sections 30--31 settle finite-index and UAS/LERA/LERF cases.  Soficity of \(G\curvearrowright G/\Gamma\) for an arbitrary sofic property-\((T)\) base with an arbitrary proper infinite-index self-embedding remains the clean action-theoretic gap.
- **A finitely presented full-MF-radical group.**  The formal saturation machinery shows what would follow from a routing construction with defect equal to the whole group.  Constructing such a concrete finitely presented group would produce an approximation "black hole" with no nontrivial MF quotient.
- **Formalize Sections 37 and 49--54.**  The analytic collapse core is already represented in Lean source.  The telescope iteration, finite-index induction, profinite-twin correspondence, fully invariant radical, invisible-family arguments, split-extension package, and graph-product finite-presentation obstruction are algebraic and are natural next formalization targets.
- **Engineer a finitely presented replacement around the proven obstruction.**  Theorem 54.5 shows that the present transitive wreath architecture fails finite presentability because height produces infinitely many double cosets.  Any finitely presented replacement must therefore alter the site action or encode the lamps by a different finite-presentation mechanism rather than merely streamline the existing presentation.
- **Push the invisible-kernel encoding principle.**  Perfect finite lamps already allow different finite simple types to be hidden behind the same visible quotient.  A next question is which finitely generated groups can occur as fully invariant approximation-invisible kernels while the MF/profinite/linear/Bohr-visible quotient is held fixed.
- **Common-field split-extension failure.**  The elementary abelian lamp kernel is linear in characteristic two and \(G_*\) is linear in characteristic zero.  It is natural to ask whether one can force both factors to be linear over one prescribed field while the split extension remains non-MF and nonlinear.
- **Two-generator and continuum-strength variants.**  The present examples prioritize transparent geometry and exact radical computation rather than minimal generation.  Compression/routing or embedding constructions could be used to ask for two-generator analogues, or continuum many mutually nonisomorphic hidden kernels behind one visible quotient, while preserving the target-equivalence phenomenon.

The crucial point is that none of these open directions is needed for any of the proved results in Section 54.  They are genuine next problems, not gaps in the proved chain above.

---

## Appendix A. Referee audit ledger

This appendix records the final audit of the dossier itself.  It is deliberately separate from the mathematical argument: none of the theorems above depends on these bookkeeping checks.

### A.1 Substantive defects found and repaired during the audit

The continuation/referee pass did not merely add consequences.  It found and corrected the following points.

1. **Norm corona versus subsequence.**  The historical finite-mover argument originally risked treating vanishing along a subsequence as vanishing in the ordinary quotient \(\prod M_{d_n}/\bigoplus M_{d_n}\).  Section 6 gives the counterexample and Section 7 replaces the invalid inference by simultaneous finite-block amplification.
2. **Wrong ambient object in the historical non-MF conclusion.**  An earlier draft accidentally said that the restricted direct-sum lamp subgroup was non-MF.  That is false: for finite lamps that subgroup is locally finite, hence amenable.  Theorem 7.2 now correctly concludes non-MF-ness of the **full ambient lamp-action group** containing the Kazhdan movers.
3. **Zero normalization scale.**  The max-mover proof now explicitly treats the case \(k_n=0\).  The zero-scale branch forces all corrected mover defects toward the identity, contradicting the simultaneous separation furnished by block amplification; only after this step is division by \(k_n\) used.
4. **Finite chart target in the amenable-action proof.**  The action-sofic definition requires a finite chart target.  Section 30.6 now takes
   \(B=\{a^{-1}y:a\in A,\ y\in E\}\), which is finite, instead of implicitly using the whole possibly infinite \(G\)-set.
5. **Finite-intersection closure for LERA.**  The dossier now proves that finite intersections of strongly co-amenable subgroups remain strongly co-amenable by embedding the corresponding core quotient into a finite product of amenable groups.  Thus the decreasing-sequence formulation is justified rather than assumed.
6. **Cyclic-extension error bookkeeping.**  The group and action proofs no longer use the shorthand \(O(Q/L)+o(1)\).  At most \(2Q\) of the \(L\) stack levels are boundary levels, and on every other level the defect is at most the chosen \(N\)-model error \(\delta\), giving the explicit bound \(2Q/L+\delta\).
7. **Generalized-wreath multiplication bookkeeping.**  Section 29.6 now uses exactly three bad sets.  Their total proportion is \(<3\varepsilon_i\), and outside them the lamp-coordinate identity is exact.
8. **HNN linear embedding compatibility.**  Section 39.7 now writes the intertwining identity
   \(D j[(\gamma,n)]D^{-1}=j[(\gamma,n-1)]\) for \(n\ge1\), with the \(n=0\) case equal to the defining relation \(D\gamma D^{-1}=\alpha(\gamma)\).  The semidirect-product homomorphism is therefore established before the determinant argument proves injectivity.
9. **TeX escape corruption.**  A malformed `\\ne1` sequence in the finite-lamp defect formula was repaired to the intended \(\ne1\).  A targeted scan found no remaining isolated fragments of that kind.
10. **Formal-verification wording.**  The file no longer equates “Lean source exists” with a fresh kernel execution or an observed hosted-CI success.  Section 44 states the exact evidence boundary.
11. **Terminal escape/count synchronization.**  After the last theorem additions, a raw carriage-return/tab escape introduced while editing `\rtimes` / `\twoheadrightarrow` was detected at byte level and repaired.  The duplicate equation tag `49.15` was also split into `49.15` and `49.16`, and the appendix counts below were recomputed from the final file rather than copied from an earlier checkpoint.

### A.2 Mechanical integrity checks

After the substantive repairs, the final file was checked programmatically for structural consistency.  At the time of this audit:

- the numbered mathematical sections run continuously from **0 through 54**, with no missing or duplicate section number;
- all **290** displayed equation tags are unique;
- every numeric parenthetical equation reference appearing in the text resolves to an existing tag;
- all true TeX display delimiters `\\[` / `\\]` are balanced (array line breaks such as `\\\\[1mm]` are distinguished from display delimiters);
- every `\\begin{...}` environment has a matching `\\end{...}`;
- fenced code blocks are balanced;
- there are no ASCII control characters, tab characters, or carriage returns in the Markdown source;
- a CommonMark/Markdown-It parse succeeds;
- targeted searches outside this audit discussion find none of the superseded assertions: a non-MF claim about the lamp subgroup alone, an asserted hosted-CI success, or an asserted independent Lean rerun.

These are syntax and consistency checks, not substitutes for mathematical proof; their purpose is to prevent a correct argument from being damaged by a malformed artifact.

### A.3 Final proof-status boundary

The strongest claims of the dossier fall into three evidence layers.

- **Project-specific mathematics proved in this file:** the metric bridges, corona repair, HNN/Følner/telescope calculations, the finite-index and UAS action arguments, the generalized-wreath reconstruction, the exact telescope radical, the all-fields linear residual, the universal factorization theorems, finite-index induction of radicals, MF commensurability invariance, restricted-target equivalence, the hereditary finite-index twin tower, the split-extension failure package, sharp arbitrary-subgroup radical non-heredity, the graph-product proof of non-finite-presentability, and the finite-action/profinite-twin consequences.
- **Project-specific analytic endpoint also backed by formal source:** involutive compression collapse and its projection/torsion consequences, together with the explicit affine property-\((T)\) certificate chain.  The audited source is premise-free at the theorem boundary and contains no `sorry` or declared `axiom` in the relevant project modules; this session did not independently execute Lean.
- **Named classical or published inputs:** basic Hilbert-space/property-\((T)\) facts where stated, Zariski's lemma, Peter--Weyl, and the primary-source context from Monod--Popa, Gao, Gao--Kunnawalkam Elayavalli--Patchell, and Kun--Thom.  Their use is identified at the point where it enters.

The remaining general question is intentionally not promoted to a theorem: for an arbitrary sofic property-\((T)\) base and an arbitrary proper infinite-index self-embedding, soficity of the specific ascending-HNN coset action is not proved here.  Finite-index and UAS/LERA/LERF cases are proved; the unrestricted case remains the clean action-theoretic frontier.

### A.4 Final referee verdict

Within the stated evidence boundary, the resulting chain is now internally consistent:

- the historical condition-(iii) discussion is correct at the non-MF level after the corona repair;
- the current compression theorem supplies the stronger fixed-element radical statement needed by the HNN construction;
- the collapse iterates to a completely explicit quotient;
- in the concrete affine family that quotient is residually finite and MF, so the radical is computed exactly;
- the same explicit kernel is simultaneously the MF, finite-dimensional-unitary, all-fields-linear, Bohr, and finite residual;
- for perfect finite lamps, quotienting by that kernel produces an explicit residually finite MF group with the same finite actions, finite-index subgroup lattice, profinite completion, Bohr compactification, and finite-dimensional representation categories as the original sofic non-MF group;
- the quotient and its proper section are inverse equivalences on all target Hom-sets in the restricted target family, and this equivalence persists at every finite-index node while the MF status remains opposite;
- MF is proved to be an abstract-commensurability invariant, yet the split \(C_2\)-lamp exact sequence shows that MF is not closed under split extensions, even with a locally finite elementary abelian residually finite amenable kernel and a residually finite linear quotient;
- the common ambient radical is itself locally finite, residually finite, amenable, and MF, so the finite-index radical formula provably fails for arbitrary normal subgroups;
- the finite-presentation question for the displayed wreath examples is closed: height gives infinitely many double cosets and the graph-product argument forces non-finite-presentability.

No stronger conclusion is asserted where the proof currently stops.
