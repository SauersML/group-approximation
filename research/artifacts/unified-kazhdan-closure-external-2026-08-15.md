# 2026-08-15 — External note: the unified Kazhdan-projection compression closure

Source: user-supplied external draft (unrefereed, paper-level proofs, explicitly
not Lean-translated by its author), pasted 2026-08-15 into the P13 session.
This is a DIFFERENT document from
`unified-mf-compression-external-2026-08-15.md` (that file audits a companion
note with theorem numbers 4.1/6.1/6.2/13.1/14.1; this one is the follow-up
unification with Theorems 1–11).  NOT yet audited by this session — the P13
completeness build is the critical path here.  Routing into the graph belongs
to the compression-collapse lane.

Transcription note: the paste mangled some displayed equations — rows of
`===`/`---` inside display math are markdown-rendered `=`/`-` alignment
artifacts of the original equalities, not content.  Read `X ==== Y` as `X = Y`.

Status: literature-transcription-grade input (LITERATURE_INPUT gate applies if
anything below is cited before in-repo verification).

Summary of the claimed structure (my reading, for the index):

1. **Theorem 1 (master lemma)**: in any *finite* unital C*-algebra A
   (isometries are unitaries — includes norm matrix coronas and ultraproducts
   of matrix algebras, via polar correction of approximate isometries), the
   Kazhdan projection p_L of a property-(T) subgroup L ≤ H under ρ : H → U(A)
   satisfies: (1) sLs⁻¹ ≤ L ⟹ ρ(s) p_L ρ(s)* = p_L (equivalent projections
   with p ≤ q are equal in a finite algebra, via the isometry
   w = v* + (1−q)); (2) L ⊴ H ⟹ p_L ∈ ρ(H)'; (3) p_L = 1 ⟹ ρ(L) = 1.
2. **Theorem 2 / Corollary 3**: one-sided matricial Mautner equality — for
   operator-norm asymptotic representations, U_ω(s) preserves the L-fixed
   subspace of the Hilbert ultraproduct, at EVERY weight w_n on
   Tr(y*x)/w_n; normalized-HS transport (w_n = d_n) and rank-normalized
   collapse (w_n = r_n) are literally the same theorem.
3. **Theorem 4**: the whole intrinsic tracial compression defect
   𝔇₂(H,L) = ⟨⟨[gzg⁻¹, ℓ] : g ∈ Comp_H(L), z ∈ C_H(L), ℓ ∈ L⟩⟩_H is
   universally tracially invisible (‖U_n(x) − 1‖₂ → 0), via the normal
   subgroup N₂(U) and Corollary 3.
4. **Theorem 5 (normal-Kazhdan extraction)**: K ⊴ H, K property (T),
   K universally tracially invisible ⟹ K ≤ Rad_MF(H).  Proof: corona
   Kazhdan projection is central by normality; the complementary corner
   qQq carries a trace τ = lim_ω tr_{r_n}; no K-fixed vectors in GNS ⟹ a
   Kazhdan-pair 2-norm gap (14)–(15), contradicting invisibility.  Subsumes
   the sign corner (ε = u², Clifford only proves ε ≠ 1), the finite Reynolds
   corner, and the moving-corner proof.
5. **Theorem 7 (projection-orbit collapse — torsion-free!)**: p ∈ Q a
   projection commuting with π(sLs⁻¹), with pairwise-commuting L-orbit ⟹
   [p, π(L)] = 0.  Engine: exact commuting projection lifts (inductive joint
   spectral-block compression + spectral rounding), rank pseudometric
   d_n(λ,μ) = rank(P_λ,n − P_μ,n) = Hamming distance (commuting!),
   eventual translation invariance by 0/1-singular-value rigidity,
   self-normalized scale r_n = Σ_{a∈S} d_n(1,a), the class
   c(λ) = [(P_λ,n − P_1,n)] is an exact 1-cocycle in the r_n-weighted
   ultraproduct (rank-subadditivity kills the defect: Tr(M*M) ≤ rank·‖M‖²),
   property-(T) FH gives a coboundary, w is sLs⁻¹-fixed, Theorem 2 transports
   u = σ(s)*w back, contradiction with ‖c‖ = 1 normalization (32).
   ⚠ FH input: this is the same affine-fixed-point hypothesis the program
   keeps gated (see compression-collapse memory) — the gate applies here too.
6. **Theorem 8 / Corollary 9**: projection-generated packets B ⊆ Q with
   commuting orbits lie in π(L)'; zero-dimensional spectrum ⟹ collapse;
   finite spectrum, finite order, involutions (m = 2) are strictly special
   cases — "no analytically distinguished value of m".
7. **Theorem 10 (component confinement)**: ‖v_λ − v‖ ≤ sup of diameters of
   connected components of σ(v) — Kazhdan compression cannot move the clopen
   part of the spectrum; only motion inside connected components survives.
   Explains why finite-order lamps die and slow infinite-order phases escape
   (the two branches are a real boundary, not proof inelegance).
8. **§9–11 (the closure)**: 𝔎(H,L) (normal-(T) pieces of 𝔇₂) and
   𝔓(H;L,s) (discrete commuting witnesses) generate Δ_comp(H) ≤ Rad_MF(H);
   transfinite quotient iteration N_{α+1} = q_α⁻¹(Δ_comp(H/N_α)) stabilizes
   at Cl_comp(H) ≤ Rad_MF(H), with equality iff H/Cl_comp is MF (radical
   identity Rad_MF(H) = q⁻¹(Rad_MF(H/N)) for N ≤ Rad_MF(H)).  Semantic
   form: the MF-root closure operator ᴹᶠ√N on normal subgroups of the free
   group; G is MF iff ⟨⟨R⟩⟩ is MF-radical-closed; compression rigidity is a
   calculus for deriving MF-semantic consequences of relations (65).
9. **Program-level reframe (§12–13)**: two extraction regimes fed by one
   Kazhdan-projection engine — (normal rigid corner) and (discrete
   self-normalizing rank) — feeding the same closure; the research problem
   becomes "when is Cl_comp(G) = Rad_MF(G)?", replacing witness-hunting.

Full verbatim text follows.

---

Yes. I think there is now a genuine unified theorem, and the right starting
point is **not** a marked word.

The clean common engine is a Kazhdan projection in a finite C*-target. From
that one statement you get arbitrary-scale transport, the entire
Hilbert–Schmidt compression defect, the normal-Kazhdan upgrade, and — after
one additional cocycle argument — a projection-orbit collapse theorem that
subsumes involutions, finite-order lamps, finite spectrum, zero-dimensional
spectrum, and projection-generated packets.

What follows is a paper-level proof. I am deliberately not translating it
into Lean.

# 1. The exact master lemma

Call a unital C*-algebra A **finite** if every isometry in A is unitary.

Every norm matrix corona Q = ∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ) is finite.
The same is true of every norm ultraproduct ∏_ω M_{d_n}(ℂ), and of
∏_ω B(H_n) when every H_n is finite-dimensional.

Indeed, suppose x*x = 1 in such a quotient. Choose lifts x_n. Then
‖x_n* x_n − 1‖ → 0. Eventually x_n* x_n is invertible, hence x_n is
invertible because it is square. Its polar correction
u_n = x_n (x_n* x_n)^{−1/2} is unitary and satisfies ‖u_n − x_n‖ → 0.
Thus x = [u_n] is unitary.

That elementary observation is the cancellation principle we need.

## Theorem 1 — Kazhdan projection calculus in finite targets

Let A be a finite unital C*-algebra, let ρ : H → U(A) be a group
homomorphism, and let L ≤ H have property (T).

There is a canonical projection p_L ∈ A, obtained from the Kazhdan
projection of L, with the following properties.

If s L s⁻¹ ≤ L, then

    ρ(s) p_L ρ(s)* = p_L.                                   (1)

If instead L ⊴ H, then

    p_L ∈ ρ(H)'.                                            (2)

Finally,

    p_L = 1  ⟹  ρ(L) = 1.                                   (3)

### Proof

Choose a finite symmetric generating Kazhdan set S ⊂ L with Kazhdan
constant κ > 0. In C*_max(L), put

    T = (1/|S|) Σ_{s∈S} s,     a = (1 + T)/2.

Because S = S⁻¹, T = T*, and a is a positive contraction.

Consider any unitary representation π : L → U(𝓗). On 𝓗^L, π(a) = 1.
On its orthogonal complement, if ‖ξ‖ = 1, some s ∈ S satisfies
‖π(s)ξ − ξ‖ ≥ κ. Hence 2 − 2 Re⟨π(s)ξ, ξ⟩ ≥ κ², so
Re⟨π(s)ξ, ξ⟩ ≤ 1 − κ²/2. All the other summands have real part at most 1,
and therefore ⟨π(T)ξ, ξ⟩ ≤ 1 − κ²/(2|S|). Consequently
⟨π(a)ξ, ξ⟩ ≤ 1 − δ, δ = κ²/(4|S|) > 0.

Thus, uniformly over all unitary representations,
sp(π(a)) ⊂ [0, 1−δ] ∪ {1}.

It follows that aⁿ converges in the maximal C*-norm to a projection
p ∈ C*_max(L), and in every unitary representation π, π(p) is exactly the
orthogonal projection onto 𝓗^L. This is the Kazhdan projection.

Let p_L denote its image in A.

Represent A faithfully on a Hilbert space 𝓚. Then p_L projects onto the
vectors fixed by ρ(L).

Suppose first that s L s⁻¹ ≤ L. The projection q = ρ(s) p_L ρ(s)*
projects onto the vectors fixed by ρ(s L s⁻¹). Since s L s⁻¹ ≤ L, every
L-fixed vector is s L s⁻¹-fixed. Hence p_L ≤ q. But q is unitarily
equivalent to p_L.

In a finite C*-algebra an equivalent projection cannot properly contain
the original projection. For completeness, if p ≤ q and q = u p u*, put
v = u p, so v*v = p, v v* = q. Then w = v* + (1 − q) satisfies w*w = 1,
w w* = p + (1 − q). Thus w is an isometry. Finiteness makes it unitary,
hence p + (1 − q) = 1, so p = q. This proves (1).

If L ⊴ H, then for every h ∈ H, h L h⁻¹ = L. Thus ρ(h) p_L ρ(h)* and p_L
are both the projections onto the same L-fixed subspace. Hence they are
equal, proving (2).

Finally every ℓ ∈ L satisfies ρ(ℓ) p_L = p_L. If p_L = 1, then ρ(ℓ) = 1
for every ℓ ∈ L. ∎

That is the common core. There is no sign in it. There is no
Hilbert–Schmidt norm in it. There is no finite-order element. There is no
Clifford algebra.

# 2. Arbitrary-scale Kazhdan transport is a corollary

## Theorem 2 — One-sided matricial Mautner equality at every scale

Let U_n : H → U(𝓚_n) be an operator-norm asymptotic representation on
finite-dimensional Hilbert spaces: ‖U_n(gh) − U_n(g)U_n(h)‖ → 0 for every
fixed g, h ∈ H.

Fix a free ultrafilter ω. Let 𝓚_ω = ∏_ω 𝓚_n be the Hilbert ultraproduct,
and let U_ω : H → U(𝓚_ω) be the induced exact representation.

If L ≤ H has property (T) and s L s⁻¹ ≤ L, then

    𝓚_ω^L = U_ω(s) 𝓚_ω^L.                                   (4)

Thus U_ω(s) and U_ω(s)* preserve the L-fixed subspace.

### Proof

The operators U_n(g) determine a homomorphism H → U(∏_ω B(𝓚_n)). The
norm ultraproduct A_ω = ∏_ω B(𝓚_n) is finite by the polar-correction
argument above. Apply Theorem 1 to A_ω. Its Kazhdan projection p_L acts
on 𝓚_ω as the orthogonal projection onto 𝓚_ω^L, and (1) says
U_ω(s) p_L U_ω(s)* = p_L. Hence U_ω(s) preserves its range. ∎

Now put arbitrary weights into the Hilbert structure. Let w_n > 0, and
take 𝓚_n = M_{d_n}(ℂ) with ⟨x, y⟩_{n,w} = Tr(y*x)/w_n.        (5)

Conjugation by a unitary is still a unitary operator on this Hilbert
space, irrespective of w_n. Therefore:

## Corollary 3 — Weighted transport

Suppose U_n : H → U(d_n) is operator-norm asymptotically multiplicative,
L has property (T), and s L s⁻¹ ≤ L. Let x_n ∈ M_{d_n} satisfy
sup_n Tr(x_n* x_n)/w_n < ∞. If, for every ℓ ∈ L,

    Tr|U_n(ℓ) x_n U_n(ℓ)* − x_n|² / w_n → 0,               (6)

then

    Tr|U_n(ℓ) U_n(s) x_n U_n(s)* U_n(ℓ)* − U_n(s) x_n U_n(s)*|² / w_n → 0   (7)

for every ℓ ∈ L. The same holds with s replaced by s⁻¹.

### Proof

If (7) failed on a subsequence, choose an ultrafilter containing that
subsequence. Condition (6) says that the class x = [x_n] in the weighted
Hilbert ultraproduct is L-fixed. Theorem 2 says U_ω(s) x is also L-fixed,
contradicting the chosen failure of (7). ∎

This is important because the usual normalized Hilbert–Schmidt transport
and the rank-normalized collapse theorem are **literally the same
theorem**. For normalized Hilbert–Schmidt norm, take w_n = d_n. For a
defect supported on a rank-r_n sector, take w_n = r_n. There is no
conceptual distinction.

# 3. The entire intrinsic compression defect is universally tracially invisible

Let Comp_H(L) = ⟨ g ∈ H : g L g⁻¹ ≤ L ⟩. Define

    𝔇₂(H, L) = ⟨⟨ [g z g⁻¹, ℓ] : g ∈ Comp_H(L), z ∈ C_H(L), ℓ ∈ L ⟩⟩_H.   (8)

The subscript 2 is only mnemonic: this is the subgroup that compression
forces to disappear in normalized 2-norm.

## Theorem 4 — Universal tracial collapse

If L ≤ H has property (T), then for every operator-norm asymptotic
representation U_n : H → U(d_n) and every x ∈ 𝔇₂(H, L), one has

    ‖U_n(x) − 1‖_{2, d_n} → 0.                              (9)

### Proof

Put N₂(U) = { h ∈ H : ‖U_n(h) − 1‖₂ → 0 }. Asymptotic multiplicativity
and unitary invariance imply that N₂(U) is a normal subgroup. Indeed, if
a, b ∈ N₂(U),

    ‖U_n(ab) − 1‖₂ ≤ ‖U_n(ab) − U_n(a)U_n(b)‖
                    + ‖U_n(a)(U_n(b) − 1)‖₂ + ‖U_n(a) − 1‖₂ → 0.

Likewise inverses and conjugates remain in N₂(U).

Now let z ∈ C_H(L). Since z ℓ = ℓ z,
‖U_n(ℓ) U_n(z) U_n(ℓ)* − U_n(z)‖ → 0 for each ℓ ∈ L. Hence U_n(z),
viewed in the Hilbert space M_{d_n} with normalized Hilbert–Schmidt norm,
is asymptotically L-fixed.

By Corollary 3, conjugating this sequence by any one-sided compressor
preserves L-invariance in normalized 2-norm. Because the equality of
fixed spaces is two-sided, the same is true for every element of the
group generated by the one-sided compressors.

Therefore, for every g ∈ Comp_H(L), the sequence representing g z g⁻¹
asymptotically commutes with the sequence representing every ℓ ∈ L in
normalized Hilbert–Schmidt norm. Consequently [g z g⁻¹, ℓ] ∈ N₂(U).
Since N₂(U) ⊴ H, it contains the normal closure of all these
commutators. Thus 𝔇₂(H, L) ≤ N₂(U). This is exactly (9). ∎

This is the entire "u →₂ 1" phenomenon, stripped of u. There is a whole
normal subgroup that disappears.

# 4. The strongest clean upgrade: normal property-(T) pieces actually lie in the MF radical

Call D ≤ H **universally tracially invisible** if every operator-norm
asymptotic representation U_n of H satisfies ‖U_n(d) − 1‖₂ → 0 for
d ∈ D.                                                       (10)

## Theorem 5 — Normal-Kazhdan extraction

Let H be countable. Let D ≤ H be universally tracially invisible.
Suppose K ⊴ H, K ≤ D, and K has property (T). Then

    K ≤ Rad_MF(H).                                          (11)

Equivalently every homomorphism π : H → U(Q) to every norm matrix corona
kills K elementwise.

### Proof

Assume otherwise. Then there is a norm matrix corona Q and a
homomorphism π : H → U(Q) such that π(K) ≠ 1.

Let Φ : C*_max(K) → Q be the C*-homomorphism extending π|_K. Let
p_K ∈ C*_max(K) be the Kazhdan projection and write p = Φ(p_K),
q = 1 − p. Because K ⊴ H, Theorem 1 gives p ∈ π(H)'.          (12)

Moreover q ≠ 0. Indeed, if p = 1, then for every k ∈ K,
π(k) = π(k) p = p = 1, contrary to π(K) ≠ 1.

Since q commutes with π(H), π_q(h) = q π(h) q is a homomorphism from H
into the unitary group of the corner q Q q, whose identity is q.

Lift q to coordinate projections q_n. Because q ≠ 0, infinitely many q_n
are nonzero. Choose a free ultrafilter ω concentrated on those indices
and put r_n = rank q_n. The normalized matrix traces on
q_n M_{d_n} q_n ≅ M_{r_n} define a tracial state
τ(x) = lim_ω tr_{r_n}(x_n) on q Q q.                         (13)

Consider its GNS Hilbert space L²(qQq, τ). The corner representation
gives a unitary representation of K by left multiplication. What is its
Kazhdan projection? The image of p_K in the corner is q p q = 0.
Therefore the K-fixed subspace of the GNS representation is zero.

Take a Kazhdan pair (S, κ) for K. The vector q ∈ L²(qQq, τ) has norm 1.
Because there are no nonzero K-fixed vectors, there exists s ∈ S such
that ‖π_q(s) − q‖_{2,τ} ≥ κ.                                 (14)

Now choose coordinate unitary lifts V_n(h) ∈ U(q_n M_{d_n} q_n) of the
corner representation. They form an operator-norm asymptotic
representation of H. Equation (14) says
lim_ω ‖V_n(s) − 1_{q_n}‖_{2, r_n} ≥ κ.                       (15)

But s ∈ K ≤ D, and D is universally tracially invisible. Hence for this
very corner approximation, ‖V_n(s) − 1_{q_n}‖_{2, r_n} → 0,
contradicting (15). Thus no corona homomorphism can be nontrivial on
K. ∎

## Corollary 6 — Intrinsic normal-Kazhdan radical

From Theorems 4 and 5:

    K ⊴ H, K property (T), K ≤ 𝔇₂(H, L)  ⟹  K ≤ Rad_MF(H).   (16)

This contains the previous special cases. If F ⊴ H is finite and
F ≤ 𝔇₂(H, L), then F has property (T), so F ≤ Rad_MF(H). Thus the
Reynolds theorem is a finite special case.

If ε ∈ Z(H), ε^m = 1, ε ∈ 𝔇₂(H, L), then ⟨ε⟩ ⊴ H is finite, hence
ε ∈ Rad_MF(H). In particular, if one happens to manufacture
u ∈ 𝔇₂(H, L), ε = u², ε² = 1, ε ∈ Z(H), the entire analytic sign proof
reduces to one sentence: ⟨ε⟩ ≤ 𝔇₂(H, L) ⟹ ε ∈ Rad_MF(H). The Clifford
algebra is only a way to prove ε ≠ 1.

# 5. The other branch: projections collapse

The normal-Kazhdan theorem does not encompass commuting lamp collapse.
It should not: an infinite elementary abelian lamp orbit need not itself
be Kazhdan. But the involution theorem is still not the right fundamental
statement. The right object is a **projection in the corona**.

## Theorem 7 — Projection-orbit collapse

Let H be countable, let L ≤ H have property (T), let s L s⁻¹ ≤ L, and
let π : H → U(Q) be a homomorphism to a norm matrix corona.

Let p ∈ Q be a projection satisfying [p, π(s L s⁻¹)] = 0,      (17)
and suppose its L-orbit p_λ = π(λ) p π(λ)*, λ ∈ L, is pairwise
commuting: [p_λ, p_μ] = 0 for λ, μ ∈ L.                       (18)

Then

    [p, π(L)] = 0.                                          (19)

This theorem contains no torsion whatsoever.

### Proof

Assume that (19) fails. Then for some γ₀ ∈ L, p_{γ₀} ≠ p.     (20)

Choose unitary coordinate lifts U_n(g) ∈ U(d_n) of π(g). They form an
operator-norm asymptotic representation. We need exact commuting lifts
of the projections p_λ.

**Exact commuting projection lifts.** Enumerate the countable family
{p_λ : λ ∈ L}. We claim that there are projections P_{λ,n} ∈ M_{d_n}
such that [P_{λ,n}, P_{μ,n}] = 0 for all λ, μ, n, and P_{λ,n} lifts
p_λ.

Construct them inductively. Suppose P_{1,n}, …, P_{j−1,n} have been
constructed. Their joint Boolean algebra has finitely many orthogonal
joint spectral projections e_{α,n}, Σ_α e_{α,n} = 1. Take any
self-adjoint lift X_{j,n} of the next corona projection p_j and put
Y_{j,n} = Σ_α e_{α,n} X_{j,n} e_{α,n}.                        (21)

Then Y_{j,n} commutes exactly with all previously constructed
projections. Because p_j commutes in the quotient with all earlier p_i,
equation (21) still represents p_j. Hence ‖Y_{j,n}² − Y_{j,n}‖ → 0.
Spectral rounding at 1/2 gives a genuine projection P_{j,n} representing
the same corona element and still commuting with the previous
projections. Proceeding through the enumeration proves the claim.

Since π(g) p_λ π(g)* = p_{gλ}, we have covariance

    ‖U_n(g) P_{λ,n} U_n(g)* − P_{gλ,n}‖ → 0                 (22)

for every fixed g, λ ∈ L.

Define d_n(λ, μ) = rank(P_{λ,n} − P_{μ,n}).                   (23)

Because all the P_{λ,n} commute, they are simultaneously diagonalizable,
so d_n is simply Hamming distance between their 0/1 labels. Therefore it
is a pseudometric. Moreover Tr|P_{λ,n} − P_{μ,n}|² = d_n(λ, μ).  (24)

Equation (22) implies eventual translation invariance:
d_n(gλ, gμ) = d_n(λ, μ)                                       (25)
for every fixed triple g, λ, μ, once n is large enough. To see this, the
matrices U_n(g)(P_{λ,n} − P_{μ,n})U_n(g)* and P_{gλ,n} − P_{gμ,n} are
asymptotically equal in operator norm. Each has singular values only 0
and 1. Once their distance is less than 1/2, the number of singular
values equal to 1 must agree, hence their ranks agree.

Now choose a finite symmetric generating Kazhdan set S ⊂ L, and define
r_n = Σ_{a∈S} d_n(1, a).                                      (26)

If λ = a₁⋯a_m is an S-word, the triangle inequality and (25) give
eventually

    d_n(1, λ) ≤ Σ_{j=1}^m d_n(a₁⋯a_{j−1}, a₁⋯a_j)
              = Σ_{j=1}^m d_n(1, a_j) ≤ m · r_n.             (27)

Because of (20), the corona element p_{γ₀} − p is nonzero. For commuting
projections its lift has operator norm either 0 or 1. Therefore along an
infinite set of indices, d_n(1, γ₀) > 0. By (27), after passing to a
subsequence we may assume r_n ≥ 1 for every n.                (28)

Now define the Hilbert space 𝓗_n = M_{d_n}(ℂ) with the rescaled inner
product ⟨X, Y⟩_n = Tr(Y*X)/r_n.                               (29)

Let ω be a free ultrafilter and let 𝓗_ω = ∏_ω 𝓗_n. Conjugation by the
U_n(g)'s induces an exact unitary representation
σ : H → U(𝓗_ω).                                              (30)

For λ ∈ L, set c(λ) = [(P_{λ,n} − P_{1,n})]_n.                (31)

By (24) and (27), ‖c(λ)‖² = lim_ω d_n(1, λ)/r_n ≤ |λ|_S, so c(λ) is
well-defined. Furthermore

    Σ_{a∈S} ‖c(a)‖² = lim_ω (Σ_{a∈S} d_n(1, a))/r_n = 1.     (32)

Thus c is nonzero.

We next prove that c is a genuine 1-cocycle for σ|_L. Fix a, λ ∈ L.
Consider

    M_n = (P_{aλ,n} − P_{1,n}) − (P_{a,n} − P_{1,n})
          − U_n(a)(P_{λ,n} − P_{1,n})U_n(a)*.                (33)

Rearranging,

    M_n = (P_{aλ,n} − U_n(a) P_{λ,n} U_n(a)*)
        + (U_n(a) P_{1,n} U_n(a)* − P_{a,n}).                (34)

By covariance, ‖M_n‖ → 0.                                     (35)

On the other hand, from (33) and rank subadditivity,

    rank M_n ≤ d_n(1, aλ) + d_n(1, λ) + d_n(1, a) ≤ C_{a,λ} r_n   (36)

for a constant C_{a,λ} independent of n. For every matrix M,
Tr(M*M) ≤ rank(M) ‖M‖².                                       (37)
Hence Tr(M_n* M_n)/r_n ≤ C_{a,λ} ‖M_n‖² → 0.                  (38)

Thus (33) becomes an exact identity in 𝓗_ω:

    c(aλ) = c(a) + σ(a) c(λ).                               (39)

So c is a 1-cocycle. Property (T) has the fixed-point property for
affine isometric Hilbert actions. Therefore every 1-cocycle is a
coboundary. There exists w ∈ 𝓗_ω such that
c(λ) = σ(λ) w − w.                                            (40)

Now put L₁ = s L s⁻¹. Assumption (17) says p_h = p for h ∈ L₁. Since
P_{h,n} and P_{1,n} are commuting projections representing the same
corona projection, ‖P_{h,n} − P_{1,n}‖ → 0. Their difference has norm
either 0 or 1, so eventually P_{h,n} = P_{1,n}. Thus c(h) = 0 for
h ∈ L₁. By (40), σ(h) w = w for h ∈ L₁.                       (41)

Define u = σ(s)* w. For λ ∈ L,

    σ(λ) u = σ(λ) σ(s)* w = σ(s)* σ(s λ s⁻¹) w = σ(s)* w = u,

because s λ s⁻¹ ∈ L₁ and w is L₁-fixed. Hence u ∈ 𝓗_ω^L.      (42)

But 𝓗_ω is exactly a finite-dimensional Hilbert ultraproduct of the
kind covered by Theorem 2. Therefore one-sided compression gives
σ(s) 𝓗_ω^L = 𝓗_ω^L. Since u is L-fixed, w = σ(s) u is also L-fixed.
Equation (40) now gives c(λ) = 0 for λ ∈ L, contradicting (32).

Therefore the assumption (20) was impossible: p_λ = p for λ ∈ L. That
proves (19). ∎

This is, I think, the correct fundamental theorem behind the entire
commuting-torsion branch. It says nothing about torsion. It says: a
commuting orbit of projections cannot acquire new directions across a
one-sided Kazhdan compression.

# 6. Projection-generated algebras collapse pointwise

## Theorem 8 — Projection-generated packet collapse

Keep H, L, s, π as above. Let B ⊆ Q be a unital C*-subalgebra such that
[B, π(s L s⁻¹)] = 0.                                          (43)
Assume that for every projection p ∈ B, the projections
π(λ) p π(λ)*, λ ∈ L, commute pairwise. If B is generated as a
C*-algebra by its projections, then

    B ⊆ π(L)'.                                              (44)

### Proof

Every projection p ∈ B satisfies Theorem 7, so [p, π(L)] = 0. Thus π(L)
commutes with every projection in B. Since those projections generate B,
it commutes with all of B. ∎

This includes finite-dimensional C*-packets, AF packets under the
orbit-commutation hypothesis, and more generally any unital
projection-generated packet. The packet itself need not be abelian.

# 7. Finite spectrum is only a corollary

Let v ∈ U(Q), suppose [v, π(s L s⁻¹)] = 0, and suppose the conjugates
v_λ = π(λ) v π(λ)* commute pairwise. If C*(v) is generated by
projections, Theorem 8 gives v_λ = v. For a unitary, C*(v) ≅ C(σ(v)).
If σ(v) is zero-dimensional, C(σ(v)) is generated by characteristic
functions of clopen sets. Hence:

## Corollary 9 — Zero-dimensional spectral collapse

If σ(v) is zero-dimensional, then v_λ = v for λ ∈ L.          (45)

Finite spectrum is a special case. Finite order is therefore a still
smaller special case. If k ∈ H satisfies k^m = 1, [k, s L s⁻¹] = 1, and
[λ k λ⁻¹, μ k μ⁻¹] = 1 for λ, μ ∈ L,                          (46)
then in every corona representation π(λ k λ⁻¹) = π(k). Thus

    [λ, k] ∈ Rad_MF(H) for λ ∈ L.                            (47)

The old involution theorem is simply m = 2. There is no analytically
distinguished value of m.

# 8. What survives when the spectrum is not zero-dimensional

## Theorem 10 — Spectral-component confinement

Under the preceding hypotheses on v, for every λ ∈ L,

    ‖v_λ − v‖ ≤ sup_{C ∈ π₀(σ(v))} diam(C),                  (48)

where C ranges over connected components of the spectrum.

### Proof

Let E ⊆ σ(v) be clopen. Then p_E = 1_E(v) is a projection. Its orbit is
π(λ) p_E π(λ)* = 1_E(v_λ), and these projections commute because the
v_λ's commute. Theorem 7 therefore gives 1_E(v_λ) = 1_E(v)     (49)
for every clopen E.

Fix λ. Since v and v_λ commute, A = C*(v, v_λ) is abelian. Let X = Â.
For x ∈ X, write z = v(x), z' = v_λ(x). Equation (49) gives
1_E(z) = 1_E(z') for every clopen E ⊆ σ(v). Thus z and z' cannot be
separated by any clopen subset of σ(v). They belong to the same
quasi-component. Since σ(v) is a compact metric space, its
quasi-components are its connected components. Hence
|z − z'| ≤ sup_{C} diam(C). Taking the supremum over x ∈ X gives
(48). ∎

So the sharp message is not "torsion collapses." It is: Kazhdan
compression cannot move the clopen part of the spectrum. The only
possible motion is inside connected spectral components. That precisely
explains why finite-order lamps collapse and slowly varying
infinite-order phases can escape.

# 9. The unified compression radical

For each property-(T) subgroup L ≤ H, define its tracial compression
defect 𝔇₂(H, L) by (8). Let

    𝔎(H, L) = ⟨ K : K ⊴ H, K has (T), K ≤ 𝔇₂(H, L) ⟩.        (50)

By Theorem 5, 𝔎(H, L) ≤ Rad_MF(H).                            (51)

For a specific compressor s L s⁻¹ ≤ L, let 𝒲_disc(H; L, s) be the
collection of all finite-order k ∈ H satisfying (46), and put

    𝔓(H; L, s) = ⟨⟨ [λ, k] : λ ∈ L, k ∈ 𝒲_disc(H; L, s) ⟩⟩_H.  (52)

By Corollary 9, 𝔓(H; L, s) ≤ Rad_MF(H).                       (53)

Now take the subgroup generated by all such consequences over all
Kazhdan compression pairs in H:

    Δ_comp(H) = ⟨ 𝔎(H, L), 𝔓(H; L, s) :
                  L ≤ H has (T), s L s⁻¹ ≤ L ⟩.              (54)

Then Δ_comp(H) ≤ Rad_MF(H).                                   (55)

This is already a witness-free obstruction theorem. But one should
iterate it.

# 10. Quotient iteration is part of the theorem

Define N₀ = 1. If N_α is defined, let q_α : H → H/N_α and put
N_{α+1} = q_α⁻¹(Δ_comp(H/N_α)).                               (56)
At a limit ordinal λ, put N_λ = ∪_{α<λ} N_α.                  (57)

## Theorem 11 — Compression closure stays inside the MF radical

For every ordinal α, N_α ≤ Rad_MF(H).                         (58)
The chain stabilizes at a countable ordinal. Let its stable value be
Cl_comp(H). Then Cl_comp(H) ≤ Rad_MF(H).                      (59)
If H/Cl_comp(H) is MF, then Cl_comp(H) = Rad_MF(H).           (60)
If Cl_comp(H) = H, then every homomorphism from H to every MF group is
trivial.

### Proof

We use the following elementary radical identity. If N ≤ Rad_MF(H) and
q : H → H/N, then

    Rad_MF(H) = q⁻¹(Rad_MF(H/N)).                            (61)

Indeed, every corona representation of H kills N, so it factors through
H/N. Conversely every corona representation of H/N composes with q to
one of H. Thus an element of H is killed by all corona representations
exactly when its image in H/N is killed by all corona representations.

Now proceed by transfinite induction. For α = 0, N₀ = 1. Assume
N_α ≤ Rad_MF(H). By soundness of Δ_comp,
Δ_comp(H/N_α) ≤ Rad_MF(H/N_α). Taking preimages and using (61),
N_{α+1} ≤ Rad_MF(H). At a limit ordinal, a union of subgroups contained
in the radical is still contained in the radical. Thus (58) holds.

Because H is countable, only countably many strict successor stages can
occur: each strict successor adds at least one new element of H, and
distinct strict stages may be assigned distinct first-added elements.
The supremum of the countably many addition stages is a countable
ordinal, after which the chain is constant. This proves (59).

Finally let C = Cl_comp(H) and suppose H/C is MF. Then
Rad_MF(H/C) = 1. Since C ≤ Rad_MF(H), equation (61) gives
Rad_MF(H) = q⁻¹(1) = C. This proves (60). If C = H, then the MF radical
is all of H, and every homomorphism to an MF group kills all of H. ∎

This is where I think the theory should ultimately land. No marked
element occurs. No preferred obstruction occurs. No choice between "the
sign proof" and "the involution proof" occurs at the level of the final
object. They are simply different sound inference rules contributing
relations to the same closure.

# 11. The full semantic closure

Let N ⊴ F. Define

    ᴹᶠ√N = q_N⁻¹(Rad_MF(F/N))                                (62)
         = ∩ { ker φ : φ : F → M, M MF, N ≤ ker φ }.         (63)

Then N ↦ ᴹᶠ√N is an extensive, monotone, idempotent closure operator.
If G = ⟨X | R⟩ = F(X)/⟨⟨R⟩⟩, then w ∈ ᴹᶠ√⟨⟨R⟩⟩ means precisely: every
realization of R in every MF group also satisfies w = 1. Thus

    G is MF  ⟺  ⟨⟨R⟩⟩ = ᴹᶠ√⟨⟨R⟩⟩.                            (64)

And the theorem we just proved says

    Cl_comp^F(N) ≤ ᴹᶠ√N.                                     (65)

So compression rigidity is a calculus for deriving MF-semantic
consequences of group relations. That is the formulation in which u
disappears completely.

# 12. Where the old mechanisms sit inside this theorem

The old central-sign construction now reads: u ∈ 𝔇₂(H, L), u² = ε,
⟨ε⟩ ⊴ H finite. Therefore ε ∈ 𝔎(H, L) ≤ Rad_MF(H). Clifford geometry
proves only ε ≠ 1.

The finite-normal theorem is F ⊴ H, F < ∞, F ≤ 𝔇₂(H, L) ⟹
F ≤ 𝔎(H, L). The torsion-free normal-Kazhdan theorem is exactly (16).
The commuting involution theorem is the special case of Theorem 7
obtained from p = (1 − π(k))/2. The commuting m-torsion theorem follows
from zero-dimensional spectral collapse. Finite-spectrum lamps are
likewise a special case. Projection-generated finite-dimensional packets
are covered by Theorem 8. And iterated lamp fusion is just quotient
iteration of the sound rule.

So there really are not half a dozen unrelated tricks anymore. There are
two extraction regimes fed by one Kazhdan-projection engine:

    Kazhdan projection + finite cancellation
      ⟹ one-sided fixed-space equality at every scale

followed by either

    universal 2-invisibility + ambient-normal Kazhdan corner ⟹ MF kernel

or

    commuting projection orbit + self-normalized rank cocycle ⟹ orbit collapse.

Both conclusions then enter the same MF closure.

# 13. Why not force the last two boxes into one fake theorem

There is a genuine mathematical boundary here. The projection theorem
kills all clopen spectral information, and Theorem 10 says precisely
that the remaining motion must occur inside connected spectral
components. That is not cosmetic. Slowly varying infinite-order phases
can live on smaller and smaller relative-rank sectors while retaining
operator norm. They supply exactly the kind of diffuse wall that
normalized trace misses.

So a statement of the form [g z g⁻¹, L] ⊆ Rad_MF(H) for every
compressed centralizer z is simply too strong in general. The two
branches above are therefore not artifacts of an inelegant proof. They
correspond to two real ways to recover information lost by normalized
trace: normal rigid corner, and discrete self-normalizing rank.

What is artificial is treating the central −1, Reynolds averaging,
involutions, finite m, etc. as separate theories. They are not.

The theorem to build the manuscript around is consequently not
"u →₂ 1, u² = −1." It is:

> One-sided compression of a Kazhdan subgroup becomes equality at the
> level of fixed spaces in every finite-dimensional asymptotic target,
> at every Hilbertian scale. This forces an intrinsic collection of
> relations in every MF image. Normal Kazhdan pieces of the tracial
> defect and commuting projection-generated orbit packets are killed
> outright. Iterating these forced relations through quotients produces
> a canonical compression closure contained in the MF radical.

Then the real research problem is no longer "find a prettier u." It is:

> When does Cl_comp(G) = ᴹᶠ√1 = Rad_MF(G)?

That is a structural theory rather than an obstruction trick.
