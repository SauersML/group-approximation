# Cycle tails as Hodge atoms, and why a gap near the minimum is the cost–Betti gap

Research note, 2026-09-17 (worker b-p-fp1, family operator-algebras).

Conventions, cost, the cycle modules Z(Phi), Z_L(Phi), and the quantities z, z_L, tau_L, g are those of
`research/artifacts/fpbs/docs/cost-cycle-structure.md`, Sections 1 to 4. The graphings there are simple,
unoriented, Borel and of bounded degree. Gamma is an infinite, finitely generated group. b is a free Bernoulli
action of Gamma on (X_0,nu)^Gamma, with nu not a point mass, and R = R_b. We use the action convention
(g x)_h = x_(g^-1 h).

Status of the parts:

- Section 1 is a Hodge deduction over the imported identity (3.1) of the canonical artifact.
- Section 2 is an elementary proof over the facts (3.1), (3.2) and (4.1) of the canonical artifact. It is the
  load-bearing result.
- Section 3 is a dictionary over imported theorems: the Fourier isomorphism and Lueck approximation. It is not
  needed for Section 2.

## 1. The L-filled Hodge Laplacian carries tau_L as its kernel atom

Fix a bounded-degree graphing Phi generating R and an integer L >= 3. Let C_2^(L) be the Hilbert R-module with
one basis vector per closed Phi-walk of length at most L. The walks are chosen fiberwise and measurably, and
there are boundedly many at each vertex. The boundary operator partial_2 sends a walk to its edge chain. It is
bounded because the degree is bounded.

Every closed-walk chain is a finite sum of simple-cycle chains of no greater length. Every simple cycle is a
closed walk. So the closure of the image of partial_2 is Z_L(Phi). Put

    Delta_1^(L)(Phi) = partial_1^* partial_1 + partial_2 partial_2^*   on C_1(Phi).

**Proposition 1.**

    dim_R ker Delta_1^(L)(Phi) = beta_1^(2)(Gamma) + tau_L(Phi).

*Proof.* partial_1 partial_2 = 0, so ker Delta = ker partial_1 ∩ ker partial_2^* = ker partial_1 ⊖ Z_L(Phi).
By Section 3 of the canonical artifact, dim ker partial_1 = c(Phi) - 1. Additivity gives
dim ker Delta = c - 1 - z_L. Identity (3.1), c = 1 + beta_1 + z, turns this into beta_1 + z - z_L. QED.

Combined with (3.2) and (4.1): along any near-minimizing sequence Phi_n, the kernel dimension of
Delta_1^(L)(Phi_n) tends to beta_1 + g(R) for every fixed L. The target claim
`fpbs-bernoulli-cycle-tail-compactness` says that some near-minimizing sequence has
lim_L limsup_n dim ker Delta_1^(L)(Phi_n) = beta_1. In words, the spectral atom at zero of the L-filled
Laplacian drops to the harmonic value uniformly in large L.

## 2. Chord insertion: tau_L has no gap near the minimum unless g > 0

A *finite-piece graphing* is one whose edges {x, g x} use only group elements g from a finite set F. Such a set
F generates Gamma, because Phi generates the free relation R. Section 1 of the canonical artifact shows that
finite-piece graphings approximate C(R).

**Lemma 2 (chord insertion).** Let Phi be a finite-piece graphing generating R, and fix L >= 3 and eta > 0.
There is a finite-piece graphing Phi' ⊇ Phi generating R with the following properties:

    0 < c(Phi') - c(Phi) < eta,    Z_L(Phi') = Z_L(Phi),    tau_L(Phi') = tau_L(Phi) + (c(Phi') - c(Phi)).

*Proof.*

1. **Choose the chord element.** Let F ⊂ Gamma be finite and symmetric, with Phi using only elements of F.
   Choose gamma ∈ Gamma with word length |gamma|_F > L. This is possible because Gamma is infinite and F
   generates it. Let W be the finite set of group elements represented by words of length at most L over
   F ∪ {gamma, gamma^-1}.

2. **Define the insertion set.** Set

       V = {w^-1 : w ∈ W, w ≠ e} ∪ {w^-1 gamma : w ∈ W, w ≠ gamma}.

   V is finite and e ∉ V. Pick a Borel B ⊂ X_0 with 0 < nu(B) < 1, a finite set V' ⊇ V not containing e, and
   put

       U = {x : x_e ∈ B, and x_v ∉ B for all v ∈ V'}.

   Then mu(U) = nu(B)(1 - nu(B))^|V'|. Enlarging V' makes this positive and smaller than eta. Let Phi' add to
   Phi the chord edges {y, gamma y} for y ∈ U.

3. **Check that the chords are new and distinct.** Take y ∈ U and w ∈ W. The coordinate (w y)_e equals
   y_(w^-1), which lies outside B whenever w ≠ e. So w y ∉ U for w ≠ e. Likewise w y ∈ gamma U means
   gamma^-1 w y ∈ U, which forces w = gamma.

   Since gamma ∈ W, this gives U ∩ gamma U = ∅, so distinct y give distinct chord edges. Each chord edge is new
   because gamma ∉ F (|gamma|_F > L >= 3). Hence Phi' is simple, has bounded degree, generates R, and
   c(Phi') = c(Phi) + mu(U).

4. **No short simple cycle uses a chord.** Suppose a simple cycle of length at most L uses the chord at y ∈ U.
   All its vertices have the form w y with w ∈ W. By Step 3, the only chord endpoints among them are y and
   gamma y, so the cycle uses only that one chord. Removing the chord leaves a Phi-chain c_Phi with
   partial c_Phi = ±(gamma y - y), supported on a path of length at most L - 1.

   Every Phi-path from y to gamma y has length at least |gamma|_F > L - 1. So y and gamma y lie in different
   connected components of the support of c_Phi. The boundary coefficients of a chain sum to zero on each
   component of its support, but the component containing y carries the single coefficient ∓1. This is a
   contradiction.

   Hence the simple cycles of Phi' of length at most L are exactly those of Phi, and Z_L(Phi') = Z_L(Phi).

5. **Compute the tail.** Identity (3.1), with beta_1 depending only on Gamma, gives
   z(Phi') = z(Phi) + mu(U). Subtracting z_L(Phi') = z_L(Phi) gives the claim. QED.

**Theorem 3 (gap near the minimum is equivalent to the cost–Betti gap).** Fix any L >= 3. The following are
equivalent:

- (i) g(R_b) > 0, that is, C(b) > 1 + beta_1^(2)(Gamma).
- (ii) There are delta > 0 and eps > 0 such that every finite-piece graphing Phi generating R_b with
  c(Phi) < C(b) + eps satisfies tau_L(Phi) ∉ (0, delta).

(i) implies (ii) also for all bounded-degree graphings, with eps and delta depending on L.

*Proof.*

- **(i) ⇒ (ii).** Estimate (4.2) of the canonical artifact gives tau_L(Phi) >= g - (L-1) eps'. Here
  eps' = c(Phi) - C(b). Take eps = g / (2(L-1)) and delta = g/2. Then tau_L >= g/2, so tau_L ∉ (0, delta).
- **(ii) ⇒ (i).** Suppose g = 0, and let delta and eps be given. Pick a finite-piece graphing Phi with
  c(Phi) < C(b) + min(eps, delta)/2. By (3.2), tau_L(Phi) <= z(Phi) = c(Phi) - C(b) < delta/2. Apply Lemma 2
  with eta = min(eps, delta)/2. The result Phi' satisfies c(Phi') < C(b) + eps and
  0 < tau_L(Phi') < delta, contradicting (ii). QED.

**Consequence: the class of approaches that dies.** Take any argument for the target that runs:

1. show that the cycle tail (equivalently, by Proposition 1, the Hodge atom above beta_1) of near-minimizers
   is quantized, or has a uniform spectral gap at zero;
2. conclude that small tails vanish.

Theorem 3 shows that such a gap holds near the minimum exactly when the target fails. Step 1 is therefore
unprovable if the target is true.

This covers integrality or Atiyah-type rationality of kernel dimensions with bounded denominators. It also
covers Lueck-type approximation by integer Betti numbers of finite complexes when used to force a gap, and
upper semicontinuity arguments that only separate zero from positive values.

What survives is a *quantitative decay estimate for a specifically constructed sequence*, not an invariant of
all near-minimizers. Chord insertion is cost-cheap and invisible at scale L, so any valid argument must be
insensitive to it. It must either pick its sequence (chords can be deleted again by Theorem 2.1 at scale
|gamma|_F + 1) or prove a bound of the form tau_L <= f_L(eps) with f_L(eps) -> 0.

## 3. Finite-quotient dictionary for residually finite groups (imported theorems)

This section takes X_0 = {0,1} with the uniform measure. Let G = (Z/2)^(Gamma) ⋊ Gamma = Z/2 wr Gamma.

**Fourier isomorphism.** The Fourier transform L^2({0,1}^Gamma) ≅ l^2((Z/2)^(Gamma)) identifies
L^infinity({0,1}^Gamma) ⋊ Gamma = L(R_b) with the group von Neumann algebra L(G), preserving traces. The
indicator of x_h = a is (1 + (-1)^a delta_h)/2. So every cylinder set is a projection in Q[(Z/2)^(Gamma)].

**Cylinder graphings give rational matrices.** Call Phi a *cylinder graphing* if it is a finite-piece graphing
whose pieces {x ∈ U_i} -> {g_i x} have cylinder domains U_i. The closed Phi-walks of length at most L form
finitely many words, and their domains are cylinder sets.

With P the diagonal projection onto the pieces, Delta' = P Delta_1^(L)(Phi) P + (1 - P) is a self-adjoint
matrix over Q[G]. It has ker Delta' = ker Delta_1^(L)(Phi).

**Cylinder graphings approximate cost.** Approximate the pieces of a near-optimal finite-piece graphing by
cylinder sets. The set on which a fixed generator is recovered by a bounded Phi-word is then a finite Boolean
combination of translates of cylinders. Add the generator on its complement, which is again a cylinder-algebra
set. This is the argument of Section 1 of the canonical artifact with cylinder-algebra sets throughout.

**Corollary 4 (finite formula).** Let Gamma be residually finite, and let N_n be a nested chain of finite-index
normal subgroups with trivial intersection. Put Q_n = Gamma/N_n. For every cylinder graphing Phi and every L,

    beta_1^(2)(Gamma) + tau_L(Phi)
        = lim_n  2^(-|Q_n|) sum_(x ∈ {0,1}^(Q_n))  b_1( X_n^(L)(Phi, x) ; Q ) / |Q_n|.

Here X_n^(L)(Phi, x) is the 2-complex on the vertex set Q_n with:

- edges {q, g_i q} whenever q·x lies in the pattern U_i read in Q_n;
- a 2-cell on every closed edge-walk of length at most L.

*Proof.*

- **Residual finiteness and the chain.** G is residually finite (Gruenberg). The kernels K_n of
  G -> (Z/2)^(Q_n) ⋊ Q_n form a nested chain with trivial intersection: a finitely supported f summing to zero
  along all N_n-cosets vanishes once its support injects into Q_n.
- **Lueck approximation.** Lueck's approximation theorem (GAFA 4 (1994), for integer matrices; clear
  denominators) applied to Delta' gives the kernel dimension as the limit of normalized kernel dimensions over
  Q[G/K_n].
- **Reading the finite complexes.** Under the finite Fourier transform, the regular representation of
  Q[(Z/2)^(Q_n) ⋊ Q_n] is the direct sum over x ∈ {0,1}^(Q_n) of l^2 of the groupoid fiber Q_n. The image of
  Delta' is the Hodge Laplacian of X_n^(L)(Phi, x) there. Once the L-ball and the cylinder windows inject into
  Q_n, the short closed walks and patterns are the correct ones.
- **Finite Hodge theorem.** Its kernel has dimension b_1. QED.

Corollary 4 changes neither status nor uniformity. The target needs the limit in n uniformly over a
near-minimizing sequence of cylinder graphings, which is the interchange already identified in Section 4 of the
canonical artifact. Theorem 3 shows that a finite-level integrality gap cannot supply that uniformity: b_1 is an
integer, but its normalized average is not quantized.

## References

- Canonical artifact: `research/artifacts/fpbs/docs/cost-cycle-structure.md`, (3.1), (3.2), (4.1), (4.2) and
  Section 1.
- W. Lueck, Approximating L^2-invariants by their finite-dimensional analogues, GAFA 4 (1994) 455–481.
- K. W. Gruenberg, Residual properties of infinite soluble groups, Proc. LMS (3) 7 (1957) 29–62, for residual
  finiteness of A wr Gamma with A finite abelian and Gamma residually finite.
