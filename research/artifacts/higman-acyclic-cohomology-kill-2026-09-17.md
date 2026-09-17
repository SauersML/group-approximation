# Higman acyclicity and the cohomological refutation lane: verbatim sources (2026-09-17)

This is the source file for `higman-cohomological-countermodel-invariants-vanish`.
The texts below were extracted by `pypdf` on 2026-09-17 from the PDFs, and
line-break hyphenation has been removed.

## 1. Higman group: torsion-free, classifying 2-complex, acyclic

Source: I. J. Leary and M. Saadetoglu, *Some groups of finite homological
type*, OSU preprint 2005-3,
<https://math.osu.edu/sites/math.osu.edu/files/2005-3-preprint.pdf>.

> "The group H below was introduced by Higman, who proved that H has the
> 'group theoretic' properties given in the following theorem [6]. The proof
> that H has the stated 'homological properties' was given by Baumslag, Dyer
> and Heller in [1], where the group H played an important role in their
> strengthened version of the Kan-Thurston theorem.
>
> Theorem 8 (G. Higman, G. Baumslag, E. Dyer, A. Heller) Let H be the group
> defined by the presentation H = ⟨ a,b,c,d : a^b = a^2, b^c = b^2, c^d = c^2,
> d^a = d^2 ⟩. Then H is an infinite torsion-free group, the presentation
> 2-complex for the above presentation is a classifying space for H, and H
> admits no non-trivial quotient in which the images of the generators have
> finite order.
>
> Corollary 9 H as above is a non-trivial torsion-free acyclic group with no
> proper finite-index subgroups."

Reference [1] there is Baumslag--Dyer--Heller, *The topology of discrete
groups*, J. Pure Appl. Algebra 16 (1980).  Only the conventions of the
presentation differ from `(HMF1)`: inverting the generators and reversing the
cyclic order gives the same group.  The cellular calculation in the proof
route independently checks `H_1 = H_2 = 0` for the cyclic convention.

## 2. Dadarlat--Glebe obstruction class

Source: M. Dadarlat and F. Glebe, *Central extensions and almost
representations*, arXiv:2502.04590.

> Abstract: "... For an asymptotic group homomorphism ρ_n : Γ → U(A_n), the
> corresponding pullback of the canonical central extension gives a
> 2-cohomology class in H^2(Γ, Q(R)) which obstructs the perturbation of
> (ρ_n) to a sequence of true homomorphisms of groups π_n : Γ → GL(A_n). The
> pairing of the obstruction class with elements of H_2(Γ, Z) yields
> numerical invariants in τ_{n*}(K_0(A_n)) that subsume the winding number
> invariants of Kazhdan, Exel and Loring."
>
> "Theorem 1.2. Let Γ be a discrete countable group. (1) If H^2(Γ, R) ≠ 0,
> then Γ is not local-to-local stable with respect the class of separable
> unital tracial C*-algebras. (2) If the comparison map J : H^2_b(Γ, R) →
> H^2(Γ, R) is nonzero, then Γ is not uniform-to-local stable with respect
> the class of separable unital tracial C*-algebras."
>
> "Theorem 1.4. If Γ is a countable discrete group and for some [σ] ∈ H^2(Γ,
> R) \ {0} there is a sequence θ_n ↘ 0 so that for each n, the twisted full
> group C*-algebra, C*(Γ, σ^{θ_n}) has a nonzero MF quotient, then Γ is not
> matricially stable."
>
> Introduction: "... one obtains a central extension as above with Q(R) =
> c_0(N, R)/c_00(N, R)."

## 3. Dadarlat's even-cohomology obstruction

This is already imported with verbatim quotes in
`dadarlat-matricial-stability-obstruction`: Theorem 1.1 of arXiv:2007.12655
has the hypothesis `H^(2k)(G, Q) != 0` for some `k >= 1`.

## 4. The consequence for the Higman seed

- Every theorem quoted in sections 2--3 has a hypothesis of the form "some
  class in `H^2(Γ;R)`, `H^(2k)(Γ;Q)` or `H_2(Γ;Z)` is nonzero".
- For `Hig` all of these groups are zero.
- For every generalized cycle `H_k(BS(1,m))`, `m >= 2`, the `H^2` and `H_2`
  groups are zero.

So the lane of perturbation obstructions indexed by two-cohomology has no
member that can separate a quasi-representation of `Hig` from the trivial
representation.  Any operator-norm countermodel to `(HMF3)` must be invisible
to all of them.
