# gq-typeA-projective board — DONE (first target)
**Approach:** family host-geometry/type (A). Signature: "type (A) extension of projective action".
**Established (landed ae52139fe, 917e91b63; hand proofs, not independently reviewed):**
- type-a-orbit-accumulation-forces-fg-nontrivial-germs (+ -proof): Γ on Hausdorff X, invariant S with f.g. stabilizers
  and finitely many 2-subset orbits; if x accumulates on Γx then Stab(x)/(elements trivial near x) is f.g. AND nontrivial.
  => generic (trivial-germ) orbits never carry type (A); if H ≤ Γ has the identity principle, Stab_H(x) embeds in the germ group.
**Open target landed:** pgl-q-projective-type-a-extension (fp Γ ≥ PGL_m(Q), type (A) action containing P^(m-1)(Q) as an
  orbit, infinitely many m), route gl-n-q-type-a-via-projective-extension -> gl-n-q-in-permutational-boone-higman-class.
  Strong form S = P^(m-1)(Q): only "Γ fp" + "point stabilizer f.g." remain (2-transitivity gives the rest).
  Subgroup form: f.g. Λ ≥ P(Q), Λ ⊉ PGL_m(Q) (P(Q) maximal), finitely many ΛgΛ.
**Dead (recorded in its Attempts):** (1) natural finitely-piecewise projective hosts (via germ-extensions-omit-standard-gl-n-q);
  (2) near actions on P^(m-1)(Q) (γ agrees with h_γ ∈ PGL_m(Q) off a finite set ⇒ γ ↦ h_γ homomorphism ⇒ f.g. image; kills
  FSym ⋊ PGL and Houghton-type extensions of the natural action — cofinite topology, not covered by the Hausdorff piece lemma);
  (3) homeomorphism hosts: germ group at a rational point must be a f.g. non-RF overgroup of the parabolic P(Q) (Aff(Q) for m=2).
**Needs:** a f.g. group Λ ⊇ Aff(Q) with Λ ∩ PGL_2(Q) = Aff(Q) inside an fp Γ ⊇ PGL_2(Q) with finitely many Λ-double cosets.
**Sparks:** Zariski-topology version of the piece lemma (Cremona-type bijections of P^(m-1)(Q)); Raney transducers realize
  PGL_2(Q) as rational (finite-state) homeomorphisms of the Stern–Brocot Cantor set — killed by the piece lemma (quasi-analytic),
  so any rational/RSG host must add non-local elements.
