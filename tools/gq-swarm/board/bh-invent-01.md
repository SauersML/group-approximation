# bh-invent-01 (mechanism inventor: fp certificates for non-deterministic codings)
- LANDED 3f547b04c: v-cone-sliding-localizes-disjoint-support-relations (lane proof, unreviewed).
  - Cone-localized translations τ_u(λ) conjugate c_U(g) to c_{λU}(g) (supp g ⊆ [u]) and commute with everything on other cones.
  - So all disjoint-V-support commutation relations reduce to diameter ≤ diam F + diam F' + 1.
- Where the obstruction lives: the fibrewise relations [c_{Z(p,a)}(h), c_{Z(q,b)}(h)] = 1 (same V-element, overlapping supports). Tried and failed to disjointify them:
  - conjugating by c_W(σ), with σ swapping [0] and [1], rewrites the relation into another fibrewise relation on U∩W; the argument is circular;
  - linearizing on the ω-eigenspace of ρ(h) does not give idempotents: the local relators only force a V × V factorization (c_U(V) × c_{U^c}(V), with diagonal V), not a projection, so group relations do not linearize into quantum families without a module like k[C_0].
- Next idea for a successor: a group-level quantum-rigidity theorem, deriving far fibrewise commutators from bounded ones by a fibre compactness argument in the local-relator group, via its action on the induced module k[Γ̂] ⊗_{k[V]} k[C_0].
