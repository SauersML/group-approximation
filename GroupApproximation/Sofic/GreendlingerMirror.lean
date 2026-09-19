import GroupApproximation.Sofic.GreendlingerOverlap

/-!
# The descent read backwards

`GreendlingerOverlap` settles the two-factor descent when the *first*
conjugator is the longer one: then the second is a prefix of it, the overhang
positions the overlap inside the second rotation, and either the overlap is a
piece or the two factors cancel.

The other regime --- the second conjugator longer --- is not a new argument.
The whole configuration is self-dual under the formal inverse, and this file
records the duality rather than repeating the geometry.

## The duality

`invRev` reverses and inverts, so it turns a palindrome into a palindrome with
the *same* conjugator and the inverted rotation
(`invRev_palindrome`), and it turns the element the palindrome spells into its
inverse (`mk_palindrome_invRev`).  Applied to a cancellation

`P₁ = P' ++ M`,  `P₂ = invRev M ++ B'`

it produces

`invRev P₂ = invRev B' ++ M`,  `invRev P₁ = invRev M ++ invRev P'`,

which is a cancellation of the same shape with the two factors exchanged and the
same destroyed block `M`.  So the mirrored configuration is an *instance* of the
theorem already proved, at conjugators `(c', c)` --- and the regime hypothesis
`|c'| ≤ |c|` becomes `|c| ≤ |c'|`, which is the case that was open.

## Transporting the conclusion

The Greendlinger conclusion itself is invariant under `invRev`
(`greendlinger_of_invRev`).  Contiguous subwords stay contiguous
(`invRev_infix_of_infix`); a prefix of a symmetrized relator becomes a *suffix*
of one (`invRev_suffix_of_prefix`), and a suffix is a prefix of a rotation
(`prefix_rotate_of_suffix`), which `symmetrization` contains.  Lengths are
unchanged, so the inequality `|s| < 2|u|` survives verbatim.

That last step is the same observation that makes pieces prefix-only: with all
rotations present, "occurs in" and "begins" are the same relation.

The duality pays twice: besides the open conjugator regime it also gives the
*free* case at the other end (`greendlinger_of_short_cancellation_mirror`), a
cancellation that never reaches the second factor's rotation.

Unconditional except where `GreendlingerOverlap` is invoked.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Palindromes under the formal inverse -/

/-- **A palindrome inverts to a palindrome**, with the same conjugator and the
inverted rotation. -/
theorem invRev_palindrome (c t : List (α × Bool)) :
    FreeGroup.invRev (palindrome c t) = palindrome c (FreeGroup.invRev t) := by
  have h1 : FreeGroup.invRev (palindrome c t)
      = FreeGroup.invRev (FreeGroup.invRev c) ++ FreeGroup.invRev (c ++ t) :=
    FreeGroup.invRev_append
  have h2 : FreeGroup.invRev (c ++ t)
      = FreeGroup.invRev t ++ FreeGroup.invRev c :=
    FreeGroup.invRev_append
  rw [h1, h2, FreeGroup.invRev_invRev]
  unfold palindrome
  simp only [List.append_assoc]

/-- And it spells the inverse element. -/
theorem mk_palindrome_invRev (c t : List (α × Bool)) :
    FreeGroup.mk (palindrome c (FreeGroup.invRev t))
      = (FreeGroup.mk (palindrome c t))⁻¹ := by
  rw [mk_palindrome, mk_palindrome, ← FreeGroup.inv_mk]
  group

/-! ## The Greendlinger conclusion is self-dual -/

/-- The formal inverse turns prefixes into suffixes; the companion of
`invRev_prefix_of_suffix`. -/
theorem invRev_suffix_of_prefix {M L : List (α × Bool)} (h : M <+: L) :
    FreeGroup.invRev M <:+ FreeGroup.invRev L := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨FreeGroup.invRev d, FreeGroup.invRev_append.symm⟩

/-- Contiguous subwords stay contiguous under the formal inverse. -/
theorem invRev_infix_of_infix {u w : List (α × Bool)} (h : u <:+: w) :
    FreeGroup.invRev u <:+: FreeGroup.invRev w := by
  obtain ⟨x, y, rfl⟩ := h
  refine ⟨FreeGroup.invRev y, FreeGroup.invRev x, ?_⟩
  have h1 : FreeGroup.invRev (x ++ u ++ y)
      = FreeGroup.invRev y ++ FreeGroup.invRev (x ++ u) :=
    FreeGroup.invRev_append
  have h2 : FreeGroup.invRev (x ++ u)
      = FreeGroup.invRev u ++ FreeGroup.invRev x :=
    FreeGroup.invRev_append
  rw [h1, h2]
  simp only [List.append_assoc]

/-- A suffix of a word is a prefix of the rotation that brings it to the front.
With all rotations present in `symmetrization`, this is what lets a piece be
defined by prefixes alone. -/
theorem prefix_rotate_of_suffix {u s : List (α × Bool)} (h : u <:+ s) :
    u <+: s.rotate (s.length - u.length) := by
  obtain ⟨z, hz⟩ := h
  have hlen : z.length = s.length - u.length := by
    have hz' := congrArg List.length hz
    rw [List.length_append] at hz'
    omega
  have hpre : z ++ u <+: s := ⟨[], by rw [hz, List.append_nil]⟩
  have hrot := prefix_rotate_of_append_prefix hpre
  rwa [hlen] at hrot

/-- **The Greendlinger conclusion is invariant under the formal inverse.**  A
word contains more than half of a symmetrized relator exactly when its formal
inverse does. -/
theorem greendlinger_of_invRev {R : Set (List (α × Bool))} {w : List (α × Bool)}
    (h : ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: FreeGroup.invRev w ∧ u <+: s ∧ s.length < 2 * u.length) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  obtain ⟨s, hs, u, huinf, hupre, hlt⟩ := h
  have hinf : FreeGroup.invRev u <:+: w := by
    have h1 := invRev_infix_of_infix huinf
    rwa [FreeGroup.invRev_invRev] at h1
  have hsuf : FreeGroup.invRev u <:+ FreeGroup.invRev s :=
    invRev_suffix_of_prefix hupre
  refine ⟨(FreeGroup.invRev s).rotate
      ((FreeGroup.invRev s).length - (FreeGroup.invRev u).length),
    rotate_mem_symmetrization (invRev_mem_symmetrization hs) _,
    FreeGroup.invRev u, hinf, prefix_rotate_of_suffix hsuf, ?_⟩
  rw [List.length_rotate, FreeGroup.invRev_length, FreeGroup.invRev_length]
  exact hlt

/-! ## The free case, mirrored -/

/-- **The mirror of the free case.**  A cancellation confined to the *second*
factor's leading conjugator leaves the second rotation whole, and a whole
rotation is more than half of itself.

`GreendlingerDescent` proved this for the first factor's trailing conjugator;
the duality supplies the other end for free. -/
theorem greendlinger_of_short_cancellation_mirror {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) {c' t' P' M B' : List (α × Bool)}
    (ht' : t' ∈ symmetrization R)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hlen : M.length ≤ c'.length) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length := by
  refine greendlinger_of_invRev ?_
  rw [FreeGroup.invRev_append]
  have hm1 : palindrome c' (FreeGroup.invRev t')
      = FreeGroup.invRev B' ++ M := by
    rw [← invRev_palindrome, heq', FreeGroup.invRev_append,
      FreeGroup.invRev_invRev]
  refine greendlinger_of_short_cancellation hRne
    (invRev_mem_symmetrization ht') hm1 ?_
  have hcl : (FreeGroup.invRev c').length = c'.length := FreeGroup.invRev_length
  omega

/-! ## The other conjugator regime -/

/-- **The two-factor descent, read backwards.**  When the *second* conjugator is
the longer one, the mirrored configuration is an instance of
`greendlinger_of_two_palindromes` at the exchanged factors, and the conclusion
transports back.

Nothing new is assumed: `hcoin` is again the statement that the two factors do
not cancel, which is what minimality of the expression supplies. -/
theorem greendlinger_of_two_palindromes_mirror {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hhigh : M.length ≤ (FreeGroup.invRev c').length + t'.length)
    (hle : c.length ≤ c'.length)
    (hfit : c'.length - c.length + M.length ≤ c'.length + t.length)
    (hcoin : FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') ≠ 1) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: P' ++ B' ∧ u <+: s ∧ s.length < 2 * u.length := by
  refine greendlinger_of_invRev ?_
  rw [FreeGroup.invRev_append]
  -- the mirrored cancellation, with the two factors exchanged
  have hm1 : palindrome c' (FreeGroup.invRev t')
      = FreeGroup.invRev B' ++ M := by
    rw [← invRev_palindrome, heq', FreeGroup.invRev_append,
      FreeGroup.invRev_invRev]
  have hm2 : palindrome c (FreeGroup.invRev t)
      = FreeGroup.invRev M ++ FreeGroup.invRev P' := by
    rw [← invRev_palindrome, heq, FreeGroup.invRev_append]
  have hm3 : FreeGroup.invRev M <+: palindrome c (FreeGroup.invRev t) := by
    rw [hm2]
    exact ⟨FreeGroup.invRev P', rfl⟩
  have htl : (FreeGroup.invRev t).length = t.length := FreeGroup.invRev_length
  have htl' : (FreeGroup.invRev t').length = t'.length := FreeGroup.invRev_length
  have hcoin' : FreeGroup.mk (palindrome c' (FreeGroup.invRev t'))
      * FreeGroup.mk (palindrome c (FreeGroup.invRev t)) ≠ 1 := by
    rw [mk_palindrome_invRev, mk_palindrome_invRev]
    intro hcon
    refine hcoin ?_
    rw [← inv_inv (FreeGroup.mk (palindrome c t)
      * FreeGroup.mk (palindrome c' t')), mul_inv_rev, hcon, inv_one]
  exact greendlinger_of_two_palindromes hRne hmetric
    (invRev_mem_symmetrization ht') (invRev_mem_symmetrization ht) hm1 hm3
    (by omega) hle (by omega) hcoin'

end SmallCancellationRouter
end GroupApproximation
