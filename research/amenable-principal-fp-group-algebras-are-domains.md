---
rg: 2
id: amenable-principal-fp-group-algebras-are-domains
kind: claim
title: For a torsion-free amenable group, Q[G] is a domain iff every principal left ideal is of type FP; with finite cd, left coherence of Q[G] suffices
distinct_from:
  amenable-finite-cd-integral-group-rings-are-domains: that is the open zero-divisor half of Kropholler's question; this is an established criterion that turns it into a homological finiteness (coherence) statement about principal left ideals
  kaplansky-zero-divisor-conjecture: that asserts domains for all torsion-free groups with no finiteness input; this proves domains only for amenable groups and only under the principal-FP (e.g. coherence) hypothesis
  elementary-amenable-torsion-free-strong-atiyah: that is Linnell's theorem for elementary amenable groups via induction on the class; this uses no elementary amenability, only amenability, Baum--Connes traces and a finite projective resolution
  coherent-flat-group-algebra-hosts-force-fp-infinity: that derives finiteness of subgroups from coherent hosts; this derives absence of zero divisors from finiteness of principal ideals
---

**ESTABLISHED** through `amenable-principal-fp-group-algebras-are-domains-proof`, from cited
theorems (Lück's dimension-flatness for amenable groups, Higson--Kasparov plus the trace
conjecture consequence of Baum--Connes).

Let `G` be a torsion-free amenable group (any cardinality).

1. **Criterion.** `Q[G]` has no zero divisors if and only if, for every `a ∈ Q[G]`, the principal
   left ideal `Q[G]a` is of type `FP` as a left `Q[G]`-module (a finite-length resolution by
   finitely generated projective modules).
2. **Finite cd.** If `cd_Q G < ∞`, "type `FP`" in (1) may be replaced by "type `FP_∞`" (a resolution by finitely generated projectives, possibly infinite).
3. **Coherence.** If `cd_Q G < ∞` and `Q[G]` is left coherent, then `Q[G]` (hence `Z[G]`) is a
   domain. The same holds with `Q` replaced by any subfield of `C`.

This is the coherent analogue of the Farkas--Snider argument for polycyclic groups (Noetherian
plus finite global dimension plus integral ranks gives a domain), with amenability replacing Goldie
theory and the Baum--Connes trace theorem replacing Moody's induction theorem.

For the zero-divisor half of Kropholler's question it gives a new sufficient condition: the
integral group ring of an amenable group `G` of finite cd is a domain as soon as `Q[G]` is left
coherent. In dimension 2 the condition is also
necessary (`amenable-cd-two-solvable-iff-coherent-rational-group-algebra`).
