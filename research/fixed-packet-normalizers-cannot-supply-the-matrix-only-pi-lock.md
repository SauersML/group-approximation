---
rg: 2
id: fixed-packet-normalizers-cannot-supply-the-matrix-only-pi-lock
kind: claim
title: Fixed packet normalizers cannot supply the matrix-only polynomial-identity lock
distinct_from:
  finite-selector-gadget-induction-barrier: that rules out arbitrary support pruning by finite selector groups; this shows that even adjoining finitely many exact packet normalizers remains tracial-functorial at the PI endpoint.
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that supplies the explicit scalar contradiction after source-factor confinement and target Pauli recovery; this proves that confinement cannot come solely from normalization of the fixed source packet.
---

Let `K` be a finite group and let `pi` be a two-dimensional irreducible
representation.  Write `e_pi` for its central primitive idempotent.  In any
tracial representation `rho` of `K`, the finite packet algebra on the
`pi`-corner is

```text
A_pi=rho(C[K]) e_pi ~= M_2 tensor 1.                       (FPN1)
```

The multiplicity algebra may be a matrix algebra, diffuse, or infinite, but
it does not change the degree-two polynomial identity of `A_pi`.

### Packet normalization is tracial-functorial

Suppose a unitary `u` implements an automorphism `theta` of the fixed packet:

```text
u rho(k) u^* = rho(theta(k))  for every k in K,             (FPN2)
```

and suppose `theta` preserves the equivalence class of `pi`.  Then

```text
u e_pi u^*=e_pi,
u A_pi u^*=A_pi.                                           (FPN3)
```

This is true in every tracial von Neumann algebra, not only in matrices.  It
is simply functoriality of the finite-dimensional algebra `C[K]e_pi`.

The robust version is also dimension-free.  If `(FPN2)` holds with
Hilbert--Schmidt error at most `epsilon` on every member of the fixed finite
table, then the Fourier formula

```text
e_pi=(dim(pi)/|K|) sum_(k in K) conjugate(chi_pi(k)) rho(k) (FPN4)
```

gives

```text
||u e_pi u^*-e_pi||_2 <= C_K epsilon.                      (FPN5)
```

Likewise, for every fixed packet word `a`, the compressed conjugate
`e_pi u rho(a)u^*e_pi` lies within `C_(K,a) epsilon` of `A_pi`.  The constants
depend only on the fixed finite table and character coefficients.  The proof
uses only finite linear combinations, unitary invariance of `||.||_2`, and
the triangle inequality, so it remains valid in arbitrary finite tracial von
Neumann algebras.

### Consequence for the rectangular PI route

Take four returned words obtained by conjugating four fixed packet words by
finitely many normalizers satisfying relations of the form `(FPN2)`.  On the
`pi`-corner all four are confined to the same `M_2` algebra, up to a fixed
multiple of the normalizer defect.  Therefore
`four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap` says that they
cannot also satisfy two anticommuting Pauli-pair relations and four
cross-commutation relations below its fixed `1/30` scale.

But this implication is universal tracial.  In the canonical regular trace
of a group containing the packet faithfully,

```text
tau(e_pi)=dim(pi)^2/|K|>0.                                 (FPN6)
```

Consequently, exact group relations which obtain both source confinement and
the target two-qubit Pauli relations solely through fixed packet
normalization would also eliminate a positive regular packet corner.  Such a
presentation cannot simultaneously preserve the required exact marked
regular model.

### Claim boundary

This does not refute the fixed-degree PI strategy.  It identifies where its
matrix-only input must occur.  A successful actuator has to expose something
which distinguishes finite multiplicity from an arbitrary tracial
multiplicity algebra, for example:

- a scalable word-generated algebra exhausting the commutant;
- a closed multiplicity cycle returning to the identical finite reservoir;
- a source-specific non-Connes-embeddable moment condition; or
- another finite-coordinate common-carrier theorem.

Adding more fixed finite normalizers, more character projectors, or a finite
Hecke table cannot provide that distinction.  Those operations never see
the anonymous multiplicity factor and therefore cannot defeat rectangular
escape without also triggering the regular-trace firewall.
