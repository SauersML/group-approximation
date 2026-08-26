---
rg: 2
id: atlas-shortest-escapee-literal-control-firewall
kind: claim
title: The shortest Atlas escapee has a three-term inversion energy, and literal controls reach only its parabolic term
distinct_from:
  atlas-escapee-defect-charges-inversion-commutator-energy: that gives the universal bubble-sort lower bound for every single-factor escapee; this computes the energy of one actual escapee exactly and isolates what the literal controls do and do not charge.
  atlas-flip-first-order-rigidity: that proves vanishing of scalar trace derivatives for every relator at the flip; this is an operator-valued commutator decomposition and does not follow from trace stationarity.
  atlas-stabilizer-commutant-no-go: that excludes an entire relative-unitary ansatz at every multiplicity; this only fences the elementary literal-control telescope and leaves all unrestricted relative unitaries in play.
---

**ESTABLISHED EXACT DECOMPOSITION AND LITERAL-CONTROL FIREWALL.**  Use
row-major hexadecimal notation for matrices in `GL_4(F_2)` and put

```text
a = 8461,             b = 8621,             c = 8241.
```

The shortest cartesian escapee `st3_135_11` is exactly

```text
w = a_1 b_2 a_1 c_2 a_1 b_2 a_1 a_2 a_1.            (SLC1)
```

Here `a^2=b^2=c^2=1`, `c=aba`, and `(ab)^3=1`.  Hence the factor
projections are `(p_1(w),p_2(w))=(a,1)`, and its ten inversions give

```text
E_w(U)
 = 6 ||[A_a,B_b]||_2^2
 + 3 ||[A_a,B_c]||_2^2
 +   ||[A_a,B_a]||_2^2.                              (SLC2)
```

The final term is charged exactly, with constant one, by the literal
four-syllable control `orth_15_35_11=[a_1,a_2]`:

```text
||pi_U(orth_15_35_11)-1||_2 = ||[A_a,B_a]||_2.       (SLC3)
```

The complete literal-control telescope with first-chart letter `a` stops
there.  Its second-chart letters are

```text
8431, 8461, 8423, 8425,
```

and they generate the order-`24` parabolic

```text
P = { diag(1,M) : M in GL_3(F_2), e_1^* M=e_1^* }.
```

Both `b=8621` and `c=8241` lie outside `P`.  Therefore neither of the first
two terms of `(SLC2)` can be reached by repeatedly applying

```text
||[A,B_(xy)]||_2 <= ||[A,B_x]||_2 + ||[A,B_y]||_2   (SLC4)
```

to the literal controls while holding `A=A_a` fixed.  Thus pointwise
bubble-sort charging by the visible four-syllable controls does **not** prove
the desired coercivity even for the shortest escapee.

**FULL-CONTROL COERCIVITY REMAINS OPEN.**  This firewall is deliberately
narrow.  It does not exclude an inequality using longer controls, linear
combinations of their operator Jacobians, or all `4,564` control defects.
The stronger `atlas-shortest-escapee-has-no-relator-telescope` shows that
longer controls cannot help through an exact product-of-conjugates word
telescope either; genuinely analytic operator information could still help.
In particular it proves neither

```text
E_w(U) <= C sum_(s in controls) ||pi_U(s)-1||_2^2
```

nor a counterdirection to that inequality.  The landed flip-stationarity
result concerns scalar trace derivatives.  The bounded Hessian artifact uses
only a `72`-word control sample and finitely many unpolarized translation
directions.  Neither supplies the full operator-Jacobian kernel inclusion
needed for local coercivity, so neither decides this endpoint.

DERIVATION
atlas-shortest-escapee-literal-control-firewall-proof
