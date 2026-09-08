# Boone--Higman ring route: characteristic and center corrections

## Result and scope

Two defects in the former ring route are corrected here. Neither is a
disproof of Boone--Higman, and neither uses GPU computation.

1. The unrestricted finite-fullness premise is false: Z/6Z cannot embed
   unitally in any nonzero simple ring. More precisely, a nonzero unital
   ring admits an abstract simple unital envelope exactly when it has
   prime characteristic or torsion-free additive group.
2. Every ring containing Z has -I_4 as a nontrivial proper central
   involution in EL_4. Thus even obtaining a simple coefficient ring
   cannot make the proposed unquotiented elementary group simple.

The proofs are canonical Cairn routes
ring-simple-envelope-characteristic-proof and
rank-four-central-involution-proof. They are ordinary algebraic proofs,
not Lean-verified proofs and not conclusions of the graph checker.

## Why the first defect matters

The old premise quantified over all finitely presented unital rings with
decidable equality. Z/6Z meets those hypotheses and contradicts the
conclusion. Merely adding characteristic zero is insufficient, since
Z x F_2 has characteristic zero with nonzero additive torsion. A
characteristic-zero simple unital ring contains Q centrally,
so none of its additive subgroups has nonzero integer torsion.

The actual coefficient rings Z[H] are torsion-free as additive groups.
For them, rationalization followed by an amplified regular representation
in an endomorphism ring modulo low-rank operators supplies an abstract
simple ring embedding. This separates the elementary algebraic obstruction
from the unresolved finite-presentation problem. It supplies no finite
description of the enormous simple target.

## Why the second defect matters

The earlier route said that a Steinberg normal-generation computation
supplied simplicity of EL_4(L). The explicit identity
w_12^2 w_34^2=-I_4, where
w_ij=e_ij(1)e_ji(-1)e_ij(1), contradicts that conclusion for every
characteristic-zero L. A normal generator does not exclude central
normal subgroups.

Quotienting only by this order-two subgroup is not a proof that all proper
normal subgroups have disappeared. Quotienting by the full center still
requires a proof of simplicity and finite presentation. In particular, if
one starts with a finitely presented elementary group, the quotient
criterion requires finite normal generation of the kernel; the center's
being central does not by itself supply a finite generating set.

## Repaired conditional route

decidable-group-ring-has-fp-projective-simple-host is the narrowed open
construction target. It asks for an embedding of the actual integral group
ring into a finitely presented ring whose projective rank-four elementary
group is explicitly both finitely presented and simple.

boone-higman-via-projective-ring-host proves this target would suffice.
Clapham supplies the decidable finitely presented group ring input. The
perfect simple core embeds diagonally in the elementary group by an
explicit commutator identity, and its centerlessness keeps it injective
after projectivization. This proves the embedding step without any new
claim about normal subgroup structure. The host existence is still open.

The old route is retained as an invalidated attempt; the false generic
premise is marked refuted. The repaired route avoids another unsupported
step in the old prose: decidability of equality in Z[H] does not by itself
give decidability in its universal sandwich extension. It starts directly
from Z[H] and needs no such transfer.
