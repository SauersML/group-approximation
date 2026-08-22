# Exact universal presentation behind the marked collision-S4 vertex.
free := FreeGroup("t", "s", "c");;
t := free.1;;
s := free.2;;
c := free.3;;
collision := t*c*s*c*t^-1*c*s*t*c;;
group := free / [t^3, s^2, (s*t)^2, c^2, (c*t)^3, collision];;

# A Todd--Coxeter calculation gives the upper bound 24.
if Size(group) <> 24 then
  Error("universal local collision presentation does not have order 24");
fi;
if AbelianInvariants(group) <> [2] then
  Error("unexpected abelianization");
fi;

# The marked S4 permutations give a quotient of order 24, hence an isomorphism.
t4 := (1,2,3);;
s4 := (1,2);;
# GAP composes permutations by its right-action convention.  This is the
# right-action representative of c=(1 3)(2 4) in the left-composition
# convention used by the packet replay.
c4 := (1,4)(2,3);;
if t4^3 <> () or s4^2 <> () or (s4*t4)^2 <> () or c4^2 <> ()
   or (c4*t4)^3 <> ()
   or t4*c4*s4*c4*t4^-1*c4*s4*t4*c4 <> () then
  Error("marked S4 tuple does not satisfy the universal relators");
fi;
image := Group(t4, s4, c4);;
if Size(image) <> 24 or IdGroup(image) <> [24,12] then
  Error("marked quotient is not S4");
fi;

permutation_isomorphism := IsomorphismPermGroup(group);;
permutation_group := Image(permutation_isomorphism);;
if IdGroup(permutation_group) <> [24,12] then
  Error("universal group is not S4");
fi;

quotient_generators := GeneratorsOfGroup(group);;
tg := quotient_generators[1];;
sg := quotient_generators[2];;
cg := quotient_generators[3];;
k := Subgroup(group, [tg,sg]);;
v := NormalClosure(group, Subgroup(group, [cg]));;
if Size(k) <> 6 or Size(v) <> 4 or Size(FactorGroup(group,v)) <> 6 then
  Error("marked S3/V4 structure is wrong");
fi;

Print("universal_order=", Size(group),
      " id=", IdGroup(permutation_group),
      " marked_K_order=", Size(k),
      " normal_closure_c_order=", Size(v),
      " quotient_by_normal_closure_order=", Size(FactorGroup(group,v)),
      "\n");
