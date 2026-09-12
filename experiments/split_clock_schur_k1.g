# Exact first instance of the finite split-clock Schur family.
#
# This is p=3, k=1, so M=3 and n=9.  In the augmentation basis
# a=e_1-e_0, b=e_2-e_0, cyclic shift acts by
# a |-> b-a and b |-> -a.

if LoadPackage("polycyclic") <> true then
    Error("the polycyclic package is required");
fi;

free := FreeGroup("a", "b", "h", "c");;
a := free.1;;
b := free.2;;
h := free.3;;
c := free.4;;

relations := [
    a^9,
    b^9,
    h^9,
    c^3,
    Comm(a, b),
    Comm(h, a),
    Comm(h, b),
    c*h*c^-1*h^-4,
    c*a*c^-1*(b*a^-1)^-1,
    c*b*c^-1*(a^-1)^-1
];;

presented := free/relations;;
pcIsomorphism := IsomorphismPcGroup(presented);;
if pcIsomorphism = fail then
    Error("failed to convert the split-clock presentation to a pc group");
fi;

splitClock := Image(pcIsomorphism);;
groupOrder := Size(splitClock);;
multiplierInvariants := AbelianInvariantsMultiplier(splitClock);;

if groupOrder <> 2187 then
    Error("unexpected split-clock group order");
fi;
if multiplierInvariants <> [3, 3, 9] then
    Error("unexpected Schur multiplier");
fi;

Print("order=", groupOrder, "\n");
Print("H2_invariants=", multiplierInvariants, "\n");

