# Exact relative H2 maps for the first finite split-clock group.
#
# The ambient group is G_1=J_1 semidirect B_1 of order 3^7.  We compare
# the maps on H_2 induced by the two natural subgroups J_1 semidirect <h>
# and J_1 semidirect <c>.  This distinguishes absorption of the marked
# h/clock direction from the unmarked pure-cycle direction.

if LoadPackage("HAP") <> true then
    Error("HAP is required");
fi;
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

ambient := Image(pcIsomorphism);;
fpGenerators := GeneratorsOfGroup(presented);;
aa := Image(pcIsomorphism, fpGenerators[1]);;
bb := Image(pcIsomorphism, fpGenerators[2]);;
hh := Image(pcIsomorphism, fpGenerators[3]);;
cc := Image(pcIsomorphism, fpGenerators[4]);;

positiveH := Group(aa, bb, hh);;
cycleC := Group(aa, bb, cc);;

if Size(ambient) <> 2187 then
    Error("unexpected ambient order");
fi;
if Size(positiveH) <> 729 then
    Error("unexpected J semidirect <h> order");
fi;
if Size(cycleC) <> 243 then
    Error("unexpected J semidirect <c> order");
fi;

inclusionH := GroupHomomorphismByFunction(positiveH, ambient, x -> x);;
inclusionC := GroupHomomorphismByFunction(cycleC, ambient, x -> x);;

mapH := GroupHomology(inclusionH, 2);;
mapC := GroupHomology(inclusionC, 2);;

cokernelH := Range(mapH)/Image(mapH);;
cokernelC := Range(mapC)/Image(mapC);;

Print("ambient_order=", Size(ambient), "\n");
Print("ambient_H2=", AbelianInvariants(Range(mapH)), "\n");
Print("positive_h_order=", Size(positiveH), "\n");
Print("positive_h_H2=", AbelianInvariants(Source(mapH)), "\n");
Print("positive_h_image=", AbelianInvariants(Image(mapH)), "\n");
Print("positive_h_image_order=", Size(Image(mapH)), "\n");
Print("positive_h_cokernel=", AbelianInvariants(cokernelH), "\n");
Print("cycle_c_order=", Size(cycleC), "\n");
Print("cycle_c_H2=", AbelianInvariants(Source(mapC)), "\n");
Print("cycle_c_image=", AbelianInvariants(Image(mapC)), "\n");
Print("cycle_c_image_order=", Size(Image(mapC)), "\n");
Print("cycle_c_cokernel=", AbelianInvariants(cokernelC), "\n");

sameRange := Range(mapH) = Range(mapC);;
Print("common_target_object=", sameRange, "\n");
if sameRange then
    combinedImage := Group(Concatenation(
        GeneratorsOfGroup(Image(mapH)),
        GeneratorsOfGroup(Image(mapC))));;
    combinedCokernel := Range(mapH)/combinedImage;;
    Print("combined_image_order=", Size(combinedImage), "\n");
    Print("combined_cokernel=", AbelianInvariants(combinedCokernel), "\n");
fi;
