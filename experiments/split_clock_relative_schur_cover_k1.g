# Put both natural subgroup images inside one Schur multiplier model.
#
# HAP's two independent GroupHomology calls construct isomorphic but
# distinct target objects.  A single Schur extension avoids that ambiguity.
# For an inclusion H -> G, the image H_2(H,Z) -> H_2(G,Z), represented in
# the multiplier kernel M of a Schur cover, is M intersect [H~,H~], where
# H~ is the full preimage of H.

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

ambientPc := Image(pcIsomorphism);;
fpGenerators := GeneratorsOfGroup(presented);;
aaPc := Image(pcIsomorphism, fpGenerators[1]);;
bbPc := Image(pcIsomorphism, fpGenerators[2]);;
hhPc := Image(pcIsomorphism, fpGenerators[3]);;
ccPc := Image(pcIsomorphism, fpGenerators[4]);;

# The polycyclic package installs the Schur-extension method for its pcp
# representation, not GAP's finite pc representation.
pcpIsomorphism := IsomorphismPcpGroup(ambientPc);;
ambient := Range(pcpIsomorphism);;
aa := Image(pcpIsomorphism, aaPc);;
bb := Image(pcpIsomorphism, bbPc);;
hh := Image(pcpIsomorphism, hhPc);;
cc := Image(pcpIsomorphism, ccPc);;

positiveH := Group(aa, bb, hh);;
cycleC := Group(aa, bb, cc);;

if Size(ambient) <> 2187 or Size(positiveH) <> 729 or Size(cycleC) <> 243 then
    Error("unexpected group order");
fi;

coverMap := SchurExtensionEpimorphism(ambient);;
cover := Source(coverMap);;
multiplier := Intersection(Kernel(coverMap), DerivedSubgroup(cover));;

preH := PreImage(coverMap, positiveH);;
preC := PreImage(coverMap, cycleC);;
imageH := Intersection(multiplier, DerivedSubgroup(preH));;
imageC := Intersection(multiplier, DerivedSubgroup(preC));;
combinedImage := Group(Concatenation(Igs(imageH), Igs(imageC)));;
intersectionImage := Intersection(imageH, imageC);;

if AbelianInvariants(multiplier) <> [3, 3, 9] then
    Error("unexpected ambient Schur multiplier");
fi;
if AbelianInvariants(imageH) <> [3, 9]
   or AbelianInvariants(imageC) <> [3, 9] then
    Error("unexpected subgroup image");
fi;
if imageH = imageC or AbelianInvariants(intersectionImage) <> [9] then
    Error("unexpected image intersection");
fi;
if combinedImage <> multiplier then
    Error("the two subgroup images do not fill the multiplier");
fi;

Print("ambient_order=", Size(ambient), "\n");
Print("multiplier=", AbelianInvariants(multiplier), "\n");
Print("positive_h_image=", AbelianInvariants(imageH), "\n");
Print("positive_h_image_order=", Size(imageH), "\n");
Print("cycle_c_image=", AbelianInvariants(imageC), "\n");
Print("cycle_c_image_order=", Size(imageC), "\n");
Print("images_equal=", imageH = imageC, "\n");
Print("intersection=", AbelianInvariants(intersectionImage), "\n");
Print("intersection_order=", Size(intersectionImage), "\n");
Print("combined_image=", AbelianInvariants(combinedImage), "\n");
Print("combined_image_order=", Size(combinedImage), "\n");
Print("combined_cokernel=", AbelianInvariants(multiplier/combinedImage), "\n");
