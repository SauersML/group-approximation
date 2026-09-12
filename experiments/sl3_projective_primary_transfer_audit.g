# Exact finite-group audit of the orientation-primary transfer block in the
# fixed SL(3,Z) cellular resolution.
#
# Run after making HAP available to GAP.  The degree-one stabilizer is D8,
# the first degree-two stabilizer is S4, and the three cellular boundary
# elements are a right transversal for D8 in S4.  The script checks every
# subgroup, not only every conjugacy class, so the conclusion applies to
# every transitive S4-set and hence to every finite S4-set.

if LoadPackage("hap") = fail then
    Error("the HAP package is required");
fi;

PrimaryTransferComplex := ContractibleGcomplex("SL(3,Z)");
PrimaryTransferD8 := PrimaryTransferComplex!.stabilizer(1, 1);
PrimaryTransferS4 := PrimaryTransferComplex!.stabilizer(2, 1);
PrimaryTransferBoundary := List(
    PrimaryTransferComplex!.boundary(2, 1),
    term -> PrimaryTransferComplex!.elts[term[2]]);

if StructureDescription(PrimaryTransferD8) <> "D8" then
    Error("unexpected degree-one stabilizer");
fi;
if StructureDescription(PrimaryTransferS4) <> "S4" then
    Error("unexpected degree-two stabilizer");
fi;
if not IsSubgroup(PrimaryTransferS4, PrimaryTransferD8) then
    Error("the cellular D8 is not a subgroup of the cellular S4");
fi;
if Length(Set(List(
        PrimaryTransferBoundary,
        element -> RightCoset(PrimaryTransferD8, element))))
        <> Index(PrimaryTransferS4, PrimaryTransferD8) then
    Error("the boundary elements are not a right transversal");
fi;

PrimaryTransferOrientation := function(degree, cell, element)
    local position;
    position := Position(PrimaryTransferComplex!.elts, element);
    if position = fail then
        Add(PrimaryTransferComplex!.elts, element);
        position := Length(PrimaryTransferComplex!.elts);
    fi;
    return PrimaryTransferComplex!.action(degree, cell, position);
end;

PrimaryTransferAudit := function()
    local all_subgroups, torsion_subgroups, subgroup, source_is_torsion,
          cosets, orbits, torsion_orbits, counts, element, coset, position,
          odd_positions;
    all_subgroups := Concatenation(List(
        ConjugacyClassesSubgroups(PrimaryTransferS4), AsList));
    torsion_subgroups := 0;

    for subgroup in all_subgroups do
        source_is_torsion := ForAny(
            Elements(subgroup),
            element -> PrimaryTransferOrientation(2, 1, element) = -1);
        cosets := RightCosets(PrimaryTransferS4, subgroup);
        orbits := Orbits(PrimaryTransferD8, cosets, OnRight);
        torsion_orbits := Filtered(
            [1..Length(orbits)],
            position -> ForAny(
                Elements(Stabilizer(
                    PrimaryTransferD8, orbits[position][1], OnRight)),
                element -> PrimaryTransferOrientation(1, 1, element) = -1));

        if source_is_torsion then
            torsion_subgroups := torsion_subgroups + 1;
            if Length(torsion_orbits) <> 1 then
                Error("a signed S4 torsion orbit does not restrict to exactly one D8 torsion orbit");
            fi;

            counts := List(orbits, orbit -> 0);
            for element in PrimaryTransferBoundary do
                coset := RightCoset(subgroup, element^-1);
                position := PositionProperty(orbits, orbit -> coset in orbit);
                if position = fail then
                    Error("a boundary image is absent from the D8 orbit partition");
                fi;
                counts[position] := counts[position] + 1;
            od;

            odd_positions := Filtered(
                [1..Length(counts)],
                position -> IsOddInt(counts[position]));
            if odd_positions <> torsion_orbits then
                Error("the mod-two transfer is not the unique D8 torsion coordinate");
            fi;
        elif Length(torsion_orbits) <> 0 then
            Error("an orientable S4 orbit acquired D8 orientation torsion");
        fi;
    od;
    return [Length(all_subgroups), torsion_subgroups];
end;

PrimaryTransferResult := PrimaryTransferAudit();
Print("subgroups_checked=", PrimaryTransferResult[1],
      " torsion_subgroups=", PrimaryTransferResult[2],
      " unique_primary_transfer=true\n");
