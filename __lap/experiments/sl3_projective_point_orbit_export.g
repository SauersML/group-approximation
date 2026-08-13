# Export selected points from the projective coefficient orbit at prime-power
# level.  This is a lightweight companion to
# sl3_projective_cellular_prime_power_export.g: it reproduces exactly the same
# breadth-first orbit order without constructing any cellular boundary.
#
# Before reading this file, load HAP and bind:
#
#   PROJECTIVE_POINT_LEVEL
#   PROJECTIVE_POINT_OUTPUT
#   PROJECTIVE_POINT_INDICES   (optional, zero-based indices)

if not IsBound(ContractibleGcomplex) then
    Error("load HAP before reading sl3_projective_point_orbit_export.g");
fi;
if not IsBound(PROJECTIVE_POINT_LEVEL) then
    Error("PROJECTIVE_POINT_LEVEL is not bound");
fi;
if not IsBound(PROJECTIVE_POINT_OUTPUT) then
    Error("PROJECTIVE_POINT_OUTPUT is not bound");
fi;

ProjectivePointReduceMatrix := function(value, modulus)
    return List(value, row -> List(row, entry -> Int(entry mod modulus)));
end;

ProjectivePointCanonicalLine := function(value, modulus)
    local entries, pivot, inverse, result;
    entries := List(value, entry -> Int(entry mod modulus));
    pivot := First([1..Length(entries)],
        index -> GcdInt(entries[index], modulus) = 1);
    if pivot = fail then
        Error("projective vector is not unimodular");
    fi;
    inverse := PowerModInt(entries[pivot], -1, modulus);
    result := List(entries, entry -> Int((entry * inverse) mod modulus));
    MakeImmutable(result);
    return result;
end;

ProjectivePointRowAction := function(value, matrix, modulus)
    local dimension;
    dimension := Length(value);
    return ProjectivePointCanonicalLine(
        List([1..dimension], column -> Int(Sum([1..dimension],
            row -> value[row] * matrix[row][column]) mod modulus)),
        modulus);
end;

ProjectivePointOrbit := function(generators, modulus)
    local reduced_generators, base, orbit, positions, head, generator, image;
    reduced_generators := List(generators,
        generator -> ProjectivePointReduceMatrix(generator, modulus));
    base := ListWithIdenticalEntries(Length(reduced_generators[1]), 0);
    base[1] := 1;
    MakeImmutable(base);
    orbit := [base];
    positions := NewDictionary(base, true);
    AddDictionary(positions, base, 1);
    head := 1;
    while head <= Length(orbit) do
        for generator in reduced_generators do
            image := ProjectivePointRowAction(
                orbit[head], generator, modulus);
            if LookupDictionary(positions, image) = fail then
                Add(orbit, image);
                AddDictionary(positions, image, Length(orbit));
            fi;
        od;
        head := head + 1;
    od;
    return orbit;
end;

ProjectivePointExportRun := function(modulus, path, selected)
    local factors, prime, exponent, expected_degree, complex, orbit, indices,
          stream, index, point;
    factors := FactorsInt(modulus);
    if Length(factors) = 0 or Length(Set(factors)) <> 1 then
        Error("the projective level must be a prime power");
    fi;
    prime := factors[1];
    exponent := Length(factors);
    expected_degree := prime^(2 * (exponent - 1))
        * (prime^2 + prime + 1);
    complex := ContractibleGcomplex("SL(3,Z)");
    orbit := ProjectivePointOrbit(
        GeneratorsOfGroup(complex!.group), modulus);
    if Length(orbit) <> expected_degree then
        Error("projective orbit has the wrong degree");
    fi;
    if selected = fail then
        indices := [0..Length(orbit) - 1];
    else
        indices := Set(selected);
    fi;
    if ForAny(indices, index -> index < 0 or index >= Length(orbit)) then
        Error("selected projective point index is out of range");
    fi;
    stream := OutputTextFile(path, false);
    SetPrintFormattingStatus(stream, false);
    AppendTo(stream, "META ", modulus, " ", Length(orbit), "\n");
    for index in indices do
        point := orbit[index + 1];
        AppendTo(stream, "POINT ", index, " ",
            JoinStringsWithSeparator(List(point, String), ","), "\n");
    od;
    CloseStream(stream);
    Print("level=", modulus, " projective_degree=", Length(orbit),
          " exported_points=", Length(indices), "\n");
end;

if IsBound(PROJECTIVE_POINT_INDICES) then
    ProjectivePointExportRun(
        PROJECTIVE_POINT_LEVEL,
        PROJECTIVE_POINT_OUTPUT,
        PROJECTIVE_POINT_INDICES);
else
    ProjectivePointExportRun(
        PROJECTIVE_POINT_LEVEL,
        PROJECTIVE_POINT_OUTPUT,
        fail);
fi;
