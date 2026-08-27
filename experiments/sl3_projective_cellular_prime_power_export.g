# Export the rational projective Shapiro complex at a prime-power level.
#
# Unlike sl3_projective_cellular_export.g, this file does not pass through a
# finite field.  It constructs the orbit of the Veronese line directly over
# Z/(p^k), canonically normalizing every unimodular row by its first unit
# coordinate.  This includes the next literature-certified cuspidal levels
# 121 and 169.
#
# Before reading this file, load HAP and bind:
#
#   PROJECTIVE_CELLULAR_LEVEL
#   PROJECTIVE_CELLULAR_OUTPUT

if not IsBound(ContractibleGcomplex) then
    Error("load HAP before reading sl3_projective_cellular_prime_power_export.g");
fi;
if not IsBound(PROJECTIVE_CELLULAR_LEVEL) then
    Error("PROJECTIVE_CELLULAR_LEVEL is not bound");
fi;
if not IsBound(PROJECTIVE_CELLULAR_OUTPUT) then
    Error("PROJECTIVE_CELLULAR_OUTPUT is not bound");
fi;

ProjectiveCellularPrimePowerReduceMatrix := function(value, modulus)
    return List(value, row -> List(row, entry -> Int(entry mod modulus)));
end;

ProjectiveCellularPrimePowerCanonicalLine := function(value, modulus)
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

ProjectiveCellularPrimePowerRowAction := function(value, matrix, modulus)
    local dimension;
    dimension := Length(value);
    return ProjectiveCellularPrimePowerCanonicalLine(
        List([1..dimension], column -> Int(Sum([1..dimension],
            row -> value[row] * matrix[row][column]) mod modulus)),
        modulus);
end;

ProjectiveCellularPrimePowerOrbit := function(generators, modulus)
    local reduced_generators, base, orbit, positions, head, generator, image;
    reduced_generators := List(generators,
        generator -> ProjectiveCellularPrimePowerReduceMatrix(
            generator, modulus));
    base := ListWithIdenticalEntries(
        Length(reduced_generators[1]), 0);
    base[1] := 1;
    MakeImmutable(base);
    orbit := [base];
    positions := NewDictionary(base, true);
    AddDictionary(positions, base, 1);
    head := 1;
    while head <= Length(orbit) do
        for generator in reduced_generators do
            image := ProjectiveCellularPrimePowerRowAction(
                orbit[head], generator, modulus);
            if LookupDictionary(positions, image) = fail then
                Add(orbit, image);
                AddDictionary(positions, image, Length(orbit));
            fi;
        od;
        head := head + 1;
    od;
    return [orbit, positions];
end;

ProjectiveCellularPrimePowerRun := function(modulus, path)
    local factors, prime, exponent, expected_degree, complex, group,
          generators, orbit_data, orbit, orbit_positions, degree, stream,
          permutation_cache, permutation, element, position, reduced,
          images, inverse_images, target, q, r, stabilizer, sign, word, term;

    factors := FactorsInt(modulus);
    if Length(factors) = 0 or Length(Set(factors)) <> 1 then
        Error("the projective level must be a prime power");
    fi;
    prime := factors[1];
    exponent := Length(factors);
    expected_degree := prime^(2 * (exponent - 1))
        * (prime^2 + prime + 1);

    complex := ContractibleGcomplex("SL(3,Z)");
    group := complex!.group;
    generators := GeneratorsOfGroup(group);
    orbit_data := ProjectiveCellularPrimePowerOrbit(generators, modulus);
    orbit := orbit_data[1];
    orbit_positions := orbit_data[2];
    degree := Length(orbit);
    if degree <> expected_degree then
        Error("symmetric-square orbit has the wrong projective degree");
    fi;

    permutation_cache := NewDictionary(One(group), true);
    permutation := function(element)
        local cached, orbit_point;
        cached := LookupDictionary(permutation_cache, element);
        if cached <> fail then
            return cached;
        fi;
        reduced := ProjectiveCellularPrimePowerReduceMatrix(
            element^-1, modulus);
        images := List(orbit, orbit_point -> LookupDictionary(
            orbit_positions,
            ProjectiveCellularPrimePowerRowAction(
                orbit_point, reduced, modulus)));
        if fail in images then
            Error("coefficient matrix did not preserve the orbit");
        fi;
        inverse_images := ListWithIdenticalEntries(degree, 0);
        for target in [1..degree] do
            inverse_images[images[target]] := target;
        od;
        if 0 in inverse_images then
            Error("coefficient action is not a permutation");
        fi;
        AddDictionary(permutation_cache, element, inverse_images);
        return inverse_images;
    end;

    stream := OutputTextFile(path, false);
    SetPrintFormattingStatus(stream, false);
    AppendTo(stream, "META ", modulus, " ", degree, " ",
        JoinStringsWithSeparator(
            List([0..3], q -> String(complex!.dimension(q))), ","), "\n");

    for q in [0..3] do
        for r in [1..complex!.dimension(q)] do
            stabilizer := complex!.stabilizer(q, r);
            AppendTo(stream, "CELL ", q, " ", r, " ",
                Order(stabilizer), "\n");
            for element in Elements(stabilizer) do
                position := Position(complex!.elts, element);
                if position = fail then
                    Add(complex!.elts, element);
                    position := Length(complex!.elts);
                fi;
                sign := complex!.action(q, r, position);
                AppendTo(stream, "STAB ", q, " ", r, " ", sign, " ",
                    JoinStringsWithSeparator(
                        List(permutation(element), String), ","), "\n");
            od;
            if q > 0 then
                word := complex!.boundary(q, r);
                for term in word do
                    element := complex!.elts[term[2]];
                    AppendTo(stream, "BOUND ", q, " ", r, " ",
                        term[1], " ",
                        JoinStringsWithSeparator(
                            List(permutation(element), String), ","), "\n");
                od;
            fi;
        od;
    od;
    CloseStream(stream);
    Print("level=", modulus, " prime=", prime, " exponent=", exponent,
          " projective_degree=", degree,
          " cellular_dimensions=", List([0..3], complex!.dimension), "\n");
end;

ProjectiveCellularPrimePowerRun(
    PROJECTIVE_CELLULAR_LEVEL, PROJECTIVE_CELLULAR_OUTPUT);
