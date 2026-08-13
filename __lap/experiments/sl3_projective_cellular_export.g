# Export the rational projective Shapiro complex of the non-free
# SL(3,Z)-cellular resolution.
#
# Before reading this file, load HAP and bind:
#
#   PROJECTIVE_CELLULAR_PRIME
#   PROJECTIVE_CELLULAR_OUTPUT
#
# The output records signed stabilizer permutations and cellular boundary
# permutations.  A separate exact Sage program forms the signed coinvariants.

if not IsBound(ContractibleGcomplex) then
    Error("load HAP before reading sl3_projective_cellular_export.g");
fi;
if not IsBound(PROJECTIVE_CELLULAR_PRIME) then
    Error("PROJECTIVE_CELLULAR_PRIME is not bound");
fi;
if not IsBound(PROJECTIVE_CELLULAR_OUTPUT) then
    Error("PROJECTIVE_CELLULAR_OUTPUT is not bound");
fi;

ProjectiveCellularReduceMatrix := function(value, field, prime)
    local one;
    one := One(field);
    return ImmutableMatrix(field, List(
        value, row -> List(row, entry -> (entry mod prime) * one)));
end;

ProjectiveCellularRun := function(prime, path)
    local complex, group, generators, field, one, zero, finite_group, point,
          orbit, orbit_positions, degree, stream, permutation_cache,
          permutation, element, position, reduced, images, inverse_images,
          target, q, r, stabilizer, sign, word, term;

    complex := ContractibleGcomplex("SL(3,Z)");
    group := complex!.group;
    generators := GeneratorsOfGroup(group);
    field := GF(prime);
    one := One(field);
    zero := Zero(field);
    finite_group := Group(List(generators,
        generator -> ProjectiveCellularReduceMatrix(generator, field, prime)));
    point := [one, zero, zero, zero, zero, zero];
    orbit := Orbit(finite_group, point, OnLines);
    degree := prime^2 + prime + 1;
    if Length(orbit) <> degree then
        Error("symmetric-square line is not the projective-plane orbit");
    fi;
    orbit_positions := NewDictionary(orbit[1], true);
    for position in [1..degree] do
        AddDictionary(orbit_positions, orbit[position], position);
    od;

    permutation_cache := NewDictionary(One(group), true);
    permutation := function(element)
        local cached;
        cached := LookupDictionary(permutation_cache, element);
        if cached <> fail then
            return cached;
        fi;
        reduced := ProjectiveCellularReduceMatrix(element^-1, field, prime);
        images := List(orbit,
            orbit_point -> LookupDictionary(
                orbit_positions, OnLines(orbit_point, reduced)));
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
    AppendTo(stream, "META ", prime, " ", degree, " ",
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
                    JoinStringsWithSeparator(List(permutation(element), String), ","),
                    "\n");
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
    Print("prime=", prime, " projective_degree=", degree,
          " cellular_dimensions=", List([0..3], complex!.dimension), "\n");
end;

ProjectiveCellularRun(
    PROJECTIVE_CELLULAR_PRIME, PROJECTIVE_CELLULAR_OUTPUT);
