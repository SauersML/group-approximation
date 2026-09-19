# Direct orientation-primary audit in the natural three-dimensional model.
#
# Load HAP and bind PRIMARY_NATURAL_PRIMES before reading this file.  Unlike
# the full cellular exporter, this script never writes the projective
# permutations.  It works directly on P^2(F_p), checks the residual matching
# law, and prints one compact exact row per prime.

if not IsBound(FreeGResolution) then
    Error("load HAP before reading sl3_projective_primary_natural_audit.g");
fi;
if not IsBound(PRIMARY_NATURAL_PRIMES) then
    Error("PRIMARY_NATURAL_PRIMES is not bound");
fi;

PrimaryNaturalReduce := function(value, field, prime)
    local one;
    one := One(field);
    return ImmutableMatrix(field, List(
        value, row -> List(row, entry -> (entry mod prime) * one)));
end;

PrimaryNaturalOrientation := function(complex, degree, cell, element)
    local position;
    position := Position(complex!.elts, element);
    if position = fail then
        Add(complex!.elts, element);
        position := Length(complex!.elts);
    fi;
    return complex!.action(degree, cell, position);
end;

PrimaryNaturalBadOrbits := function(
        complex, degree, cell, points, field, prime)
    local stabilizer, reduced_group, orbits, bad, orbit, representative,
          element;
    stabilizer := complex!.stabilizer(degree, cell);
    reduced_group := Group(List(
        GeneratorsOfGroup(stabilizer),
        element -> PrimaryNaturalReduce(element, field, prime)));
    orbits := OrbitsDomain(reduced_group, points, OnLines);
    bad := [];
    for orbit in orbits do
        representative := orbit[1];
        if ForAny(Elements(stabilizer), element ->
            OnLines(
                representative,
                PrimaryNaturalReduce(element, field, prime)) = representative
            and PrimaryNaturalOrientation(
                complex, degree, cell, element) = -1) then
            Add(bad, orbit);
        fi;
    od;
    return bad;
end;

PrimaryNaturalComplex := ContractibleGcomplex("SL(3,Z)a");

PrimaryNaturalRun := function(prime)
    local complex, field, one, zero, reduced_group, points, source_orbits,
          target_orbits, boundary_elements, rows, columns, orbit,
          representative, element, image, target, row, row_weights,
          column_weights, chi, expected;

    complex := PrimaryNaturalComplex;
    field := GF(prime);
    one := One(field);
    zero := Zero(field);
    reduced_group := Group(List(
        GeneratorsOfGroup(complex!.group),
        element -> PrimaryNaturalReduce(element, field, prime)));
    points := Orbit(reduced_group, [one, zero, zero], OnLines);
    if Length(points) <> prime^2 + prime + 1 then
        Error("the natural action did not produce the projective plane");
    fi;

    source_orbits := PrimaryNaturalBadOrbits(
        complex, 3, 1, points, field, prime);
    target_orbits := PrimaryNaturalBadOrbits(
        complex, 2, 2, points, field, prime);
    boundary_elements := List(
        Filtered(complex!.boundary(3, 1), term -> AbsInt(term[1]) = 2),
        term -> complex!.elts[term[2]]);
    if Length(boundary_elements) <> 6 then
        Error("unexpected residual cellular boundary width");
    fi;

    rows := [];
    columns := ListWithIdenticalEntries(Length(target_orbits), 0);
    for orbit in source_orbits do
        representative := orbit[1];
        row := ListWithIdenticalEntries(Length(target_orbits), 0);
        for element in boundary_elements do
            image := OnLines(
                representative,
                PrimaryNaturalReduce(element, field, prime));
            target := PositionProperty(target_orbits, candidate -> image in candidate);
            if target <> fail then
                row[target] := (row[target] + 1) mod 2;
            fi;
        od;
        Add(rows, row);
    od;
    row_weights := List(rows, row -> Number(row, value -> value = 1));
    for row in rows do
        for target in [1..Length(row)] do
            if row[target] = 1 then
                columns[target] := columns[target] + 1;
            fi;
        od;
    od;
    column_weights := columns;

    chi := Legendre(-1, prime);
    expected := [
        (prime + 4 + chi) / 2,
        prime + 2,
        (3 + chi) / 2,
        (prime + 1) / 2,
        1,
        prime + 1,
    ];
    if [
        Length(source_orbits),
        Length(target_orbits),
        Number(row_weights, weight -> weight = 0),
        Number(row_weights, weight -> weight = 2),
        Number(column_weights, weight -> weight = 0),
        Number(column_weights, weight -> weight = 1),
    ] <> expected then
        Error("the residual matching law failed");
    fi;
    if not ForAll(row_weights, weight -> weight = 0 or weight = 2) then
        Error("unexpected residual row weight");
    fi;
    if not ForAll(column_weights, weight -> weight = 0 or weight = 1) then
        Error("unexpected residual column weight");
    fi;

    Print("prime=", prime,
          " source=", Length(source_orbits),
          " target=", Length(target_orbits),
          " zero_rows=", Number(row_weights, weight -> weight = 0),
          " weight_two_rows=", Number(row_weights, weight -> weight = 2),
          " zero_columns=", Number(column_weights, weight -> weight = 0),
          " weight_one_columns=", Number(column_weights, weight -> weight = 1),
          " matching_law=true\n");
end;

for PrimaryNaturalPrime in PRIMARY_NATURAL_PRIMES do
    PrimaryNaturalRun(PrimaryNaturalPrime);
od;
