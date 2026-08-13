# Export the Shapiro chain complex for a projective stabilizer.
#
# Before reading this file, load HAP and bind:
#
#   PROJECTIVE_H2_PRIME
#   PROJECTIVE_H2_OUTPUT_PREFIX
#
# HAP's generic TensorWithIntegralModule repeatedly solves a matrix-group
# word problem when evaluating the coefficient representation.  Here every
# coefficient element is instead reduced modulo p directly and applied to the
# known projective coset action.  This produces the same integral permutation
# chain complex without infinite-group preimage or word decomposition.

if not IsBound(ResolutionArithmeticGroup) then
    Error("load HAP before reading sl3_projective_h2_export.g");
fi;
if not IsBound(PROJECTIVE_H2_PRIME) then
    Error("PROJECTIVE_H2_PRIME is not bound");
fi;
if not IsBound(PROJECTIVE_H2_OUTPUT_PREFIX) then
    Error("PROJECTIVE_H2_OUTPUT_PREFIX is not bound");
fi;

ProjectiveH2ReduceMatrix := function(value, field, prime)
    local one;
    one := One(field);
    return ImmutableMatrix(field, List(
        value, row -> List(row, entry -> (entry mod prime) * one)));
end;

ProjectiveH2WriteBoundary := function(
        resolution, orbit, orbit_positions, field, prime, degree,
        chain_degree, path)
    local stream, source_rank, target_rank, cache, source, coordinate,
          word, term, element_index, reduced, images, inverse_images,
          target;
    source_rank := resolution!.dimension(chain_degree) * degree;
    target_rank := resolution!.dimension(chain_degree - 1) * degree;
    stream := OutputTextFile(path, false);
    SetPrintFormattingStatus(stream, false);
    AppendTo(stream, source_rank, " ", target_rank, "\n");
    cache := [];
    for source in [1..resolution!.dimension(chain_degree)] do
        word := resolution!.boundary(chain_degree, source);
        for coordinate in [1..degree] do
            for term in word do
                element_index := term[2];
                if not IsBound(cache[element_index]) then
                    reduced := ProjectiveH2ReduceMatrix(
                        resolution!.elts[element_index]^-1, field, prime);
                    images := List(orbit,
                        point -> LookupDictionary(
                            orbit_positions, OnLines(point, reduced)));
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
                    cache[element_index] := inverse_images;
                fi;
                target := cache[element_index][coordinate];
                AppendTo(stream,
                    (source - 1) * degree + coordinate - 1, " ",
                    (AbsoluteValue(term[1]) - 1) * degree + target - 1,
                    " ", SignInt(term[1]), "\n");
            od;
        od;
    od;
    CloseStream(stream);
    return [source_rank, target_rank];
end;

ProjectiveH2Run := function(prime, prefix)
    local resolution, group, generators, field, one, zero, reduced_generators,
          finite_group, point, orbit, orbit_positions, coordinate, degree,
          dimensions1, dimensions2, dimensions3;
    resolution := ResolutionArithmeticGroup("SL(3,Z)", 3);
    group := GroupOfResolution(resolution);
    generators := GeneratorsOfGroup(group);
    field := GF(prime);
    one := One(field);
    zero := Zero(field);
    reduced_generators := List(generators,
        generator -> ProjectiveH2ReduceMatrix(generator, field, prime));
    finite_group := Group(reduced_generators);
    point := [one, zero, zero, zero, zero, zero];
    orbit := Orbit(finite_group, point, OnLines);
    degree := prime^2 + prime + 1;
    if Length(orbit) <> degree then
        Error("symmetric-square line is not the projective-plane orbit");
    fi;
    orbit_positions := NewDictionary(orbit[1], true);
    for coordinate in [1..degree] do
        AddDictionary(orbit_positions, orbit[coordinate], coordinate);
    od;
    dimensions1 := ProjectiveH2WriteBoundary(
        resolution, orbit, orbit_positions, field, prime, degree, 1,
        Concatenation(prefix, "-d1.tsv"));
    dimensions2 := ProjectiveH2WriteBoundary(
        resolution, orbit, orbit_positions, field, prime, degree, 2,
        Concatenation(prefix, "-d2.tsv"));
    dimensions3 := ProjectiveH2WriteBoundary(
        resolution, orbit, orbit_positions, field, prime, degree, 3,
        Concatenation(prefix, "-d3.tsv"));
    Print("prime=", prime,
          " projective_degree=", degree,
          " d1=", dimensions1,
          " d2=", dimensions2,
          " d3=", dimensions3, "\n");
end;

ProjectiveH2Run(PROJECTIVE_H2_PRIME, PROJECTIVE_H2_OUTPUT_PREFIX);
