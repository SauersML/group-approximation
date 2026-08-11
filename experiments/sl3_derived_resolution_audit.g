# Audit HAP's derived free resolution of the proper SL(3,Z) cell complex.
#
# Load HAP before reading this file and bind DERIVED_AUDIT_OUTPUT to the
# desired output path.  The output records the finite stabilizers, the
# bidegree decomposition of the Wall total complex, and coefficient-l1
# Schur data for its differentials.

if not IsBound(FreeGResolution) then
    Error("load HAP before reading sl3_derived_resolution_audit.g");
fi;
if not IsBound(DERIVED_AUDIT_OUTPUT) then
    Error("DERIVED_AUDIT_OUTPUT is not bound");
fi;

DerivedAuditActionValues := function(complex, degree, generator, stabilizer)
    local values, element, position;
    values := [];
    for element in Elements(stabilizer) do
        position := Position(complex!.elts, element);
        if position = fail then
            Add(complex!.elts, element);
            position := Length(complex!.elts);
        fi;
        AddSet(values, complex!.action(degree, generator, position));
    od;
    return values;
end;

DerivedAuditRun := function(path)
    local complex, resolution, stream, cellular_dimensions, free_dimensions,
          degree, generator, stabilizer, identifier, action_values, quad,
          boundary, target_types, term, column_counts, row_counts;

    complex := ContractibleGcomplex("SL(3,Z)");
    resolution := FreeGResolution(complex, 3);
    cellular_dimensions := List([0..3], complex!.dimension);
    free_dimensions := List([0..3], resolution!.dimension);

    stream := OutputTextFile(path, false);
    SetPrintFormattingStatus(stream, false);
    AppendTo(stream, "META cellular_dimensions ", cellular_dimensions, "\n");
    AppendTo(stream, "META free_dimensions ", free_dimensions, "\n");

    for degree in [0..3] do
        for generator in [1..complex!.dimension(degree)] do
            stabilizer := complex!.stabilizer(degree, generator);
            identifier := IdGroup(Image(RegularActionHomomorphism(stabilizer)));
            action_values := DerivedAuditActionValues(
                complex, degree, generator, stabilizer);
            AppendTo(stream, "STABILIZER ", degree, " ", generator, " ",
                Order(stabilizer), " ", identifier, " ", action_values, "\n");
        od;
    od;

    for degree in [0..3] do
        for generator in [1..resolution!.dimension(degree)] do
            quad := resolution!.pair2Quad(degree, generator);
            if degree = 0 then
                boundary := [];
                target_types := [];
            else
                boundary := resolution!.boundary(degree, generator);
                target_types := Set(List(boundary, term ->
                    resolution!.pair2Quad(
                        degree - 1, AbsoluteValue(term[1])){[1,3]}));
            fi;
            AppendTo(stream, "GENERATOR ", degree, " ", generator, " ",
                quad, " ", Length(boundary), " ", target_types, "\n");
        od;
    od;

    for degree in [1..3] do
        column_counts := List([1..resolution!.dimension(degree)],
            generator -> Length(resolution!.boundary(degree, generator)));
        row_counts := ListWithIdenticalEntries(
            resolution!.dimension(degree - 1), 0);
        for generator in [1..resolution!.dimension(degree)] do
            for term in resolution!.boundary(degree, generator) do
                row_counts[AbsoluteValue(term[1])] :=
                    row_counts[AbsoluteValue(term[1])] + 1;
            od;
        od;
        AppendTo(stream, "SCHUR ", degree, " ", column_counts, " ",
            row_counts, " ", Maximum(column_counts), " ",
            Maximum(row_counts), " ",
            Maximum(column_counts) * Maximum(row_counts), "\n");
    od;

    CloseStream(stream);
    Print("derived resolution audit written to ", path, "\n");
end;

DerivedAuditRun(DERIVED_AUDIT_OUTPUT);
