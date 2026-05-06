
LoadPackage("qpa");

#######################
# Auxiliary Functions #
#######################

# The "VectorBasis" function returns "generators" as a basis of a vector space over "K".

DeclareOperation("VectorBasis",[IsField, IsList]);
InstallMethod( VectorBasis,
    "for a base field and a set of generators",
    [ IsField, IsList], 0,
    function( K , generators )

    local V;
    V := VectorSpace(K, generators, "basis");
    return Basis(V, generators);
end);

# The "Relation" function returns an element (that should be quotiented out later) given
# a path element "elt_path" that is a non-zero linear combination of paths in "basis" 
# with coefficients "coeffs" over "K". The "path_dict" is a dictionary to transform from
# a matrix element to a path element.

DeclareOperation("Relation",[IsList, IsList, IsDictionary, IsPositionalObjectRep, IsField]);
InstallMethod( Relation,
    "for a base field and a set of generators",
    [IsList, IsList, IsDictionary, IsPositionalObjectRep, IsField], 0,
    function(basis, coeffs, path_dict, elt_path, K)

    local relation, i;
    if coeffs = fail then
        return fail;
    else
        relation := elt_path;
        for i in [1..Length(basis)] do
            if coeffs[i] <> Zero(K) then
                relation := relation - (coeffs[i] * LookupDictionary(path_dict, basis[i]));
            fi;
        od;
    fi;
    return relation;
end);

# The "MatrixByDiagonalBlocks" function take a list of matrices "blocks" and a ring
# "R" and returns a new matrix over that ring made by arranging the "blocks" diagonally.
# e.g. if the "blocks" are all square you get the usual block diagonal matrix.

DeclareOperation("MatrixByDiagonalBlocks",[IsList, IsRing]);
InstallMethod( MatrixByDiagonalBlocks,
    "for a list of diagonal blocks of a matrix, and a ring",
    [IsList, IsRing], 0,
    function(blocks, R)

    local mat, n, m, c_index, i, a, b;
    n := Length(blocks);
    c_index := [0];

    for i in [1..n] do
        Add(c_index, Size(blocks[i]) + c_index[i]);
    od;
    m := Last(c_index);
    mat := NullMat(m,m,R);

    for i in [1..n] do
        a := c_index[i]+1;
        b := c_index[i+1];
        mat{[a..b]}{[a..b]} := blocks[i];
    od;
    return mat;
end);

# The "IdempotentsOfEndOverAlgebra" takes a path algebra module "M" and returns the
# principal idempotents of the endomorphism algebra. 

DeclareOperation("IdempotentsOfEndOverAlgebra",[IsPathAlgebraMatModule]);
InstallMethod( IdempotentsOfEndOverAlgebra,
    "for a representation of a quiver",
    [IsPathAlgebraMatModule], 0,
    function(M)

    local K, bsids, idemps, maps, mat, i;
    K := LeftActingDomain(M);
    bsids := BlockSplittingIdempotents(M);

    idemps := [];
    maps := NullMat(Dimension(M),Dimension(M),K); 
    for i in [1..Length(bsids)] do
        mat := MatrixByDiagonalBlocks(bsids[i]!.maps, K);
        Add(idemps, Immutable(mat));
    od;
        
    return idemps;
end);

#################
# Main Function #
#################

# M - module
# max_length - maximum path length for search in quiver
DeclareOperation("QuiverAndRelationsOfEndOfModule",[ IsPathAlgebraMatModule, IsInt]);
InstallMethod( QuiverAndRelationsOfEndOfModule,
    "for a representation of a quiver and a maximum search depth",
    [ IsPathAlgebraMatModule, IsInt], 0,
    function( M , max_length )

    local K, endo, radendo, radendo2, idemps, matrix, n_idemps, O, Arrows, 
        vertex_module_list, vertex_module_dict, reordered_arrows, n_arrows, 
        quiver_data, Q, KQ, path_dict, Relations, Elts, x, i, j, k, a, new_elts, 
        generators, y, y_path, basis, coeffs, len, B, next_list, x_path, f, b;

    K := LeftActingDomain(M);

    endo := EndOverAlgebra(M); 
    radendo := RadicalOfAlgebra(endo); 
    radendo2 := ProductSpace(radendo,radendo); 

    # The principle idempotents are found using the "IdempotentsOfEndOverAlgebra" 
    # function. These will correspond to the vertices of the quiver.
    
    idemps := IdempotentsOfEndOverAlgebra(M);
    n_idemps := Size(idemps);
    O := Immutable(Zero(endo));

    ##########
    # Quiver #
    ##########
    
    # The elements corresponding to the arrows come from the quotient of the radical
    # and radical squared "radendo / radendo2". They are found as preimage
    # representatives of the basis of this quotient space.

    # In a previous version of this code these elements were found by taking the 
    # basis elemtents of "radendo" which were not in "radendo2". For our application 
    # it gave an identical result, but this was changed so as to be more robust.

    f := NaturalHomomorphismBySubspace( radendo, radendo2 );
    b := Basis(Image(f));

    Arrows := [];
    for x in b do
        Add(Arrows, PreImagesRepresentative(f, x)); 
    od;

    n_arrows := Size(Arrows);

    # Here we create the quiver data as a list and a matrix. The arrows need to be in
    # the order given below so we can match them to the path algebra elements later. 
    
    quiver_data := [];
    reordered_arrows := [];
    matrix := NullMat(n_idemps,n_idemps);
    for i in [1..n_idemps] do
        for j in [1..n_idemps] do
            for k in [1..n_arrows] do
                if idemps[i] * Arrows[k] * idemps[j] = Arrows[k] then
                    Add(quiver_data, [i,j, Concatenation("a", String(k))]);
                    Add(reordered_arrows, Arrows[k]);
                    matrix[i][j] :=  matrix[i][j] + 1;
                fi;
            od;
        od;
    od;
    Arrows := reordered_arrows;

    Q:=Quiver(n_idemps, quiver_data);

    #############
    # Relations #
    #############

    KQ := PathAlgebra(K, Q);

    vertex_module_list := []; # vertex_module_list[i] = module associated to vertex i
    AssignGeneratorVariables(KQ);

    # First we initialise "path_dict", a dictionary that lets us go from a matrix 
    # to its corresponding path. We add the vertex and arrow elements to begin.
    
    path_dict := NewDictionary(O, true, endo); 
    for i in [1..n_idemps] do
        AddDictionary(path_dict, idemps[i], VerticesOfPathAlgebra(KQ)[i]);
        Add(vertex_module_list, 
          [VerticesOfPathAlgebra(KQ)[i], Image(BlockSplittingIdempotents(M)[i])]);
    od;
    for i in [1..n_arrows] do
        AddDictionary(path_dict, Arrows[i], ElementOfPathAlgebra(KQ, ArrowsOfQuiver(Q)[i]));
    od;

    # To find the relations we do a breadth first search through the paths.
    # i.e. first we look at the paths of length 2, then length 3 and so on.
    # When a new path is a linear combination of those that came before we have 
    # found a new relation, and we can exclude paths containing this one form 
    # the next stage of our search.

    Relations := [];
    Elts := [idemps, Arrows]; # The ith list in "Elts" will contain the paths of length i.

    len := 1;
    while Last(Elts) <> [] and len <= max_length do
        new_elts := [];
        for x in Last(Elts) do
            for i in [1..n_arrows] do
                # "y_path" corrsponds to "y = x * Arrows[i]".
                y_path := LookupDictionary(path_dict, x) * 
                    LookupDictionary(path_dict, Arrows[i]);
                if not IsZero(y_path) then
                    y := x * Arrows[i];
                    generators := Concatenation(Concatenation(Elts), new_elts);
                    basis := VectorBasis(K, generators);
                    coeffs := Coefficients(basis, y);
                    if  coeffs = fail then # coeffs = fail when we don't have a relation
                        Add(new_elts, y); # "y" will be incuded in the next seach step
                        AddDictionary(path_dict, y, y_path);
                    else
                        # Add new relation to the list
                        Add(Relations, Relation(basis, coeffs, path_dict, y_path, K));
                        # In this case we don't need to add "y" to "path_dict" as
                        # it is a linear combination of elements already in there.
                    fi;
                fi;
            od;
        od;
        Add(Elts, new_elts); # Add new elements to search over to list
        len := len + 1;
    od;

    if len > max_length then
        Display("Warning: search exceeded max_length; relations may not be complete.\n");
    fi;

    B := KQ/Relations;

    # B - the endomorhpsim algebra of M as a quiver algebra
    # Q - the quiver of B
    # matrix - the adjacency matrix of Q
    # quiver_data - list of vertices and edges of Q
    # vertex_module_list - list of modules associated to each vertex
    # Relations - the list of relations used to define B
    
    return [B, Q, matrix, quiver_data, vertex_module_list, Relations];
end);

