// TO BE DELETED

OmegaPlusSubspace := function( d1, d2, F )    
    
    d := d1 + d2;
    V := VectorSpace( F, d div 2 );
    
    vecs := [];
    
    for i in [1..d1 div 2 - 1] do
        v := Zero( V );
        v[i] := 1; v[d1 div 2] := -1;
        Append( ~vecs, v );
    end for;
    
    Append( ~vecs, V!([1 : i in [1..d1 div 2]] cat 
                [ 0 : i in [1..d2 div 2]]));
    
    for i in [1..d2 div 2-1] do
        v := Zero( V );
        v[d1 div 2 + i] := 1; v[d div 2] := -1;
        Append( ~vecs, v );
    end for;
    
        Append( ~vecs, V!([0 : i in [1..d1 div 2]] cat 
                [ 1 : i in [1..d2 div 2]]));
    
    return VectorSpaceWithBasis( vecs );
end function;

OmegaMinusSubspace := function( d1, d2, F )

    d := d1 + d2;
    V := VectorSpace( F, d div 2 + 1 );
    
    vecs := [];
    
    for i in [1..d1 div 2 - 1] do
        v := Zero( V );
        v[i] := 1; v[d1 div 2] := -1;
        Append( ~vecs, v );
    end for;
    
    Append( ~vecs, V!([1 : i in [1..d1 div 2]] cat 
                [ 0 : i in [1..d2 div 2+1]]));
    
    for i in [1..d2 div 2] do
        v := Zero( V );
        v[d1 div 2 + i] := 1; v[d div 2+1] := -1;
        Append( ~vecs, v );
    end for;
    
        Append( ~vecs, V!([0 : i in [1..d1 div 2]] cat 
                [ 1 : i in [1..d2 div 2-1]] cat [1/2,1/2]));
    
    return VectorSpaceWithBasis( vecs );
end function;

// end of TO BE DELETED