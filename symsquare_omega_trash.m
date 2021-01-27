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

OmegaSubspace := function( d1, d2, F : firsttype := "Omega+" )

    d := d1 + d2;
    V := VectorSpace( F, (d+1) div 2 );
    
    vecs := [];
    
    for i in [1..d1 div 2 - 1] do
        v := Zero( V );
        v[i] := 1; v[d1 div 2] := -1;
        Append( ~vecs, v );
    end for;
    
    Append( ~vecs, V!([1 : i in [1..d1 div 2]] cat 
                [ 0 : i in [1..(d2+1) div 2]]));

    for i in [1..(d2+1) div 2-1] do
        v := Zero( V );
        v[(d1+1) div 2 + i] := 1; v[(d+1) div 2] := -2;
        Append( ~vecs, v );
    end for;
    Append( ~vecs, V!([0 : i in [1..d1 div 2]] cat 
                [ 1 : i in [1..(d2+1) div 2]]));
    
    return Matrix( F, #vecs, #vecs, vecs );
end function;

BuildBasisOmegaPlus := function( basH, basK, basT : wH, scalars := [1,1,1,1] )

    a := scalars[1]; b := scalars[2]; c := scalars[3];
    d := scalars[4]; 
              
    q := #Field( Parent( basH[1] ));
    _, p := IsPrimePower( q );
    
    for v in [1..#basH] do
        basH[v] := a*basH[v];
    end for;
    
    for v in [1..#basK] do
        basK[v] := b*basK[v];
    end for;
    
    for v in [1..#basT] do
        basT[v] := c*basT[v];
    end for;
    
    if not Category( wH ) eq BoolElt then
        bone1 := d*wH;
    end if;
    
    bas := [];
              
    dH := SolveSymSquareDimEq( #basH : type := "Omega+" ); 
    dK := SolveSymSquareDimEq( #basK : type := "Omega+" );
    d := dH + dK;
    rangeH := [1..dH/2] cat [dH/2+dK+1..d];
    rangeK := [dH/2+1..dH/2+dK];
    
    subsp := OmegaPlusSubspace( dH, dK, GF( q )); 
    vecs_ex := [ basH[ funcpos_symsquare( dH, i, dH-i+1 : type := "Omega+" )] :
                 i in [1..dH/2-1]];
    vecs_ex := vecs_ex cat [ bone1 ];
    
    vecs_ex := vecs_ex cat [ basK[ funcpos_symsquare( dK, i, dK-i+1 : 
                       type := "Omega+" )] : i in [1..dK/2-1]];
    
    vecs_ex := vecs_ex cat [ -bone1 ];
    
    for i in [1..d] do
        for j in [i..d] do
            i0 := i; j0 := j;
            if <i0,j0> eq <d div 2,d div 2+1> then
                continue j;
            end if;
            if i0 in rangeH and j0 in rangeH then
                if i0 gt dH/2 then
                    i0 := i0 - dK;
                end if;
                
                if j0 gt dH/2 then
                    j0 := j0 - dK;
                end if;
                
                if i0+j0 ne dH+1 then
                    
                    vec := basH[ funcpos_symsquare( dH, i0, j0 : 
                                   type := "Omega+" )];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega+" )] := vec;
                    
                else
                    
                    V := VectorSpace( GF( q ), d div 2 );
                    vec := Zero( V );
                    vec[i0] := 1; vec[d div 2] := -1;
                    // vec := vec*trmat^-1;
                    vec := Coordinates( subsp, vec );
                    //error(111);
                    vec := &+[ vec[i]*vecs_ex[i] : i in [1..d/2]];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega+" )] := vec;
                    
                end if;
                
            elif i0 in rangeK and j0 in rangeK then
                
                i0 := i0 - dH div 2;
                j0 := j0 - dH div 2;
                if i0 + j0 ne dK +1 then
                    
                    vec := basK[ funcpos_symsquare( dK, i0, j0 : 
                                   type := "Omega+" )];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega+" )] := vec;
                    
                else
                    V := VectorSpace( GF( q ), d div 2 );
                    vec := Zero( V );
                    vec[dH div 2+i0] := 1; vec[ d div 2 ] := -1;
                    
                    //vec := vec*trmat^-1;
                    vec := Coordinates( subsp, vec );
                    vec := &+[ vec[i]*vecs_ex[i] : i in [1..d/2]];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega+" )] := vec;

                end if;
                
            elif i0 in rangeH and j0 in rangeK then
                
                vec := basT[(i0-1)*dK+j0-dH div 2];
                bas[ funcpos_symsquare( d, i, j : type := "Omega+" )] := vec;
                
            elif i0 in rangeK and j0 in rangeH then
                                
                vec := basT[(j0-dK-1)*dK+i0-dH div 2];
                bas[ funcpos_symsquare( d, i, j : type := "Omega+" )] := vec;
                
            end if;
        end for;
    end for;

    return Matrix( GF( q ), #bas, #bas, [ [ y[i] : i in [1..#bas]] 
                   : y in bas ]);
end function;

BuildBasisOmegaMinus := function( basH, basK, basT : wH, scalars := [1,1,1,1] )

    a := scalars[1]; b := scalars[2]; c := scalars[3];
    d := scalars[4]; 
              
    q := #Field( Parent( basH[1] ));
    _, p := IsPrimePower( q );
    
    for v in [1..#basH] do
        basH[v] := a*basH[v];
    end for;
    
    for v in [1..#basK] do
        basK[v] := b*basK[v];
    end for;
    
    for v in [1..#basT] do
        basT[v] := c*basT[v];
    end for;
    
    if not Category( wH ) eq BoolElt then
        bone1 := d*wH;
    end if;
    
    bas := [];
              
    dH := SolveSymSquareDimEq( #basH : type := "Omega+" ); 
    dK := SolveSymSquareDimEq( #basK : type := "Omega+" );
    d := dH + dK;
    rangeH := [1..dH/2] cat [dH/2+dK+1..d];
    rangeK := [dH/2+1..dH/2+dK];
    
    subsp := OmegaMinusSubspace( dH, dK, GF( q )); 
    vecs_ex := [ basH[ funcpos_symsquare( dH, i, dH-i+1 : type := "Omega+" )] :
                 i in [1..dH/2-1]];
    vecs_ex := vecs_ex cat [ bone1 ];
    
    vecs_ex := vecs_ex cat [ basK[ funcpos_symsquare( dK, i, dK-i+1 : 
                       type := "Omega-" )] : i in [1..dK/2-1]];
    vecs_ex := vecs_ex cat [ basK[ funcpos_symsquare( dK, dK div 2, dK div 2 : 
                                            type := "Omega-" )]];
    vecs_ex := vecs_ex cat [ -bone1 ];
    
    for i in [1..d] do
        for j in [i..d] do
            i0 := i; j0 := j;
            if <i0,j0> eq <d div 2+1,d div 2+1> then
                continue j;
            end if;
            if i0 in rangeH and j0 in rangeH then
                if i0 gt dH/2 then
                    i0 := i0 - dK;
                end if;
                
                if j0 gt dH/2 then
                    j0 := j0 - dK;
                end if;
                
                if i0+j0 ne dH+1 then
                    
                    vec := basH[ funcpos_symsquare( dH, i0, j0 : 
                                   type := "Omega+" )];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega-" )] := vec;
                    
                else
                    
                    V := VectorSpace( GF( q ), d div 2+1 );
                    vec := Zero( V );
                    vec[i0] := 1; vec[d div 2+1] := -1;
                    // vec := vec*trmat^-1;
                    vec := Coordinates( subsp, vec );
                    vec := &+[ vec[i]*vecs_ex[i] : i in [1..d/2+1]];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega-" )] := vec;
                    
                end if;
                
            elif i0 in rangeK and j0 in rangeK then
                
                i0 := i0 - dH div 2;
                j0 := j0 - dH div 2;
                if i0 eq dK/2 or i0 + j0 ne dK +1 then
                    
                    vec := basK[ funcpos_symsquare( dK, i0, j0 : 
                                   type := "Omega-" )];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega-" )] := vec;
                    
                else
                    V := VectorSpace( GF( q ), d div 2+1 );
                    vec := Zero( V );
                    vec[dH div 2+i0] := 1; vec[ d div 2+1 ] := -1;
                    
                    //vec := vec*trmat^-1;
                    vec := Coordinates( subsp, vec );
                    vec := &+[ vec[i]*vecs_ex[i] : i in [1..d/2+1]];
                    bas[ funcpos_symsquare( d, i, j : type := "Omega-" )] := vec;

                end if;
                
            elif i0 in rangeH and j0 in rangeK then
                
                vec := basT[(i0-1)*dK+j0-dH div 2];
                bas[ funcpos_symsquare( d, i, j : type := "Omega-" )] := vec;
                
            elif i0 in rangeK and j0 in rangeH then
                                
                vec := basT[(j0-dK-1)*dK+i0-dH div 2];
                bas[ funcpos_symsquare( d, i, j : type := "Omega-" )] := vec;
                
            end if;
        end for;
    end for;

    return Matrix( GF( q ), #bas, #bas, [ [ y[i] : i in [1..#bas]] 
                   : y in bas ]);
end function;


