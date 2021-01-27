import "smalldimreps.m":funcpos_altsquare, funcposinv_altsquare, 
  SolveAltSquareDimEq;

import "smalldimreps.m":__funcAltSquareToSLdq, __funcSLdqToAltSquare;

SpTransformMatrix := function( d1, d2, F )
    
    d := d1+d2;
    assert IsEven( d );
    
    M := ZeroMatrix( F, d div 2, d div 2 );
    
    for i in [1..d1 div 2-1] do
        M[i,i] := 1;
        M[i,d1 div 2] := -1;
    end for;
    
    for i in [1..d1 div 2] do
        M[d1 div 2,i] := 1;
    end for;
    
    for i in [1..d2 div 2-1] do
        M[d1 div 2+i,d1 div 2+i] := 1;
        M[d1 div 2+i,(d1 div 2)+(d2 div 2)] := -1;
    end for;
    
    for i in [1..d2 div 2] do
        M[(d1 div 2) + (d2 div 2),(d1 div 2 + i)] := 1;
    end for;
    
    
    return M;
end function; 
    
SpSubspace := function( d1, d2, F : pdividesd := false )    
    
    d := d1 + d2;
    V := VectorSpace( F, d div 2 );
    
    vecs := [];
    
    for i in [1..d1 div 2 - 1] do
        v := Zero( V );
        v[i] := 1; v[d1 div 2] := -1;
        Append( ~vecs, v );
    end for;
    
    if not pdividesd then 
        Append( ~vecs, V!([1 : i in [1..d1 div 2]] cat 
                [ 0 : i in [1..d2 div 2]]));
    end if;
    
    for i in [1..d2 div 2-1] do
        v := Zero( V );
        v[d1 div 2 + i] := 1; v[d div 2] := -1;
        Append( ~vecs, v );
    end for;
    
    if not pdividesd then 
        Append( ~vecs, V!([0 : i in [1..d1 div 2]] cat 
                [ 1 : i in [1..d2 div 2]]));
    else
        Append( ~vecs, V![ 1 : i in [1..d div 2]] );
    end if;
    
    return VectorSpaceWithBasis( vecs );
end function;
    
/* Builds standard basis for V given standard bases for H, K and 
   T = H tensor K */
            
BuildBasis := function( basH, basK, basT : wH, scalars := [1,1,1,1] )

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
              
    dH := SolveAltSquareDimEq( #basH : type := "Sp" ); 
    dK := SolveAltSquareDimEq( #basK : type := "Sp" );
    d := dH + dK;
    pdividesd := d mod p eq 0;
    rangeH := [1..dH/2] cat [dH/2+dK+1..d];
    rangeK := [dH/2+1..dH/2+dK];
    
    trmat := SpTransformMatrix( dH, dK, GF( q )); 
    subsp := SpSubspace( dH, dK, GF( q ) : pdividesd := (d mod p) eq 0 );
    vecs_ex := [ basH[ funcpos_altsquare( dH, i, dH-i+1 : type := "Sp" )] :
                 i in [1..dH/2-1]];
    
    if not pdividesd then
        vecs_ex := vecs_ex cat [ bone1 ];
    end if;
    
    vecs_ex := vecs_ex cat [ basK[ funcpos_altsquare( dK, i, dK-i+1 : 
                       type := "Sp" )] : i in [1..dK/2-1]];
    
    if not pdividesd then
        vecs_ex := vecs_ex cat [ -bone1 ];
    else
        vecs_ex := vecs_ex cat [ 0*bone1 ];
        vecs_ex := vecs_ex cat [ 0*bone1 ];
    end if;
    
    for i in [1..d] do
        for j in [i+1..d] do
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
                    
                    vec := basH[ funcpos_altsquare( dH, i0, j0 : 
                                   type := "Sp" )];
                    bas[ funcpos_altsquare( d, i, j : type := "Sp" )] := vec;
                    
                else
                    
                    V := VectorSpace( GF( q ), d div 2 );
                    vec := Zero( V );
                    vec[i0] := 1; vec[d div 2] := -1;
                    // vec := vec*trmat^-1;
                    vec := Coordinates( subsp, vec );
                    if pdividesd then Append( ~vec, 0 ); end if;
                    vec := &+[ vec[i]*vecs_ex[i] : i in [1..d/2]];
                    bas[ funcpos_altsquare( d, i, j : type := "Sp" )] := vec;
                    
                end if;
                
            elif i0 in rangeK and j0 in rangeK then
                
                i0 := i0 - dH div 2;
                j0 := j0 - dH div 2;
                if i0 + j0 ne dK +1 then
                    
                    vec := basK[ funcpos_altsquare( dK, i0, j0 : 
                                   type := "Sp" )];
                    bas[ funcpos_altsquare( d, i, j : type := "Sp" )] := vec;
                    
                else
                    V := VectorSpace( GF( q ), d div 2 );
                    vec := Zero( V );
                    vec[dH div 2+i0] := 1; vec[ d div 2 ] := -1;
                    
                    //vec := vec*trmat^-1;
                    vec := Coordinates( subsp, vec );
                    if pdividesd then Append( ~vec, 0 ); end if;
                    vec := &+[ vec[i]*vecs_ex[i] : i in [1..d/2]];
                    bas[ funcpos_altsquare( d, i, j : type := "Sp" )] := vec;

                end if;
                
            elif i0 in rangeH and j0 in rangeK then
                
                vec := basT[(i0-1)*dK+j0-dH div 2];
                bas[ funcpos_altsquare( d, i, j : type := "Sp" )] := vec;
                
            elif i0 in rangeK and j0 in rangeH then
                                
                vec := basT[(j0-dK-1)*dK+i0-dH div 2];
                bas[ funcpos_altsquare( d, i, j : type := "Sp" )] := -vec;
                
            end if;
        end for;
    end for;
    
    if d mod p eq 0 then
        bas := Remove( bas, 
        funcpos_altsquare( d, (d div 2) -1, (d div 2) + 2 ));
    end if;
                    
    return Matrix( GF( q ), #bas, #bas, [ [ y[i] : i in [1..#bas]] 
                   : y in bas ]);
end function;

TestBasis := function( basH, basK, basT, wH, wK, g )
    
    scalars := [ <a,b,c,d > : a in [1,-1], b in [1,-1], c in [1,-1], 
                 d in [1,-1]]; 
    results := [];
    maxzero := 0;
    
    for s in scalars do 
        bas := BuildBasis( basH, basK, basT : wH := wH,
                       scalars := [s[1], s[2], s[3], s[4]] );
        x0 := Random( g );
        try
          x := bas*x0*bas^-1;
          y := __funcAltSquareToSLdq( x : type := "Sp" );
          x1 := __funcSLdqToAltSquare( y : type := "Sp" );
          if x*x1^-1 eq x^0 then
              //print s[1], s[2], s[3], s[4], s[5];
              Append( ~results, true );
              return true, s;
          else 
              Append( ~results, false );
              els := Eltseq( x-x1 );
              poszero := #[ els[x] : x in [1..#els] | els[x] eq 0 ];
              if poszero gt maxzero then
                 maxzero := poszero;
                 maxs := s;
              end if;
          end if;
                            
          catch e 
            Append( ~results, false );
      end try;
    end for;
    
    return true in results, maxs, maxzero;
end function;
    
    
    
        