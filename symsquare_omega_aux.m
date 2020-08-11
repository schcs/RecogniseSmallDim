import "smalldimreps.m":funcpos_symsquare, funcposinv_symsquare, 
  SolveSymSquareDimEq, BasisMatrixForSymSquareOmegaPlus, 
  BasisMatrixForSymSquareOmegaMinus, BasisMatrixForSymSquareOmega, 
  GetValueOmegaMinus;

import "smalldimreps.m":__funcSymSquareToSLdq, __funcSLdqToSymSquare;

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

OmegaPlusBasis := function( d1, d2, F : type := "Omega+", firsttype := "Omega+" )

    d := d1+d2;
    ranged1 := [1..d1 div 2] cat [d-d1 div 2 + 1..d];
    ranged2 := [d1 div 2 + 1 .. d-d1 div 2];
    len := d*(d+1) div 2;
    z1, z2 := GetValueOmegaMinus( #F );

    mat := ZeroMatrix( F, len );
    rowcount := 0;
    mid := case< firsttype | "Omega+": <d1 div 2, d-d1 div 2 + 1>, 
                             "Omega-": <d-d1 div 2 +1,d-d1 div 2 +1>,
                             default: false >; 
    posmid := funcpos_symsquare( d, mid[1], mid[2] );
    midvalue := case< firsttype | "Omega+": -1, "Omega-": z1, default: false >;

    for i in ranged1 do
        for j in [ x : x in ranged1 | i le x ] do
            if <i,j> ne mid then
                pos, v := funcpos_symsquare( d, i, j );
                rowcount := rowcount + 1;
                mat[rowcount,pos] := 1;
                if i+j eq d+1 and i ne d1/2 then
                    mat[rowcount,posmid] := midvalue;
                end if;
                if firsttype eq "Omega-" and <i,j>  eq <d1 div 2, d1 div 2 > then 
                    mat[rowcount,posmid] := midvalue;
                end if;
            end if;
        end for;
    end for;
   
   mid := case< type | "Omega+": <d div 2, d div 2 + 1 >,
                       "Omega-": <d div 2+1, d div 2 + 1 >, 
                       "Omega": <d div 2+1, d div 2 + 1 >,
                       default: false >;
   
   minusval := case< type | "Omega+": -1, "Omega-": z1, "Omega": -2, default: false >;
   posmid := funcpos_symsquare( d, mid[1], mid[2]);
   for i in ranged2 do
        for j in [ x : x in ranged2 | i le x ] do
            if <i,j> ne mid then 
                pos, v := funcpos_symsquare( d, i, j );
                rowcount := rowcount + 1;
                mat[rowcount,pos] := 1;
                if i+j eq d+1 and i ne d/2 then
                    mat[rowcount,posmid] := minusval;
                end if;
                if type eq "Omega-" and <i,j>  eq <d div 2, d div 2 > then 
                        mat[rowcount,posmid] := minusval;
                end if;
            end if;
        end for;
    end for;

    for i in ranged1 do 
        for j in ranged2 do
            rowcount := rowcount + 1;
            pos, v := funcpos_symsquare( d, i, j );
            mat[rowcount,pos] := 1;
        end for;
    end for;

    rowcount := rowcount + 1;
    for i in [1..d1 div 2-1 ] do
        pos := funcpos_symsquare( d, i, d-i+1 );
        mat[rowcount,pos] := 1;
    end for;

    if firsttype eq "Omega+" then 
        pos := funcpos_symsquare( d, d1 div 2, d-d1 div 2 + 1 );
        mat[rowcount,pos] := 1;
    elif firsttype eq "Omega-" then 
        pos := funcpos_symsquare( d, d1 div 2, d1 div 2  );
        mat[rowcount,pos] := 1/2;
        pos := funcpos_symsquare( d, d-d1 div 2+1, d - d1 div 2 + 1 );
        mat[rowcount,pos] := z2;
    end if; 

    rowcount := rowcount + 1;
    for i in [1..d div 2-1] do
        pos := funcpos_symsquare( d, i, d-i+1 );
        mat[rowcount,pos] := 1;
    end for;

    if type eq "Omega+" then 
        pos := funcpos_symsquare( d, d div 2, d div 2 + 1 );
        mat[rowcount,pos] := 1;
        // TEMP FIX
        mat[rowcount] := mat[rowcount] - mat[rowcount-1];
    elif type eq "Omega-" then 
        pos := funcpos_symsquare( d, d div 2, d div 2  );
        mat[rowcount,pos] := 1/2;
        pos := funcpos_symsquare( d, d div 2+1, d div 2+1  );
        mat[rowcount,pos] := z2;
        // TEMP FIX
        mat[rowcount] := mat[rowcount] - mat[rowcount-1];

    elif type eq "Omega" then 
        pos := funcpos_symsquare( d, d div 2, d div 2+2  );
        mat[rowcount,pos] := 1;
        pos := funcpos_symsquare( d, d div 2+1, d div 2+1  );
        mat[rowcount,pos] := 1;
        // TEMP FIX !!!!
        mat[rowcount] := mat[rowcount] - mat[rowcount-1];
    end if;

    return mat;
end function;

BuildBasisOmega := function( basH, basK, basT : type := "Omega+", 
                                                firsttype := "Omega+", 
                                                wH, wK, 
                                                scalars := [1,1,1,1] )

    dH := SolveSymSquareDimEq( #basH : type := "Omega+" ); 
    dK := SolveSymSquareDimEq( #basK : type := "Omega+" );

    a := scalars[1]; b := scalars[2]; c := scalars[3];
    d := scalars[4]; 
    if Category( wK ) eq BoolElt then wK := -wH; end if;
              
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
        wH := d*wH; wK := d*wK;
    end if;

    basall := basH cat basK cat basT cat [ wH ] cat [ wK ];
    mat := OmegaPlusBasis( dH, dK, GF( q ) : type := type, firsttype := firsttype );
    M0 := case< type | "Omega+": BasisMatrixForSymSquareOmegaPlus( dH+dK, GF(q) ),
                       "Omega-": BasisMatrixForSymSquareOmegaMinus( dH+dK, GF(q) ),
                       "Omega":  BasisMatrixForSymSquareOmega( dH+dK, GF(q) ),
                       default: false >;
    mat := M0*mat^-1; 
    bas := [ &+[ mat[i,j]*basall[j] : j in [1..#basall]] : i in [1..#basall-1]];

    if wH eq 0*wH then
        bas := Matrix( GF( q ), #bas-1, #basall-2, [ bas[i,j] : j in [1..#basall-2], 
                                             i in [1..#bas-1]] );
    else 
        bas := Matrix( GF( q ), #bas, #basall-1, [ bas[i,j] : j in [1..#basall-1], 
                                             i in [1..#bas]] );
    end if;
    
    return bas;
end function;


TestBasisOmega := function( basH, basK, basT, wH, wK, g : type := "Omega+" )
    
    scalars := [ <a,b,c,d > : a in [1,-1], b in [1,-1], c in [1,-1], 
                 d in [1,-1]]; 
    results := [];
    maxzero := 0;
    F := CoefficientRing( g );
    BuildBasis := case< type | "Omega+": BuildBasisOmega,
                               "Omega-": BuildBasisOmega,
                               "Omega": BuildBasisOmega, 
                               default: false >;

    for s in scalars do 
        bas := BuildBasis( basH, basK, basT : wH := wH, type := type,
                       scalars := [s[1], s[2], s[3], s[4]] );
        x0 := Random( g );
        try
          x := bas*x0*bas^-1;
          y := __funcSymSquareToSLdq( x : type := type );
          x1 := __funcSLdqToSymSquare( y : type := type );
          if x*x1^-1 eq x^0 then
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
    
    return true in results, maxzero;
end function;