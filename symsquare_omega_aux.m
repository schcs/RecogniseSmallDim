import "smalldimreps.m":funcpos_symsquare, funcposinv_symsquare, 
  SolveSymSquareDimEq, BasisMatrixForSymSquareOmega, 
  GetValueOmegaMinus;

import "smalldimreps.m":__funcSymSquareToSLdq, __funcSLdqToSymSquare;
basisfromcomprecf := recformat< bas : AlgMatElt, vals : SeqEnum >;

SymProd := function( vec1, vec2 )

    d := Dimension( Parent( vec1 ));
    vec := [ 0*vec1[1] : x in [1..d*(d+1)/2]];
    for i in [1..d] do
        for j in [1..d] do
            a := vec1[i]*vec2[j];
            if a ne 0 then 
                pos := funcpos_symsquare( d, i, j );
                vec[pos] := vec[pos]+a;
            end if;
        end for;
    end for;

    return vec;
end function;

SymSquareBasis := function( bas )

    mat := [];
    F := CoefficientRing( Parent( bas[1] ));
    for i in [1..#bas] do
        for j in [i..#bas] do
            Append( ~mat, SymProd( bas[i], bas[j] ));
        end for;
    end for;

return Matrix( F, #mat, #mat[1], mat );
end function;

TensorProdBasis := function( bas1, bas2 )
    
    mat := [];
    F := CoefficientRing( Parent( bas1[1] ));

    for b1 in bas1 do
        for b2 in bas2 do
            Append( ~mat, SymProd( b1, b2 ));
        end for;
    end for;

return Matrix( F, #mat, #mat[1], mat );
end function;

AssignOmegaBasisFromComponents := procedure( ~G, d1, d2, F : 
                                    ww := 1/2,
                                    type := "Omega+", 
                                    typeh := "Omega+", 
                                    typek := "Omega+" )
    
    d := d1+d2;
    q := #F;
    V := VectorSpace( F, d );

    if type eq "Omega" and typeh eq "Omega-" then 
    
        i1 := d1 div 2; i2 := (d1+d2) div 2 + 1; i3 := d1 div 2+d2+1;
        v1 := V.i1; v2 := V.i2; v3 := V.i3;
    
        W := sub< V | v1, v2, v3 >;

        mat := ClassicalForms( OmegaMinus( 4, q ))`bilinearForm;

        w2w2 := ClassicalForms( OmegaMinus( 4, q ))`bilinearForm[3,3];

        f3 := ZeroMatrix( F, 3, 3 );
        f3[1,1] := 1;
        f3[3,3] := w2w2;
        f3[2,2] := ww;

        _formf3 := function( u, v )
            return u[1]*v[3]+1/2*u[2]*v[2]+u[3]*v[1];
        end function;

    /* if false and q eq 7 then
            tr := Matrix( F, 3, 3, [3,2,1,5,1,5,0,4,1]); 
        else 
            tr := TransformForm( f3, "orthogonalcircle" );
        end if; */
        
        tr := TransformForm( f3, "orthogonalcircle" );

        while (tr[3,1] eq 0 and tr[3,3] eq 0) or tr[2,2] eq 0 do
            tr := tr*Random( GO( 3, q ));
        end while;

        print tr;

        w1 := tr[1,1]*V.i1+tr[1,2]*V.i2+tr[1,3]*V.i3; 
        w2 := tr[2,1]*V.i1+tr[2,2]*V.i2+tr[2,3]*V.i3; 
        w3 := tr[3,1]*V.i1+tr[3,2]*V.i2+tr[3,3]*V.i3;

        bas1 := [ V.i : i in [1..d1 div 2 - 1]] cat [w1,w3] cat 
                [ V.i : i in [d-d1 div 2 + 2 .. d]];
        bas2 := [ V.i : i in [d1 div 2+1 .. d div 2 ]] cat [w2] cat 
                [ V.i : i in [d div 2 + 2 .. d-d1 div 2 ]];
    
    elif type eq "Omega+" and typeh eq "Omega-" then 

        error( "option not yet implemented" );

    else 

        bas1 := [ V.i : i in [1..d1 div 2 ]] cat [ V.i : i in [d-d1 div 2 + 1 .. d]];
        bas2 := [ V.i : i in [d1 div 2+1 .. d-d1 div 2 ]];

    end if;

    basH := SymSquareBasis( bas1 );
    basK := SymSquareBasis( bas2 );
    basT := TensorProdBasis( bas1, bas2 );

    dH := NumberOfRows( basH );
    dK := NumberOfRows( basK );
    dT := NumberOfRows( basT );

    bom := BasisMatrixForSymSquareOmega( typeh, #bas1, F ); 
    boc := BasisMatrixForSymSquareOmega( typek, #bas2, F : ww := ww );
    basH := [&+[ bom[i,j]*basH[j] : j in [1..dH]] : i in [1..dH]];
    basK := [&+[ boc[i,j]*basK[j] : j in [1..dK]] : i in [1..dK]];

    bas := basH[1..dH-1] cat basK[1..dK-1] cat basT[1..dT] cat [basH[dH]] cat 
            [basK[dK]];
    
    if type eq "Omega" and typeh eq "Omega-" then
        
        _form := function( i, j )
            
            if i+j eq d+1 and i ne (d+1) div 2 then 
                return 1;
            elif i eq (d+1) div 2 and j eq (d+1) div 2 then
                return 1/2;
            else 
                return 0;
            end if;
        end function;

        _form1 := function( u, v )

            s := 0;
            for i in [1..11] do
                for j in [1..11] do
                    s := s+u[i]*v[j]*_form( i, j );
                end for;
            end for;
            return s;
        end function;

        _formsymsquare := function( u, v )
            
            a := 0;

            for i in [1..d*(d+1)/2] do 
                for j in [1..d*(d+1)/2] do 
                    if u[i] ne 0 and v[j] ne 0 then 
                        pi := funcposinv_symsquare( d, i );
                        pj := funcposinv_symsquare( d, j );
                        a := a+u[i]*v[j]*( _form( pi[1], pj[1] )*_form( pi[2], pj[2] ) + 
                                       _form( pi[1], pj[2] )*_form( pi[2], pj[1] ))/2;
                    end if;
                end for;
            end for;

            return a;
        end function;

        wH := basH[#basH];
        wK := basK[#basK];
        a := Zero( Parent( wH ));
        a[d] := 1; a[funcpos_symsquare( d, (d+1) div 2, (d+1) div 2 )] := -2;

        aa := _formsymsquare( a, a );
        awH := _formsymsquare( a, wH );
        awK := _formsymsquare( a, wK );
        wHwH := _formsymsquare( wH, wH );
        wKwK := _formsymsquare( wK, wK );  
        
    else 

        aa := 0; awH := 0; awK := 0; wHwH := 0; wKwK := 0;            

    end if;
    
    bas := Matrix( F, dH+dK+dT, dH+dK+dT, [ Eltseq( x ) : x in bas ]);
    G`BasisMatrixFromComponents := rec< basisfromcomprecf | 
                                bas := bas, vals := [ aa, awH, awK, wHwH, wKwK ]>;

    // return bas, [aa, awH, awK, wHwH, wKwK];
end procedure;

OmegaBasisFromComponents := function( G )

    return G`BasisMatrixFromComponents`bas, G`BasisMatrixFromComponents`vals;
end function; 

/* this function determines the orthogonal type of the large component of the 
    symmetric square of Omega*( d, q ) */

TypeOfSymSquareOmega := function( type, d, q )

    if (type eq "Omega" and IsEven( d )) or 
        (type in {"Omega+", "Omega-"} and IsOdd( d )) then 
        return "false";
    end if;

    _, p := IsPrimePower( q );
    nrrows := case< type  |
        "Omega+": d div 2 - 1, "Omega-": d div 2+1, 
        "Omega": (d-1) div 2, default: false >;

    if d mod p eq 0 then nrrows := nrrows - 1; end if;

    if IsOdd( nrrows ) then 
        return "orthogonalcircle";
    end if; 

    if type eq "Omega+" then 
        a := 1/2; b := 1;
    elif type eq "Omega-" then
        x := GetValueOmegaMinus( GF( q )); 
        cf := ClassicalForms( OmegaMinus( 4, GF( q )))`bilinearForm;
        a := x^2*cf[3,3]^2;
        b := (1/2+x^2*cf[3,3]^2);
        c := (cf[2,2]^2+x^2*cf[3,3]^2);
    elif type eq "Omega" then 
        a := 1;
        b := 3/2;
    end if;

    mat := [ a : x in [1..nrrows^2]];
    mat := Matrix( GF( q ), nrrows, nrrows, mat );
    for i in [1..nrrows] do
        mat[i,i] := b;
    end for;

    if type eq "Omega-" then 
        mat[nrrows-1,nrrows-1] := c;
        for i in [1..nrrows-1] do
            mat[i,nrrows] := 0; mat[nrrows,i] := 0;
        end for;
        mat[nrrows,nrrows] := (cf[2,2]*cf[3,3]/2);
    end if;

    tr := TransformBilinearForm( mat );
    if tr[nrrows div 2, nrrows div 2] eq 0 then
        return "orthogonalplus";
    else
        return "orthogonalminus";
    end if;

end function;


BuildBasisOmega := function( G, basH, basK, basT : type := "Omega+", 
                                                typeh := "Omega+",
                                                typek := "Omega+", 
                                                wH, wK, 
                                                scalars := [1,1,1,1],
                                                ww := 1/2 )

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
    mat := OmegaBasisFromComponents( G );
                
    M0 := BasisMatrixForSymSquareOmega( type, dH+dK, GF( q ));
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


TestBasisOmega := function( G, basH, basK, basT, wH, wK, g : type := "Omega+", 
                                                          typeh := "Omega+", 
                                                          typek := "Omega+",
                                                          ww := ww )

    F := CoefficientRing( g );    
    scalars := [ <a,b,c,d > : a in [1,-1], b in [1,-1], c in [1,-1], 
                 d in [ 1, -1 ]]; 
    results := [];
    maxzero := 0;
    for s in scalars do 
        bas := BuildBasisOmega( G, basH, basK, basT : wH := wH, 
                                              type := type,
                                              typeh := typeh,
                                              typek := typek,
                                 scalars := [s[1], s[2], s[3], s[4]], ww := ww );
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