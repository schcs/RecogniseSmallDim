TestBasis := function( basH, basK, basT, wH, wK, g )
    
    scalars := [ <1,b,1,d > : b in [1,-1], 
                   //c in F, 
                   d in [1,-1] ]; 
    results := [];
    maxzero := 0;
    
    
    for s in scalars do
        bas := BuildBasis( basH, basK, basT, wH :
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
    
TestBasis2 := function( basH, basK, basT, basOneDim )
    
    q  := #Field( Parent( basH[1] ));
    g0 := Sp( 8, q );
    g := sub< SL( 27, q ) | __funcSLdqToAltSquare( g0.1 : type := "Sp" ), 
         __funcSLdqToAltSquare( g0.2 : type := "Sp" ) >;

          
    repeat 
        bas := BuildBasis( basH, basK, basT, basOneDim :
                       scalars := [1, 4, 2, 4, 2] );
        try
          x := bas*Random( g )*bas^-1; 
          y := __funcAltSquareToSLdq( x : type := "Sp" ); 
          x1 := __funcSLdqToAltSquare( y : type := "Sp" ); 
          els := Eltseq( x-x1 );
          poszero := #[ els[x] : x in [1..#els] | els[x] eq 0 ];
          print poszero;
          stopcond := poszero gt 650;
          catch e
            stopcond := false;
      end try;
  until stopcond;
  
  
  return 0;
end function;