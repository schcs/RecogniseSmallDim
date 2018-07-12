/* The following function performs AltSquare recognition by recognising
   the tensor component and recovering the smaller alt square components 
   directly from the tensor factor. It does not use recursive call and it
   may perform better for certain inputs. 

   This version is the implementation of non-SL classical group */
  
      
RecogniseAltSquareWithTensorDecomposition := function( G : 
                                         type := "SL", CheckResult := true )
    cputm := Cputime(); 
    
    q := #CoefficientRing( G ); 
    dimg := Dimension( G );
    
    // the natural dimension of G
    dim := SolveAltSquareDimEq( dimg : type := type ); 
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim;
    
    /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */
      
    eiglim1 := case< dim | 6: 8, default: (2/9)*dim^2 >; 
    // lower limit for eigenspace dim
    eiglim2 := case< dim | 6: 8, default: (1/4)*dim^2 >; 
    // upper limit for eigenspace dim
      
    // set up property function for InvolutionWithProperty  
    propfunc := function( x )
        dmin := Dimension( Eigenspace( x, -1 )); 
        return dmin ge eiglim1 and dmin le eiglim2;
    end function;
        
    // completion checking function
    
    NrGensCentInv := 10; 
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    gensC := []; gensCD := [];
    
    // the number of components in the irred decomp for the centralizer
    no_mins := case< type | "SL": 3, "Sp": 4, default: 3 >;
    
    repeat   

        if not assigned inv then 
            inv := InvolutionWithProperty( G, propfunc );
        end if;
        C := CentraliserOfInvolution( G, inv : 
                     CompletionCheck := __compcheck );  
        CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv,
                      DerivedLength := case< dim | 
                      8: 2, 9: 2, 10: 2, 11: 2, 12: 2, 18: 2, 
                      default : 1 >);     
        gensC := gensC cat GeneratorsSequence( C );
        gensCD := gensCD cat GeneratorsSequence( CD );
        C := sub< Universe( gensC ) | gensC >;
        CD := sub< Universe( gensCD ) | gensCD >;
        
        M := GModule( CD );
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )];
        
        if #mins eq 2 then 
            delete inv; 
            gensC := [];
            gensCD := [];
        end if;
    until  #mins eq no_mins and &+[ Dimension( x ) : x in mins ] eq dimg;

    vprint SymSquareVerbose: "#   Cent comput dim", dim, "took ", 
      Cputime()-cputm, #gensC, "gens used.";
      
      /* The C-module V splits into three components.
         Two components are isomorphic to alt square U and alt square W, 
         respectively. The third is isomorphic to U tensor W.  
         The two alt squares lie in one of the eigenspaces of inv. The tensor 
         lies in the other eigenspace. */
    mplus := [ mins[x] : x in [1..no_mins] | 
               (M!mins[x].1)^inv eq M!mins[x].1 and 
               Dimension( mins[x] ) ge 2 ];
    mminus := [ mins[x] : x in [1..no_mins] | 
                (M!mins[x].1)^inv eq -M!mins[x].1 and 
                Dimension( mins[x] ) ge 2 ];
    
    // in the case of Sp, etc, there is a one-dimensional component
    monedims := [ mins[x] : x in [1..no_mins] | Dimension( mins[x] ) eq 1 ];
    if #monedims ne 0 then
      monedim := monedims[1];
    end if;
      
    if #mplus eq 2 then
        mH := mplus[1]; mK := mplus[2]; mT := mminus[1];
        // if there is a 1-dim component, it has to be adjoined to H and K
        if assigned monedim then
            mH := mH+monedim;
            mK := mK+monedim;
        end if;
    else 
        mH := mminus[1]; mK := mminus[2]; mT := mplus[1];
        // if there is a 1-dim component, it has to be adjoined to H and K
        if assigned monedim then
            mH := mH+monedim;
            mK := mK+monedim;
        end if;
    end if;      
        
    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );
    dH := SolveAltSquareDimEq( dimH ); 
    dK := SolveAltSquareDimEq( dimK ); 
    dT := dH*dK;
    assert Dimension( mT ) eq dT;
    
    // set up the projections into the components
    
    ah := pmap< GL( dimg, q ) -> GL( dimH, q ) | 
          x :-> GL( dimH, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    ak := pmap< GL( dimg, q ) -> GL( dimK, q ) | 
          x :-> GL( dimK, q )![ Eltseq( mK!((M!b)^x )) : b in Basis( mK )]>;
    
    at := pmap< GL( dimg, q ) -> GL( dimT, q ) | 
          x :-> GL( dimT, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;
    
    /* For some technical reason (see (###) later), the projection of a 
       generator of C cannot be similar to its negative and we want that
       the projection by ah and ak should fall into SL.     
       If some generator fails to satisfy this, it is thrown away and is 
       replaced by another one. */  

    mnsh := GL( dimH, q )!ScalarMatrix( GF( q ), dimH, -1 );
    mnsk := GL( dimK, q )!ScalarMatrix( GF( q ), dimK, -1 );
        
    // TODO: check if this is needed in this version. I suspect not.    
        
    for i in [1..#gensCD] do
        if Determinant( gensCD[i]@ah ) ne 1 or 
              Determinant( gensCD[i]@ak ) ne 1 or 
              IsSimilarToScalarMultiple( gensCD[i]@ah ) or
              IsSimilarToScalarMultiple( gensCD[i]@ak ) then
           repeat
               x := Random( CD );
           until Determinant( x@ah ) eq 1 and
                Determinant( x@ak ) eq 1 and not 
                IsSimilarToScalarMultiple( x@ah ) and not
                IsSimilarToScalarMultiple( x@ak );
           gensCD[i] := x;
       end if;
   end for; 
   
   CD:= sub< Universe( gensCD ) | gensCD >;

   /* Construct the image of CD in the tensor product component. It must be 
      isomorphic to the tensor product of the preimages of the 
      groups induced on the alt square components */
      
    genst := [ x@at : x in gensCD ];
    aT := sub< Universe( genst ) | genst >;
    
    v := IsTensor( aT ); assert v; 
    
    // get the dimensions of the tensor factors
    dt1 := Dimension( TensorFactors( aT )[1] ); 
    dt2 := Dimension( TensorFactors( aT )[2] );
    
    /* the dimensions dt1 and dt2 of the tensor factors must be equal to 
       dH and dK in this order. If not, we must swap H and K. */
                                  
    if dt1 ne dH then 
        temp := dH; dH := dK; dK := temp;
        temp := dimH; dimH := dimK; dimK := temp;
        temp := ah; ah := ak; ak := temp;
        temp := mH; mH := mK; mK := temp;
    end if;
    
    // calculate the basis for aT that reflects the tensor structure
    
    tbas := TensorBasis( aT )^-1;
    
    // set of the maps from aT into the tensor components
    
    ch := pmap< GL( dimg, q ) -> GL( dH, q ) | x :-> SplitTensor( 
                  tbas*x@at*tbas^-1, dK, dH )[2] >;
    
    ck := pmap< GL( dimg, q ) -> GL( dK, q ) | x :-> SplitTensor( 
                  tbas*x@at*tbas^-1, dK, dH )[1] >;
    
    gens1h := [ GL(dimH,q)!__funcSLdqToAltSquare( x@ch ) : x in gensCD ];
    gens2h := [ x@ah : x in gensCD ];

    gens1k := [ GL(dimK,q)!__funcSLdqToAltSquare( x@ck ) : x in gensCD ];
    gens2k := [ x@ak : x in gensCD ];
    
    vh, scalarsh := IsSimilarModScalar( gens1h, gens2h ); 
    
    if vh then
        vk, scalarsk := IsSimilarModScalar( gens1k, gens2k );
        gens2h := [ ScalarMatrix( GF(q), dimH, scalarsh[i] )*
                    gens2h[i] : 
                      i in [1..#gensCD] ];
        gens2k := [ ScalarMatrix( GF(q), dimK, scalarsk[i] )*gens2k[i] : 
                      i in [1..#gensCD] ];                            
    else 
        vh, scalarsh := IsSimilarModScalar( gens1h, gens2k ); 
        vk, scalarsk := IsSimilarModScalar( gens1k, gens2h ); 
        assert vh and vk;
        temp  := gens2h;
        gens2h := [ ScalarMatrix( GF(q), dimK, scalarsh[i] )*gens2k[i] : 
                      i in [1..#gensCD] ];
        gens2k := [ ScalarMatrix( GF(q), dimH, scalarsk[i] )*temp[i] : 
                    i in [1..#gensCD] ];
        temp := dimK; dimK := dimH; dimH := temp;
        temp := mK; mK := mH; mH := temp;       
    end if;
    
    assert vh and vk;
    
    M1H := GModule( sub< GL( dimH, q ) | gens1h >);
    M2H := GModule( sub< GL( dimH, q ) | gens2h >);
    
    v, trmh := IsIsomorphic( M1H, M2H ); assert v;
    
    M1K := GModule( sub< GL( dimK, q ) | gens1k >);
    M2K := GModule( sub< GL( dimK, q ) | gens2k >);
    
    v, trmk := IsIsomorphic( M1K, M2K ); assert v;
         
    // bas1 is [e12,e13,...,e23,...,e{k-1}{k}]
    // bas2 is [e{k+1}{k+2},...,e{d-1}d]
      
    basH := [ M!(&+[trmh[j][i]*Basis( mH )[i] : 
                    i in [1..dimH]]) : j in [1..dimH]];
    
    basK := [ M!(&+[trmk[j][i]*Basis( mK )[i] : 
                    i in [1..dimK]]) : j in [1..dimK]];
            
    /* we place the basis vectors computed in bas1 and bas2 into their place
       in the basis of V */
      
    bas := [ Zero( M ) : x in [1..dimg]];
    
    for i in [1..dH] do
        for j in [i+1..dH] do
            bas[funcpos_altsquare( dim, i, j )] := 
              basH[funcpos_altsquare( dH, i, j )];
        end for;
    end for;
    
    for i in [dH+1..dim] do
        for j in [i+1..dim] do
            bas[funcpos_altsquare(dim, i, j )] := 
              basK[funcpos_altsquare( dK, i-dH, j-dH )];
        end for;
    end for;
    
    tbas := [ M!(&+[tbas[j][i]*Basis( mT )[i] : 
                     i in [1..dT]]) : j in [1..dT]];

    for i in [1..dH] do
        for j in [dH+1..dim] do
            bas[funcpos_altsquare( dim, i, j )] := tbas[(i-1)*dK+j-dH];
        end for;
    end for;
    
    tr := GL( dimg, q )![ Eltseq( x ) : x in bas ];
    
    p12 := funcpos_altsquare( dim, 1, 2 );
    p13 := funcpos_altsquare( dim, 1, dH+1 );
    p23 := funcpos_altsquare( dim, 2, dH+1 );
    p14 := funcpos_altsquare( dim, 1, dH+2 );
    p34 := funcpos_altsquare( dim, dH+1, dH+2 );
    
    repeat
        x := Random( G )^(tr^-1);
        mat1 := Matrix( GF( q ), 3, 3, [
                        x[p12,p12],    x[p12,p13],    x[p12,p23],
                        x[p13,p12],    x[p13,p13],    x[p13,p23],        
                        x[p23,p12],    x[p23,p13],    x[p23,p23]] );
        
        mat2 := Matrix( GF( q ), 3, 3, [
                        x[p13,p13],    x[p13,p14],    x[p13,p34],
                        x[p14,p13],    x[p14,p14],    x[p14,p34],        
                        x[p34,p13],    x[p34,p14],    x[p34,p34]] );
        
                
        mm1 := __funcSLdqToAltSquare( mat1 );
        mm2 := __funcSLdqToAltSquare( mat2 );
        
    until Determinant( mat1 ) ne 0 and Determinant( mat2 ) ne 0 and 
          mm1[1,3] ne 0 and mm1[1,1] ne 0 and mm2[1,2] ne 0 and mm2[1,1] ne 0;
    
    mm2 := mm1[1,1]*mm2[1,1]^-1*mm2;
    lambdasq := mm1[1,3]/mm2[1,2];
        
    try 
      lambda := Sqrt( lambdasq ); 
      for i in [1..dH] do
           for j in [dH+1..dim] do
               pij := funcpos_altsquare( dim, i, j );
               bas[pij] := lambda*bas[pij];
           end for;
       end for; 
    catch e  
      z0 := PrimitiveElement( GF( q ));
      lambda := Sqrt( z0*lambdasq ); 
      for i in [1..dH] do
          for j in [dH+1..dim] do
              pij := funcpos_altsquare( dim, i, j );
              // multiply eij by lambda
              bas[pij] := lambda*bas[pij];
          end for;
      end for;
    
      for i in [dH+1..dim] do
          for j in [i+1..dim] do
              pij := funcpos_altsquare( dim, i, j );
              // multiply eij by z0
              bas[pij] := z0*bas[pij];
          end for;
      end for;
    end try;
    
    tr := GL( dimg, q )![ Eltseq( x ) : x in bas ];
    
    // construct the maps between GL(dim,q) and G
    
    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToAltSquare( x )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> GL( dim, q )!__funcAltSquareToSLdq( x^(tr^-1)) >;
    
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim, "took ", 
      Cputime()-cputm;
    
    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        try
          gens := [ x@b : x in GeneratorsSequence( G )];
        catch e
          return false, a, b, tr, CD;
          error(1);
        end try;
        M1 := GModule( sub< GL( dimg, q ) | 
                     [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), dim )!x ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
            vprint SymSquareVerbose: "# Check failed.";
            return false, a, b, tr, CD;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;
        
    return true, a, b, tr;
end function;

