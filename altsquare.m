/* 
    altsquare.m                                                                   RecogniseSmallDim

    This file contains the main functions for the recognition of alternating square representations
    for the classical groups except for Sp(n,q).

    Written by Csaba Schneider.
    Analysed in January, 2024
*/

import "smalldimreps.m":SolveAltSquareDimEq, funcpos_altsquare, 
  __funcSLdqToAltSquare, __funcAltSquareToSLdq;
  
import "auxfunctions.m": MyDerivedGroupMonteCarlo, IsSimilarModMinus1List, 
  IsSimilarModScalarList, InvolutionWithProperty, RandomElementWithProperty, IsSimilarModScalarMat, SplitTensor;

import "altsquare_sp.m": RecogniseAltSquareSpFunc;

import "definitions.m":altsymsquareinforf, IsNewCodeApplicable;


// 2-dimensional recognition

RecogniseAltSquareDim2 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 2";
    F := CoefficientRing( G );
    
    if Dimension( G ) ne 1 and ( Generators( G )  ne { One( G )} 
               or Generators( G ) ne {} ) then
        return false;
    end if;
    
    return true, _, pmap< GL( 2, F ) -> GL( 1, F ) |
           x:->[ Determinant( x )]>, Basis( VectorSpace( F, 2 ));
end function;
    
// three dimensional recognition    

RecogniseAltSquareDim3 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 3";
    q := #CoefficientRing( G );
      
    a := map< GL(3,q) -> GL(3,q) | x :-> __funcSLdqToAltSquare( x )>;
    b := map< GL(3,q) -> GL(3,q) | x :-> __funcAltSquareToSLdq( x )>; 
        
    return true, a, b, One( GL( 3, q ));
end function;
    
// 4-dimensional recognition    
    
RecogniseAltSquareDim4 := function( G : type := "SL" )
    
    vprint SymSquareVerbose: "# Recog AltSquare dim 4";
    cputm := Cputime();
    
    /* G preserves an orthogonal form. First find the matrix that 
       transforms G to canonical form with respect to this form. */
      
    q := #CoefficientRing( G );
    mat := GL( 6, q )!TransformForm( G );
    mat := mat*GL(6,q)!DiagonalMatrix( GF( q ), [1,-1,1,1,1,1] );
        
    // construct the function SL(4,q) -> G 
      
    a := map< GL( 4, q ) -> GL( 6, q ) | 
         x :-> (SL(6,q)!__funcSLdqToAltSquare( x )^(mat^-1)) >;
    
    // construct the function G -> SL( 4, q )
    
    b := pmap< GL( 6, q ) -> GL( 4, q ) | 
         x :-> __funcAltSquareToSLdq( x^mat ) >;

    vprint SymSquareVerbose: "# Recog AltSquare dim 4 took", Cputime()-cputm;
    
    return true, a, b, mat^-1;
end function;    


 /* find an involution with sufficiently large minus one eigenspace and 
       its centraliser. */

InvolutionWithCentralizer := function( G, type, dimG, dim )
    
    // the eigenspace dimensions are set using heuristics
    // eiglim1: lower limit; eiglim2: upper limit for eigenspaces
    if type eq "Omega-" and dim eq 12 then 
        eiglim1 := 36; eiglim2 := 36;
    elif type eq "Omega" and dim eq 9 then 
        eiglim1 := 18; eiglim2 := 18;
    else 
        eiglim1 := case< dim | 6: 8, 11: 29, 12: 35, default: (2/9)*dim^2 >; 
        eiglim2 := case< dim | 6: 8, default: (1/4)*dim^2 >; 
    end if;
      
    // set up property function for InvolutionWithProperty  
    propfunc := function( x )
        dmin := Dimension( Eigenspace( x, -1 ));  
        return dmin ge eiglim1 and dmin le eiglim2;
    end function;
        
    // completion checking function    
    NrGensCentInv := 10; 
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    
    // we want to take the perfect subgroup inside the centralizer of the 
    // involution. This variable shows how deep we need to go inside the 
    // derived series.
    dl := case< dim | 8: 2, 9: 2, 10: 2, 11: 2, 12: 2, 18: 2, default : 1 >;

    // this function returns true if the condition we want for the dimensions of the 
    // CD-components is true
    good_dims := func< dims | #dims eq 3 and not 1 in dims and &+dims eq dimG >;
    type_is_omega := type in { "Omega+", "Omega-", "Omega", "Omega*" };

    repeat
        // get an involution with the right eigenspace dimensions   
        inv := InvolutionWithProperty( G, propfunc ); 
        // set up lists for the generators of the centralizer and its derived subgroup
        gensC := []; gensCD := [];
        
        // we need to find its centralizer. The centralizer of involution function may not 
        // return the full centralizer, and this is why we need to repeat.
        // TODO: Is it simpler to chose another involution when Cent is too small?
        
       repeat 
            // find the centralizer of inv and its derived subgroup
            C := CentraliserOfInvolution( G, inv : CompletionCheck := __compcheck );   
            CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv,
                      DerivedLength := dl );      

            // add the computed generators to the ones that were computed
            gensC := gensC cat GeneratorsSequence( C );
            gensCD := gensCD cat GeneratorsSequence( CD );
            // update C and CD
            C := sub< Universe( gensC ) | gensC >;
            CD := sub< Universe( gensCD ) | gensCD >;

            // compute the CD-module and its minimal submodules
            M := GModule( CD );
            mins := [ x : x in MinimalSubmodules( M : Limit := 4 )];
            // If M contains a unique submodule of dimension 1, then it is hopless and we get another 
            // involution
            dim_mins := [ Dimension( x ) : x in mins ]; 
            nr_ones := #[ x : x in [1..#mins] | dim_mins[x] eq 1 ];
            // if M has more than 4 minimal submodules, then we need more generators
            // and so we repeat the centralizer computation
            stop_condition := #mins lt 4 or nr_ones eq 1;
            //print dim_mins;
        until stop_condition;  
    // the right centralizer should have 3 minimal submodules that form a direct sum            
    until  good_dims( dim_mins );

    return inv, gensCD, CD, M, mins;
end function;
    
// a part of the basis calculated in the main function might need to be multiplied by a scalar
// this is done in this function 
find_scalar_for_mT := procedure( G, ~tr, dim, dH, q )

    p12 := funcpos_altsquare( dim, 1, 2 );
    p13 := funcpos_altsquare( dim, 1, dH+1 );
    p23 := funcpos_altsquare( dim, 2, dH+1 );
    p14 := funcpos_altsquare( dim, 1, dH+2 );
    p34 := funcpos_altsquare( dim, dH+1, dH+2 );

    repeat
        x := tr*Random( G )*tr^-1;
        mat1 := Matrix( GF( q ), 3, 3, [
                        x[p12,p12],    x[p12,p13],    x[p12,p23],
                        x[p13,p12],    x[p13,p13],    x[p13,p23],        
                        x[p23,p12],    x[p23,p13],    x[p23,p23]] );
        
        mat2 := Matrix( GF( q ), 3, 3, [
                        x[p13,p13],    x[p13,p14],    x[p13,p34],
                        x[p14,p13],    x[p14,p14],    x[p14,p34],        
                        x[p34,p13],    x[p34,p14],    x[p34,p34]] );
        
        if Determinant( mat1 ) eq 0 or Determinant( mat2 ) eq 0 then 
            mm1 := ZeroMatrix( GF( q ), 3 );
            mm1 := ZeroMatrix( GF( q ), 3 );
        else
            mm1 := __funcAltSquareToSLdq( mat1 ); 
            mm2 := __funcAltSquareToSLdq( mat2 );
        end if;
                        
    until mm1[1,1] ne 0 and mm1[1,3] ne 0;

    assert mm1[1,1] eq mm2[1,1];
    
    lambdasq := mm1[1,3]/mm2[1,2]; 
    is_sq, lambda := IsSquare( lambdasq );
    
    if is_sq then 
      for i in [1..dH], j in [dH+1..dim] do
            pij := funcpos_altsquare( dim, i, j ); tr[pij] := lambda*tr[pij];
       end for; 
    else 
      z0 := PrimitiveElement( GF( q ));
      lambda := Sqrt( z0*lambdasq );
      for i in [1..dH], j in [dH+1..dim] do
            pij := funcpos_altsquare( dim, i, j ); tr[pij] := lambda*tr[pij];
      end for;
    
      for i in [dH+1..dim], j in [i+1..dim] do
            pij := funcpos_altsquare( dim, i, j );
            tr[pij] := z0*tr[pij];
      end for;
    end if; 
end procedure;
   

/* The following function performs AltSquare recognition. */
forward RecogniseAltSquareFunc;
RecogniseAltSquareFunc := function( G :  Method := "Recursive",
                                         type := "SL" )

    // extract data
    cputm := Cputime(); 
    q := #CoefficientRing( G ); 
    _, p := IsPrimePower( q );
    dimg := Dimension( G );
    
    // the natural dimension of G
    dim := SolveAltSquareDimEq( dimg : type := type ); 
    vprint SymSquareVerbose: "# Recog AltSquare dim", dim, 
            "type", type, "method", Method ;

    // Sp groups are handled by another function
    if type eq "Sp" then
      return RecogniseAltSquareSpFunc( G : Method := Method );
    end if;
                                                                       
    // in small dimension, call other functions
    case dim: 
      when 2: return RecogniseAltSquareDim2( G );
      when 3: return RecogniseAltSquareDim3( G );
      when 4: return RecogniseAltSquareDim4( G );
    end case;
    
    // get a balanced involution inv, the derived subgroup of its centralizer CD, 
    // the CD-module M, and its minimal submodules.
    inv, gensCD, CD, M, mins := InvolutionWithCentralizer( G, type, dimg, dim );
      
    vprint SymSquareVerbose: "#   Cent comput dim", dim, "took ", 
      Cputime()-cputm, #gensCD, "gens used.";
      
      /* The CD-module V splits into three components.
         Two components are isomorphic to alt square U and alt square W, 
         respectively. The third is isomorphic to U tensor W.  
         The two alt squares lie in one of the eigenspaces of inv. The tensor 
         lies in the other eigenspace. */
     
    mplus := [ mins[x] : x in [1..3] | 
               (M!mins[x].1)^inv eq M!mins[x].1 ];
    mminus := [ mins[x] : x in [1..3] | 
                (M!mins[x].1)^inv eq -M!mins[x].1 ];
    
    // extract the submodules
    // mH, mK: U wedge U and W wedge W; mT: U tensor W.       
    if #mplus eq 2 then
        mH := mplus[1]; mK := mplus[2]; mT := mminus[1];
    else 
        mH := mminus[1]; mK := mminus[2]; mT := mplus[1];
    end if;      
        
    // calculate the dimensions
    dimH := Dimension( mH ); dimK := Dimension( mK ); dimT := Dimension( mT );
    dH := SolveAltSquareDimEq( dimH ); dK := SolveAltSquareDimEq( dimK ); 
    dT := dH*dK; assert Dimension( mT ) eq dT;

    // set up the projections into the components. In theory, this could be done by the following line,
    // but this does not work for some reason. 
    // Perhaps, it checks membership in CD?
    // ah := SubmoduleAction( CD, mH ); ak := SubmoduleAction( CD, mK ); at := SubmoduleAction( CD, mT );

    ah := pmap< GL( dimg, q ) -> MatrixAlgebra( GF( q ), dimH ) | 
          x :-> GL( dimH, q )![ Eltseq( mH!((M!b)^x )) : b in Basis( mH )]>;
    
    ak := pmap< GL( dimg, q ) -> MatrixAlgebra( GF( q ), dimK ) | 
          x :-> GL( dimK, q )![ Eltseq( mK!((M!b)^x )) : b in Basis( mK )]>;
    
    at := pmap< GL( dimg, q ) -> MatrixAlgebra( GF( q ), dimT ) | 
          x :-> GL( dimT, q )![ Eltseq( mT!((M!b)^x )) : b in Basis( mT )]>;
        

    // this function controls what we want of a generator of CD. We want that its projections to the 
    // irreducible components of GModule( CD ) should not be similar to a scalar multiple. 
    //
    // TODO: Check if all these conditions are necessary

    if type eq "Omega" and dim eq 9 then 
        is_suitable_generator := func< x | 
            not IsSimilarModScalarMat( x@ah, x@ah : can_be_one := false ) and 
            not IsSimilarModScalarMat( x@ak, x@ak : can_be_one := false )  
            >;
    else 
        is_suitable_generator := func< x | //not IsSimilar( x@at, -x@at ) and 
        not IsSimilarModScalarMat( x@ah, x@ah : can_be_one := false ) and 
        not IsSimilarModScalarMat( x@ak, x@ak : can_be_one := false )  >;
        //is_suitable_generator := func< x | MinimalPolynomial( x@at ) ne MinimalPolynomial( -x@at ) >;
    end if;
    
    // TODO: This is time consuming if is_suitable_generator is complicated. 
    // Find out what is necessary
    for i in [1..#gensCD] do
        if not is_suitable_generator( gensCD[i] ) then 
            gensCD[i] := RandomElementWithProperty( CD, is_suitable_generator );
        end if;
    end for; 

    // update CD        
    CD:= sub< Universe( gensCD ) | gensCD >;
    
    // determine the types of the components H and K
    if type in { "Omega", "Omega+", "Omega-" } then
        // Omega* means "generic omega". It can be Omega+ or Omega-, it does not matter.
        typeh := "Omega*"; typek := "Omega*";
    else
        // otherwise the type is just the same as the original type
        typeh := type; typek := type;
    end if;

    vprint SymSquareVerbose: "# components are: ", typeh, dH, " and ", typek, dK;

    // if we can, then we use the user defined method. Otherwise we switch to Tensor
    if not IsNewCodeApplicable( "Alt", typeh, dH, q ) or not IsNewCodeApplicable( "Alt", typek, dK, q ) then 
        Method := "Tensor";
        vprint SymSquareVerbose: "# Method switched to Tensor.";
    end if;

   if Method eq "Tensor" then 

       // TENSOR SPECIFIC CODE START HERE

       /* Construct the image of CD in the tensor product component. It must be 
          isomorphic to the tensor product of the preimages of the 
          groups induced on the alt square components */
      
       genst := [ x@at : x in gensCD ];
       aT := sub< GL( dimT, q ) | genst >;

       /* find the tensor decomposition of aT. */
       v := IsTensor( aT ); assert v; 
       //get the dimensions of the tensor factors
       dt1 := Dimension( TensorFactors( aT )[1] ); 
       dt2 := Dimension( TensorFactors( aT )[2] );
       
       /* the dimensions dt1 and dt2 of the tensor factors must be equal to 
          dH and dK in this order. If not, we must swap H and K. */

       dt1 := Dimension( TensorFactors( aT )[1] ); 
       dt2 := Dimension( TensorFactors( aT )[2] );                           
       if dt1 ne dH then 
           temp := dH; dH := dK; dK := temp;
           temp := dimH; dimH := dimK; dimK := temp;
           temp := ah; ah := ak; ak := temp;
           temp := mH; mH := mK; mK := temp;
       end if;
    
       // calculate the basis for aT that reflects the tensor structure
       tbas := TensorBasis( aT )^-1;

       // set of the maps from aT into the tensor components
       ch := pmap< GL( dimg, q ) -> GL( dH, q ) | x :-> SplitTensor( tbas*x@at*tbas^-1, dH, dK )[1] >;
       ck := pmap< GL( dimg, q ) -> GL( dK, q ) | x :-> SplitTensor( tbas*x@at*tbas^-1, dH, dK )[2] >;
       
       // calculate the two sets of generators that correspond to the projection to the component H.
       // First we calculate the projection to the first tensor component and then apply the AltSquare 
       // function 
       gens1h := [ GL(dimH,q)!__funcSLdqToAltSquare( x@ch ) : x in gensCD ];
       // then we calculate the projection with the ah function
       gens2h := [ x@ah : x in gensCD ]; 

       // we do the same for the K-component
       gens1k := [ GL(dimK,q)!__funcSLdqToAltSquare( x@ck ) : x in gensCD ];
       gens2k := [ x@ak : x in gensCD ];
       
       // the generators gens1h and gens2h should be similar module scalar
       // if they are not, then dim H eq dim K and the order of H and K was set up incorrectly
       vh, scalarsh := IsSimilarModScalarList( gens1h, gens2h );
       
       if vh then
           // gens1k and gens2k should be similar mod scalar
           vk, scalarsk := IsSimilarModScalarList( gens1k, gens2k ); assert vk;
           // modify gens2h and gens2k by the respective scalars
           gens2h := [ scalarsh[i]*gens2h[i] : i in [1..#gensCD] ];
           gens2k := [ scalarsk[i]*gens2k[i] : i in [1..#gensCD] ];                            
       else 
           // vh is false and so the order of H and K is wrong.
           vh, scalarsh := IsSimilarModScalarList( gens1h, gens2k ); 
           vk, scalarsk := IsSimilarModScalarList( gens1k, gens2h ); 
           assert vh and vk;
           // swap the data associated with H and K
           temp  := gens2h;
           gens2h := [ scalarsh[i]*gens2k[i] : i in [1..#gensCD] ];
           gens2k := [ scalarsk[i]*temp[i] : i in [1..#gensCD] ];
           temp := dimK; dimK := dimH; dimH := temp;
           temp := mK; mK := mH; mH := temp;       
       end if;
       
       // construct the two Modules associated with H
       M1H := GModule( sub< GL( dimH, q ) | gens1h >);
       M2H := GModule( sub< GL( dimH, q ) | gens2h >);
       
       // they should be isomorphic 
       v, trmh := IsIsomorphic( M1H, M2H ); 
       if not v then 
            gens1h_io := Open( "testgens1h", "w" );
            gens2h_io := Open( "testgens2h", "w" );
            WriteObject( gens1h_io, gens1h );
            WriteObject( gens2h_io, gens2h ); 
       end if; 
       assert v;
       
    
       // same with K
       M1K := GModule( sub< GL( dimK, q ) | gens1k >);
       M2K := GModule( sub< GL( dimK, q ) | gens2k >);    
       v, trmk := IsIsomorphic( M1K, M2K ); 
       if not v then 
            gens1k_io := Open( "testgens1k", "w" );
            gens2k_io := Open( "testgens2k", "w" );
            WriteObject( gens1k_io, gens1k );
            WriteObject( gens2k_io, gens2k ); 
        end if; 
       assert v;
           
       // transform the basis of mH, mK, and mT into the right form
       basH_mat := trmh*Matrix( Basis( mH )); 
       // extract basis elements from the new basis matrix
       basH := [ M!mH!basH_mat[x] : x in [1..dimH]];
       // the same for K and T
       basK_mat := trmk*Matrix( Basis( mK )); 
       basK := [ M!mK!basK_mat[x] : x in [1..dimK]];
       basT_mat := tbas*Matrix( Basis( mT )); 
       tbas := [ M!mT!basT_mat[x] : x in [1..dimT]];
        
       // TENSOR SPECIFIC CODE ENDS HERE
    end if;

    if Method eq "Recursive" then 

        // RECURSIVE CODE STARTS HERE

        // construct the groups acting on H and K
        aH := sub< GL( dimH, q ) | [ x@ah : x in gensCD ]>;
        aK := sub< GL( dimK, q ) | [ x@ak : x in gensCD ]>;

        // strip the groups from unecessary decorations
        aH := MyDerivedGroupMonteCarlo( aH : DerivedLength := case< dH | 4: 2, default: 1 > ); 
        aK := MyDerivedGroupMonteCarlo( aK : DerivedLength := case< dK | 4: 2, default: 1 >); 

        // run the recognition procedure 
        v1, b1, c1, bas1 := RecogniseAltSquareFunc( aH : type := typeh );
        v2, b2, c2, bas2 := RecogniseAltSquareFunc( aK : type := typek );
        assert v1 and v2;
    
        // bas1 is [e12,e13,...,e23,...,e{k-1}{k}]
        // bas2 is [e{k+1}{k+2},...,e{d-1}d]
        basH_mat := bas1*Matrix( Basis( mH )); basH := [ M!mH!basH_mat[x] : x in [1..dimH]];
        basK_mat := bas2*Matrix( Basis( mK )); basK := [ M!mK!basK_mat[x] : x in [1..dimK]];
        
        /* Construct the image of C in the tensor product component. It must be 
        isomorphic to the tensor product of the preimages of the 
        groups induced on the alt square components */
    
        genst := [ x@at : x in gensCD ];
        genstt := [ TensorProduct( x@ah@c1, x@ak@c2 ) : x in gensCD ];

        T := GModule( sub< GL( dimT, q ) | genst >);
        v, signs := IsSimilarModMinus1List( genst, genstt );      
        
        if v then 
            
            genstt := [ signs[i]*genstt[i] : i in [1..#genstt]];
            TT := GModule( sub< GL( dimT, q ) | genstt >);
            v, al := IsIsomorphic( T, TT ); assert v;

        else 
           
           /* aT might be isomorphic to aH tensor aK or (aH)^-t tensor aK or
           aH tensor (aK)^-t or (aH)^-t tensor (aK)^-t where ^-t is the inverse
           transpose isomorphism. We need to discover which one it is and 
           modify bas1 and bas2 accordingly. This can only happen if the dimension of H or K is 
           equal to 4. WHY???? */

            // set up the possible combinations of the inverse transpose and the identity
            // functions.
            inv_transp := func< x | Transpose( x )^-1 >; idfunc := func< x | x >;
            if dH eq 4 and dK ne 4 then funcs_comb := [ <inv_transp, idfunc,true,false> ]; 
            elif dH ne 4 and dK eq 4 then funcs_comb := [  <idfunc, inv_transp, false,true> ];
            elif dH eq 4 and dK eq 4 then funcs_comb := [ <inv_transp, idfunc,true,false>,  
                            <idfunc, inv_transp, false,true>, <inv_transp,inv_transp,true,true> ];
            else error( "non isomorphic modules, but dimension is not 4.");
            end if;  

            // try all combinations of the functions set up above
            for funcs in funcs_comb do     
                genstt := [ TensorProduct( funcs[1](x@ah@c1 ), funcs[2](x@ak@c2) ) : x in gensCD ];            
                v, signs := IsSimilarModMinus1List( genst, genstt );
                if v then
                    // Bingo!
                    changedH := funcs[3]; changedK := funcs[4]; // this remembers which basis needs change
                    break; 
                end if;
            end for; 

            // modify genstt and recompute some data
            genstt := [ signs[i]*genstt[i] : i in [1..#genstt]];
            TT := GModule( sub< GL( dimT, q ) | genstt >);
            v, al := IsIsomorphic( T, TT ); assert v;

            // change bases of H and K
            if changedH then 
                basH := [ basH[6], -basH[5], basH[4], basH[3], -basH[2], basH[1]]; 
                vprint SymSquareVerbose: "# TransInv in first comp.";       
            end if;

            if changedK then
                basK := [ basK[6], -basK[5], basK[4], basK[3], -basK[2], basK[1]];
                vprint SymSquareVerbose: "# TransInv in second comp.";  
            end if; 
        end if; 
        
        /* find the vectors eij with 1 <= j <= dH and dH+1 <= j <= dimg and 
           insert them into their place in bas. */
        tbas_mat := Matrix( Basis( mT ))*al^-1;
        tbas := [ M!mT!tbas_mat[x] : x in [1..dimT]];

        // RECURSIVE CODE ENDS HERE
    end if;

    /* we return to the common part of the code. 
       At this point, the basis for H, K, and T are computed. We need mount the right basis for V.

       we place the basis vectors computed in bas1 and bas2 into their place
       in the basis of V */

    bas := [ Zero( M ) : x in [1..dimg]];

    for i in [1..dH], j in [i+1..dH] do
        bas[funcpos_altsquare( dim, i, j )] := basH[funcpos_altsquare( dH, i, j )];
    end for;
    
    for i in [dH+1..dim], j in [i+1..dim] do
        bas[funcpos_altsquare(dim, i, j )] := basK[funcpos_altsquare( dK, i-dH, j-dH )];
    end for;
    
    for i in [1..dH], j in [dH+1..dim] do
        bas[funcpos_altsquare( dim, i, j )] := tbas[(i-1)*dK+j-dH];
    end for;

    // tr is the matrix of basis change.       
    tr := Matrix( bas );
    
    // some rows of the matrix tr need to be multiplied by a scalar.
    find_scalar_for_mT( G, ~tr, dim, dH, q );
    tr := GL( dimg, q )!tr;
    
    // construct the maps between GL(dim,q) and G

    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToAltSquare( x )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> GL( dim, q )!__funcAltSquareToSLdq( x^(tr^-1)) >;

    vprint SymSquareVerbose: "# Recog AltSquare dim", dim, "took ", 
      Cputime()-cputm;
      
    return true, a, b, tr;
end function;
                
intrinsic RecogniseAltSquare( G::GrpMat : 
            type := "SL", 
            CheckResult := false,
            Method := "Recursive" ) 
          -> BoolElt, Map, Map, GrpMatElt
                                                         
 {Checks if the input group G is isomorphic to a classical group of type <type> over a field of 
 odd characteristic in its exterior square representation. Returns true or false, a map from the 
 the standard copy of the classical group in Magma to G, a map from G to the classical group in Magma, 
 and two matrices X and Y such that the conjugate G^X is equal to the large composition factor of the 
 exterior square of Y*S*Y^-1 in the standard basis where S is the corresponding classical group in Magma. 
                           
 Use the optional argument "CheckResult := true" to check the final result.
                           
The basic algorithm is implemented in two variations. The first uses a recursive call for smaller 
dimensional exterior square recognition, while the second uses recognition of tensor decomposition 
with IsTensor. In small dimensions (how small depends on the type of the group), the version using 
tensor recognition is called, while if the dimension is high enough, then the recursive version is used.
This choice can be overwritten by setting <Method> to "Tensor".}    

    if assigned G`AltSymSquareInfo then 
        return true, G`AltSymSquareInfo`phi_map, G`AltSymSquareInfo`tau_map, G`AltSymSquareInfo`tr_matrix_outer;
    end if; 

    dimg := Dimension( G );
    dim := SolveAltSquareDimEq( dimg : type := type );        
    q := #CoefficientRing( G );
    _, p := IsPrimePower( q );
    q0 := case< type | "SU": Integers()!( Sqrt( q )), default: q >;        
    error if not IsNewCodeApplicable( "Alt", type, dim, q ), "This type of group is not implemented for altsquare recognition";

    v, _, _, tr := RecogniseAltSquareFunc( G : type := type, 
                              Method := Method );  
    assert v;

    /* The matrix tr will conjugate G into a subgroup of AltSquare( SL( dim, q )). If the original G 
       is the image of a classical group, we want to further conjugate it into the image of the 
       standard classical group in Magma, such as Sp(dim,q), SU(dim,q), etc. 

       This is achieved with the tr_form matrix. 

       First we check the classical form that is preserved by the preimage of G in SL(dim,q) and 
       we compute the matrix that transforms this form into the standard form of Magma. */

    if type in { "Omega+", "Omega-", "Omega" } then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcAltSquareToSLdq( x^(tr^-1) : type := type ) : 
                            x in GeneratorsSequence( G )] >)`bilinearForm;
        tr_form := TransformForm( form, case< type | 
                                            "Omega+": "orthogonalplus", 
                                            "Omega-": "orthogonalminus", 
                                            "Omega": "orthogonalcircle", 
                                            default: false  >);        
    elif type eq "SU" then 
        form := ClassicalForms( sub< GL( dim, q ) | 
                    [ __funcAltSquareToSLdq( x^(tr^-1)) : x in GeneratorsSequence( G )] >)`sesquilinearForm;
        tr_form := TransformForm( form, "unitary" );
    else 
        tr_form := One( GL( dim, q ));
    end if;

    /* Now we compute the image of tr_form_alt in the exterior square and modify the transformation matrix 
       tr */

    tr_form_alt := __funcSLdqToAltSquare( tr_form : type := type );
    tr := GL( dimg, q )!(tr_form_alt^-1*tr);
    

    a := map< GL( dim, q ) -> GL( dimg, q ) | 
         x :-> GL( dimg, q )!__funcSLdqToAltSquare( x : type := type )^tr >;
    
    b := pmap< GL( dimg, q ) -> GL( dim, q ) |
         x :-> (GL( dim, q )!__funcAltSquareToSLdq( x^(tr^-1) : type := type )) >;

    recog_rec := rec< altsymsquareinforf | 
                      Type := type, 
                      RepType := "AltSquare",
                      NatDim := dim, 
                      NatField := q0, 
                      phi_map := a, 
                      tau_map := b, 
                      tr_matrix_outer := tr, 
                      tr_matrix_inner := One( GL( dim, q )) >; 

    G`AltSymSquareInfo := recog_rec;

    // if CheckResult is set, we perform a check
    if CheckResult then
        vprint SymSquareVerbose: "# Checking final result";
        try
          gens := [ x@b : x in GeneratorsSequence( G )];
        catch e
          error( "could not compute preimages of generators" );
        end try;
        M1 := GModule( sub< GL( dimg, q ) | 
                     [ __funcSLdqToAltSquare( MatrixAlgebra( GF( q ), dim )!(x^(tr_form^-1)) : type := type ) 
                        : x in gens ]>);
        if not IsIsomorphic( M1, GModule( G )) then
            vprint SymSquareVerbose: "# Check failed.";
            return false, a, b, tr;
        end if;
        vprint SymSquareVerbose: "# Check passed.";
    end if;

    return true, a, b, tr^-1;
end intrinsic;

