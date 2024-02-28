/* 
    auxfunctions.m                                                          RecogniseSmallDim

    This file contains some auxiliary functions for the RecogniseSmallDim package.
    Written by Csaba Schneider.
    Analysed in December, 2023
*/


// a variation to RandomElementOfOrder. This function seems to be faster than RandomElementOfOrder.
  
RandomInvolution := function( G )
    
    // we could use this line, but it seems slower
    //_, inv := RandomElementOfOrder( G, 2 ); return inv;
    
    repeat
        x := Random( G : Short := true );
        o := Order( x );
    until IsEven( o );
    
    return x^(o div 2);
end function;
      
// select an involution with certain properties
  
InvolutionWithProperty := function( G, prop )
    
    repeat
        x := RandomInvolution( G );
    until prop( x );
    
    return x;
end function;
          
RandomElementWithProperty := function( G, prop )
    
    repeat 
        x := Random( G );
    until prop( x );
    
    return x;
end function;

/* a simple function to return the likely derived subgroup 
   by considering a number (default: 20) random commutators. */
                               
MyDerivedGroupMonteCarlo := function( G : NumberGenerators := 20,
				          DerivedLength := 1 );

    if DerivedLength eq 0 then return G; end if; 

    // produces NumberOfGenerators elements of the form [x,y] or [[x,y],[u,v]]
    gens := { case< DerivedLength |
	                2: ((Random(G),Random(G)),(Random(G),Random(G))),
                    default: (Random(G),Random(G))> : 
            x in [1..NumberGenerators] };

    return sub< Universe( gens ) | gens >;
end function;

// a function to decide if two matrices are similar modulo -1 scalar

IsSimilarModMinus1 := function( m1, m2 )
    
    if IsSimilar( m1, m2 ) then 
        return true, 1;
    elif IsSimilar( m1, -m2 ) then 
        return true, -1;
    else
        return false, _;
    end if;
        
end function;
    
// an extension of the previous function to lists of matrices    
    
IsSimilarModMinus1List := function( l1, l2 )
    
    assert #l1 eq #l2;
    
    signs := [ 0 : _ in [1..#l1]];  
      
    for i -> m in l1 do
        v, s := IsSimilarModMinus1( m, l2[i] );
        if not v then return false, _; end if;
        signs[i] := s;
    end for;
    
    return true, signs;
end function;
    
// checks if two matrices are similar mod scalar
// often used with mat1 eq mat2. 
// we often want to ignore scalar = 1. In this case can_be_one is set to false
  
IsSimilarModScalarMat := function( mat1, mat2 : can_be_one := true )
    
    F := CoefficientRing( mat1 );
    n := NumberOfRows( mat1 );
    
    // the scalar can only be an n-th root of 1
    sc := AllRoots( F!1, n );
    
    // if can_be_ne eq false, then we don't want scalar = 1.
    // so this scalar is removed 
    if not can_be_one then sc := Remove( sc, 1 ); end if; 
    
    id_mat := IdentityMatrix( F, n );
    
    for s in sc do
        if IsSimilar( mat1, (s*id_mat)*mat2 ) then 
            return true, s;
        end if;
    end for;
    
    return false, _;
end function;

// checks if the matrices in two lists are similar to each other, one by one, modulo scalar

IsSimilarModScalarList := function( list1, list2 )
    
    assert #list1 eq #list2;

    // this will be the list of scalars
    scalars := [ CoefficientRing( list1[1] )!0 : _ in [1..#list1]];
        
    for i -> m in list1 do
        v, s := IsSimilarModScalarMat( m, list2[i] );
        if not v then return false, _; end if;
        scalars[i] := s;
    end for;
    
    return true, scalars;
end function;
    
// split mn x mn matrix into m x m and n x n tensor components
// the basis is assumed to be x11,...,x1n,x21,...,x2n,...,xm1,...,xmn      
// It is assumed that X has determinant one and the output matrices will also have 
// determinant 1.
SplitTensor := function( X, n, m  : SwapFactors := false )
    
    if SwapFactors then 
        temp := n; n := m; m := temp;
    end if;

    d := n*m;
    F := CoefficientRing( X );  
    // find nonzero entry in first row of X
    // this will be used to get out a block
    _ := exists(pos){ pos : pos in [1..d] | X[1,pos] ne 0 };
    bm := (pos-1) div m;
    
    b := Matrix( F, m, m, [ X[i,bm*m+j] : i, j in [1..m]] );
    pos := pos mod m; if pos eq 0 then pos := m; end if;
    c := b[1,pos];
    a := Matrix( F, n, n, [ X[i*m+1,j*m+pos]/c : i, j in [0..n-1]] );
    
    // make the determinant one
    v := exists( r ){ x : x in AllRoots( Determinant( b )^-1, m ) | 
                 x^n eq Determinant( a ) };
    assert v;
    b := r*b; a := r^-1*a;
        
    //assert TensorProduct( a, b ) eq X and Determinant( a ) eq 1 and Determinant( b ) eq 1;
    return < a, b >;
end function;

// The following is necessary because of a change that occurred around V2.25 with 
// changing the standard form preserved by OMinus( d, F )
// returns the Gram matrix of standard the Omega- form that was used before V2.25 
// TO DO: Phase it out
OldFormOmegaMinus := function( d, q )

    F := GF( q );

    oldform := ZeroMatrix( F, d );
    for i in [1..(d-2) div 2] do
        oldform[i,d+1-i] := 1;
        oldform[d+1-i,i] := 1;
    end for;

    oldform[d div 2,d div 2] := 1;
    oldform[d div 2+1,d div 2+1] := -Nonsquare( F );

    return oldform;
end function;    


// Does the same as TransformForm, but transforms into old Omega- form

TransformToForm := function( G )

    tr := TransformForm( G );
    if FormType( G ) ne "orthogonalminus" then 
        return tr;
    end if;

    d := Dimension( G );
    F := CoefficientRing( G );

    return tr*TransformForm( OldFormOmegaMinus( d, #F ), "orthogonalminus" )^-1;
end function;


// mat preserves the form mod scalar
// returns this scalar

ScalarOfPreservedForm := function( mat, form )

    i := 1;
    while form[1,i] eq 0 do 
        i +:= 1;
    end while; 

    // form[1,i] is non-zero

    form1 := mat*form*Transpose( mat );
    return form1[1,i]*form[1,i]^-1;
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
    elif type eq "Sp" and dim eq 6 then 
        eiglim1 := 9; eiglim2 := 9;
    elif type eq "Sp" and dim eq 14 then 
        eiglim1 := 40; eiglim2 := 49;
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
    
    
    if type eq "Sp" then 
        // we want to take the perfect subgroup inside the centralizer of the 
        // involution. This variable shows how deep we need to go inside the 
        // derived series.
        dl := 3;
        // the number of components in the C0-module
        nocomponents := case< dim mod Characteristic( CoefficientRing( G )) eq 0 | true: 3, default: 4 >;
        // this function returns true if the condition we want for the dimensions of the 
        // CD-components is true
        good_dims := func< dims | #dims eq nocomponents and &+dims eq dimG >;
    else 
        // the same when the type is not Sp
        dl := case< dim | 8: 2, 9: 2, 10: 2, 11: 2, 12: 2, 18: 2, default : 1 >;
        nocomponents := 3;
        good_dims := func< dims | #dims eq nocomponents and not 1 in dims and &+dims eq dimG >;
    end if; 

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
/*
InvolutionWithCentralizerAltSp := function( G, type, dimG, dim )
    
    c1 := 2/9; c2 := 1/4;

    eiglim1 := case< dim | 6: 9, 14: 40, default: c1*dim^2 >; 
    // lower limit for eigenspace dim
    eiglim2 := case< dim | 6: 9, default: c2*dim^2 >; 
    // upper limit for eigenspace dim

    // set up property function for InvolutionWithProperty  
    propfunc := function( x )
        dmin := Dimension( Eigenspace( x, -1 ));
        dplus := Dimension( Eigenspace( x, 1 ));

        //return dmin ge 6 and dplus ge 6;
        return dmin ge eiglim1 and dmin le eiglim2;
    end function;
        
    // completion checking function

    NrGensCentInv := 10; 
    __compcheck := func< G, C, g | NumberOfGenerators( C ) ge NrGensCentInv >;
    
    gensC := []; gensCD := [];
    
    //  the following block will find an involution with the right
    //  minus one eigenspace and sets up its centralizer       
      
    nocomponents := case< pdividesd | true: 3, default: 4 >;

    __dimcheck := function( dims )

        if #dims ne 3 then return true; end if;
        dims0 := [ SolveAltSquareDimEq( x : type := "Sp" ) : x in dims ];
        notz := [ i : i in [1..3] | dims0[i] ne 0 ];
        if #notz ne 2 then return false; end if;
        ind := [ x : x in [1..3] | not x in notz ][1];

        res := dims0[notz[1]]*dims0[notz[2]] eq dims[ind];

        if not res then print dims, "rejected!!!!!!!!!!!!!!!!!!!!"; end if;

        return res;
    end function; 

    repeat   
        if not assigned inv then 
            inv := InvolutionWithProperty( G, propfunc );
        end if; 
        C := CentraliserOfInvolution( G, inv : 
                     CompletionCheck := __compcheck );  
        CD := MyDerivedGroupMonteCarlo( C : 
                      NumberGenerators := NrGensCentInv,
                      DerivedLength := 3 );
        Append( ~gensCD, GeneratorsSequence( CD ));
        CD := sub< Universe( gensCD ) | gensCD >;
        
        M := GModule( CD );
        mins := [ x : x in MinimalSubmodules( M : Limit := 4 )];
            
        if #mins ne nocomponents or &+[ Dimension( x ) : x in mins ] lt dimg or 
           not __dimcheck([ Dimension( x ) : x in mins ]) then
            delete inv, C, CD;
            gensCD := [];
            mins := [];
            continue;
        end if;
    until  #mins eq nocomponents and &+[ Dimension( x ) : x in mins ] eq dimg;

*/