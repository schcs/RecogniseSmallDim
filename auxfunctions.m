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
    

