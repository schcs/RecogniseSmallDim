// verbose is declared
declare verbose SymSquareVerbose, 2;


// a variation to RandomElementOfOrder
  
RandomInvolution := function( G )
    
    //_, inv := RandomElementOfOrder( G, 2 ); return inv;
    
    repeat
        x := Random( G : Short := true );
        o := Order( x );
    until IsEven( o );
    
    return x^Round(o/2);
end function;
      
/* a simple function to return the likely derived subgroup 
   by considering a number (default: 10) random commutators. */
                               
MyDerivedGroupMonteCarlo := function( G : NumberGenerators := 20,
				          DerivedLength := 1 );

    if DerivedLength eq 0 then 
        return G;
    end if; 

    gens := { case< DerivedLength |
	                2: ((Random(G),Random(G)),(Random(G),Random(G))),
                    default: (Random(G),Random(G))> : 
            x in [1..NumberGenerators] };

    return sub< Universe( gens ) | gens >;
end function;

// a function to decide if two matrices are similar modulo -1 scalar

IsSimilarModMinus1 := function( m1, m2 )
    
    mns := ScalarMatrix( CoefficientRing( m1 ), NumberOfRows( m1 ), -1 );
    
    if IsSimilar( m1, m2 ) then 
        return true, 1;
    elif IsSimilar( m1, mns*m2 ) then 
        return true, -1;
    else
        return false, _;
    end if;
        
end function;
    
// an extension of the previous function to lists of matrices    
    
IsSimilarModMinus1List := function( l1, l2 )
    
    assert #l1 eq #l2;
      
    signs := [];  
      
    for i in [1..#l1] do
        v, s := IsSimilarModMinus1( l1[i], l2[i] );
        if not v then return false, _; end if;
        Append( ~signs, s );
    end for;
    
    return true, signs;
end function;
    
// IsSimilarModScalar    
  
IsSimilarModScalar := function( list1, list2 )
    
    F := CoefficientRing( list1[1] );
    n := NumberOfRows( list1[1] );
    scalars := [];
    
    sc := AllRoots( F!1, n );
    
    for i in [1..#list1] do
        issim := false;    
        for s in sc do
            if IsSimilar( list1[i], ScalarMatrix( F, n, s )*list2[i] ) then
                issim := true;
                Append( ~scalars, s );
                break;
            end if;
        end for;
        
        if not issim then return false, []; end if;
        
    end for;
    
    return true, scalars;
end function;
    
IsSimilarToScalarMultiple := function( mat )
    
    F := CoefficientRing( mat );
    n := NumberOfRows( mat );
    
    sc := { x : x in AllRoots( F!1, n ) | x ne 1 };
    
    for s in sc do
        if IsSimilar( mat, ScalarMatrix( F, n, s )*mat ) then
            return true, s;
        end if;
    end for;
    
    return false, _;
end function;
            
    
// select an involution with certain properties
  
InvolutionWithProperty := function( G, func )
    
    repeat
        x := RandomInvolution( G );
    until func( x );
    
    return x;
end function;
          
// split mn x mn matrix into tensor components
// the basis is assumed to be x11,...,x1n,x21,...,x2n,...,xm1,...,xmn      

SplitTensor := function( X, n, m  : SwapFactors := false )
    
    if SwapFactors then 
        temp := n; n := m; m := temp;
    end if;

    d := n*m;
    F := CoefficientRing( X );  
    _ := exists(pos){ pos : pos in [1..d] | X[1,pos] ne 0 };
    bm := (pos-1) div m;
    
    b := Matrix( F, m, m, [ X[i,bm*m+j] : i, j in [1..m]] );
    pos := pos mod m; if pos eq 0 then pos := m; end if;
    c := b[1,pos];
    a := Matrix( F, n, n, [ X[i*m+1,j*m+pos]/c : i, j in [0..n-1]] );
    
    v := exists( r ){ x : x in AllRoots( Determinant( b )^-1, m ) | 
                 x^n eq Determinant( a ) };
    assert v;
    b := r*b; a := r^-1*a;
        
    assert TensorProduct( a, b ) eq X and 
      Determinant( a ) eq 1 and Determinant( b ) eq 1;
    return < a, b >;
end function;

// The following is necessary because of a change that occurred around V2.25 with 
// changing the standard form preserved by OMinus( d, F )

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
// returns this schalar

ScalarOfPreservedForm := function( mat, form )

    i := 1;
    while form[1,i] eq 0 do 
        i +:= 1;
    end while; 

    // form[1,i] is non-zero

    form1 := mat*form*Transpose( mat );
    return form1[1,i]*form[1,i]^-1;
end function;
    

