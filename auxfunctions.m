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
        
        if not issim then return false, _; end if;
        
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

SplitTensor := function( X, n, m )
    
    d := n*m;
    F := CoefficientRing( X );  
    _ := exists(pos){ pos : pos in [1..d] | X[1,pos] ne 0 };
    bn := (pos-1) div n;
    
    a := Matrix( F, n, n, [ X[i,bn*n+j] : i, j in [1..n]] );
    pos := pos mod n; if pos eq 0 then pos := n; end if;
    c := a[1,pos];
    b := Matrix( F, m, m, [ X[i*n+1,j*n+pos]/c : i, j in [0..m-1]] );
    
    v := exists( r ){ x : x in AllRoots( Determinant( a )^-1, n ) | 
                 x^m eq Determinant( b ) };
    assert v;
    a := r*a; b := r^-1*b;
        
    assert TensorProduct( b, a ) eq X and 
      Determinant( a ) eq 1 and Determinant( b ) eq 1;
    return < a, b >;
end function;
    
      
  
