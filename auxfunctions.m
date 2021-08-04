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
    
// the following function comes from ClassicalRewrite    
// the comment was also copied from there      
    
/*  
  The various components of this package use different standard bases 
  for the classical groups, and so it is necessary to convert one
  basis for the others. We will use 3 bases:
  
  My basis: the bases used in the ClassicalRewrite package
  SX(n,q): the basis used in Magma's SX(n,q) function
  ClassicalStandardGenerators: the basis used by the output of 
  ClassicalStandardGenerators
    
  Symplectic:
  
  My basis: e1,..,en,fn,...,f1
  SX(n,q): e1,..,en,fn,...,f1
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn
  
  Unitary: 
  
  My basis: e1,...,en,fn,...,f1(,w)
  SX(n,q): e1,...,en,(w,),fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn(,w)
    
  Omega+:
    
  My basis: e1,...,en,fn,...,f1
  SX(n,q): e1,...,en,fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn  
  
  Omega-:
    
  My basis: e1,...,en,w1,w2,fn,...,f1,w1,w2 (changed from Version 5)
  SX(n,q): e1,...,en,u1,u2,fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn,w1,w2
    
  where Q(w1) eq -2 and Q(w2) eq 2z where z is a primitive root in GF(q)
  Q(u1) eq 1 and Q(u2) is ???  
    
  Omega:
    
  My basis: e1,...,en,fn,...,f1(,w)
  SX(n,q): e1,...,en,u,fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn,v
    
  where Q(w) = ???, Q(u) = ???, Q(v) eq ???  
  
*/
    
    // convert ClassicalStandardGenerators( type, n, q ) to SX(n,q)

ConjugateClassicalStandardToSXnq := function( type, dim, q )
    
    if type in { "SL", "Omega-", "Omega" } then
        
        list := [ i : i in [1..dim]];
        
    elif dim eq 2 and type eq "SU" and IsEven( q ) then
       
       gamma := PrimitiveElement( GF( q ));
       q0 := Round( Sqrt( q ));
       return GL(2,q)![gamma^((q0 div 4)*(Round(-Sqrt(q))-1)),0,0,
                      gamma^((q0 div 4)*(Round(Sqrt(q))+1))];
            
    elif type eq "SU" and IsOdd( dim ) then
        
        list := [1..dim-2 by 2] cat [ dim ] cat [dim-1..2 by -2];
        conj := GL( dim, q )!PermutationMatrix( GF( q ), list );
                
    elif IsEven( dim ) then
        
        list := [ i : i in [1..dim-1 by 2]] cat 
                [ i : i in [dim..2 by -2 ]];
        
    elif IsOdd( dim ) then
        
        list := [ dim ] cat [ i : i in [1..dim-2 by 2]] cat 
                [ i : i in [dim-1..2 by -2 ]];

    end if;
    
    return  GL( dim, q )!PermutationMatrix( GF( q ), Sym( dim )!list )^-1;
end function;
