SymSquare := function( type, n, q : twist := false )

  if type eq "SL" then
      S := ActionGroup( SymmetricSquare( GModule( SL( n, q ))));
  elif type eq "Sp" then
      S := ActionGroup( SymmetricSquare( GModule( Sp( n, q ))));
  elif type eq "SU" then
      S := ActionGroup( SymmetricSquare( GModule( SU( n, q ))));
  elif type eq "Omega" then
      S := ActionGroup( SymmetricSquare( GModule( Omega( n, q ))));
  elif type eq "Omega+" then
      M := SymmetricSquare( GModule( OmegaPlus( n, q )));
      W := MinimalSubmodules( M )[1];
      S := ActionGroup( M/W );
  elif type eq "Omega-" then
      S := ActionGroup( SymmetricSquare( GModule( OmegaMinus( n, q ))));
  end if;
  
  if twist then
      S := S^Random( GL( Round((n+1)*n/2), q ));
  end if;
  
  return S;
end function;
    
AltSquare := function( type, n, q : twist := false )
    
  gens := ClassicalStandardGenerators( type, n, q );  
    
  gensS := [ __funcSLdqToAltSquare( x ) : x in gens ];
  
  S := sub< GL( NumberOfRows( gensS[1] ), CoefficientRing( gensS[1] )) | 
       gensS >;
  
  if twist then
      x := Random( GL( Round((n-1)*n/2), q ));
  else 
      x := One( GL( Round((n-1)*n/2), q ));
  end if;
  
  return S^x, [ GL( Round((n-1)*n/2), q )!(x^-1*y*x) : y in gensS ];
end function;
    
TestSymSquare := function( d, q : NrTries := 100 )
    
    if d ge 20 then NrTries := 20; end if;
    
    for i in [1..NrTries] do
        G := SymSquare( "SL", d, q : twist := true );
        v, a, b, bas := RecogniseSymSquare( G : CheckResult := true );
        assert v and { x@b@a*x^-1 eq x^0 : x in { Random( G ) : z in [1..100] }}           eq { true };
    end for;
    
    return true;
end function;
    
TestSymSquare2 := function( limd, limq, nr )
    
    vb := GetVerbose( "SymSquareVerbose" );
    SetVerbose( "SymSquareVerbose", 0 );
    
    qs := [ x : x in [3..limq] | IsPrimePower( x ) and IsOdd( x )];
    for d in [2..limd] do
        for q in qs do
            print d, q, ":", TestSymSquare( d, q : NrTries := nr );;
        end for;
    end for;
    
    SetVerbose( "SymSquareVerbose", vb );
    
    return true;
end function;


TestAltSquare := function( d, q : NrTries := 100,
			   UseTensorDecomposition := false )
    
    if d ge 20 then NrTries := 20; end if;
    
    for i in [1..NrTries] do
        G := AltSquare( "SL", d, q : twist := true );
        v, a, b, bas := RecogniseAltSquare( G : CheckResult := true,
			UseTensorDecomposition := UseTensorDecomposition );
        assert v and { x@b@a*x^-1 eq x^0 : x in { Random( G ) : z in [1..100] }}           eq { true };
    end for;
    
    return true;
end function;
    
TestAltSquare2 := function( limd, limq, nr : UseTensorDecomposition := false )
    
    vb := GetVerbose( "SymSquareVerbose" );
    SetVerbose( "SymSquareVerbose", 0 );
    
    qs := [ x : x in [3..limq] | IsPrimePower( x ) and IsOdd( x )];
    for d in [3..limd] do
        for q in qs do
	    print d, q, ":", TestAltSquare( d, q : NrTries := nr,
			 UseTensorDecomposition := UseTensorDecomposition );
        end for;
    end for;
    
    SetVerbose( "SymSquareVerbose", vb );
    
    return true;
end function;
