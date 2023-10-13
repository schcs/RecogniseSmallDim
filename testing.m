
SymSquare := function( type, n, q : twist := false )

  if type eq "SL" then
      g := SL( n, q );
  elif type eq "Sp" then
      g := Sp( n, q );
  elif type eq "SU" then
      g := SU( n, q );
      q := q^2;
  elif type eq "Omega" then
      g := Omega( n, q );
  elif type eq "Omega+" then
      g := OmegaPlus( n, q );
  elif type eq "Omega-" then
      g := OmegaMinus( n, q );
  elif type eq "GL" then
      g := GL( n, q );
  elif type eq "GU" then
      g := GU( n, q );
      q := q^2;
  elif type eq "GO" then
      g := GO( n, q );
  elif type eq "GO+" then
      g := GOPlus( n, q );
  elif type eq "GO-" then
      g := GOMinus( n, q );
  elif type eq "SO" then
      g := SO( n, q );
  elif type eq "SO+" then
      g := SOPlus( n, q );
  elif type eq "SO-" then
      g := SOMinus( n, q );
  end if;

  comps := [ x : x in CompositionFactors( SymmetricSquare( GModule( g ))) |
             Dimension( x ) gt 1 ];
  assert #comps eq 1;
  S := ActionGroup( comps[1] );
  
  if twist then
      S := S^Random( GL( Dimension( S ), q ));
  end if;
  
  return S;
end function;
    
AltSquare := function( type, n, q : twist := false )
  
  if type eq "SL" then
      g := SL(n,q);
  elif type eq "Sp" then
      g := Sp(n,q);
  elif type eq "SU" then
      g := SU(n,q);
      q := q^2;
  elif type eq "Omega+" then
      g := OmegaPlus(n,q);
  elif type eq "Omega-" then
      g := OmegaMinus(n,q);
  elif type eq "Omega" then
      g := Omega(n,q);
  elif type eq "GL" then
      g := GL(n,q);
  elif type eq "GU" then
      g := GU(n,q);
      q := q^2;
  elif type eq "GO+" then
      g := GOPlus(n,q);
  elif type eq "GO-" then
      g := GOMinus(n,q);
  elif type eq "GO" then
      g := GO(n,q);
  elif type eq "SO+" then
      g := SOPlus(n,q);
  elif type eq "SO-" then
      g := SOMinus(n,q);
  elif type eq "SO" then
      g := SO(n,q);

  end if;
    
  comps := [ x : x in CompositionFactors( ExteriorSquare( GModule( g ))) |
             Dimension( x ) gt 1 ];
  assert #comps eq 1;
  S := ActionGroup( comps[1] );

  if twist then
      x := Random( GL( Dimension( S ), q ));
  else 
      x := One( GL( Dimension( S ), q ));
  end if;

  return S^x, GeneratorsSequence( S^x );
end function;
    
TestSymSquare := function(type, d, q : NrTries := 100 )
    
    if d ge 20 and NrTries gt 20 then NrTries := 20; end if;
    
    type0 := case< type | "GL": "SL", "GU": "SU", "SO+": "Omega+", 
                         "GO+": "Omega+", "SO-": "Omega-", "GO-": "Omega-", 
                         "SO": "Omega", "GO": "Omega", default: type >;

    for i in [1..NrTries] do
        G := SymSquare( type, d, q : twist := true );
        v, a, b, bas := RecogniseSymSquare( G : type := type0, CheckResult := true );
        assert v and { x@b@a*x^-1 eq x^0 : x in { Random( G ) : z in [1..100] }}           eq { true };
    end for;
    
    return true;
end function;
    
TestSymSquare_new := function(type, d, q : NrTries := 100 )
    
    if d ge 20 and NrTries gt 20 then NrTries := 20; end if;
    
    type0 := case< type | "GL": "SL", "GU": "SU", "SO+": "Omega+", 
                         "GO+": "Omega+", "SO-": "Omega-", "GO-": "Omega-", 
                         "SO": "Omega", "GO": "Omega", default: type >;

    for i in [1..NrTries] do
        G := SymSquare( type, d, q : twist := true );
        v, a, b, bas := RecogniseSymSquare( G : type := type0, CheckResult := true );
        for k in [1..100] do 
            x := Random( G );
            v, y := AltSymPreimage( G, x ); assert v;
            v, x1 := AltSymImage( G, y ); assert v;
            if x*x1^-1 ne x^0 then return false; end if;
        end for; 
    end for;
    
    return true;
end function;

TestAltSquare_new := function(type, d, q : NrTries := 100 )
    
    if d ge 20 and NrTries gt 20 then NrTries := 20; end if;
    
    type0 := case< type | "GL": "SL", "GU": "SU", "SO+": "Omega+", 
                         "GO+": "Omega+", "SO-": "Omega-", "GO-": "Omega-", 
                         "SO": "Omega", "GO": "Omega", default: type >;

    for i in [1..NrTries] do
        G := AltSquare( type, d, q : twist := true );
        v, a, b, bas := RecogniseAltSquare( G : type := type0, CheckResult := true );
        for k in [1..100] do 
            x := Random( G );
            v, y := AltSymPreimage( G, x ); assert v;
            v, x1 := AltSymImage( G, y ); assert v;
            if x*x1^-1 ne x^0 then return false; end if;
        end for; 
    end for;
    
    return true;
end function;


TestSymSquare2 := function( type, limd, limq, nr )
    
    vb := GetVerbose( "SymSquareVerbose" );
    SetVerbose( "SymSquareVerbose", 0 );


    ranged := case< type | "SL": [2..limd], "GL": [3..limd], 
              "SU": [3..limd], "GU": [3..limd],
              "Sp": [4..limd by 2], 
              "Omega+": [10..limd by 2], "GO+": [10..limd by 2], "SO+": [10..limd by 2],
              "Omega-": [8..limd by 2], "GO-": [10..limd by 2], "SO-": [10..limd by 2],
              "Omega": [9..limd by 2],   "GO": [9..limd by 2], "SO": [9..limd by 2],
              default: [3..limd]  >;


    ranged := case< type | "Sp": [2..limd by 2], "Omega+": [2..limd by 2], "Omega-": [2..limd by 2],
                           "Omega": [3..limd by 2], default: [2..limd] >;

    
    exc := [ <"Sp", 6, 3>, <"Sp", 9, 3 >, <"SU", 6, 7 >, <"Sp", 10, 3 >,
            <"GO+",10,3>,<"SO+",10,3>,<"Omega+",10,3>,<"GO+",10,9>,
            <"SO+",10,9>,<"GO+",10,27>,<"SO+",10,27>,
            <"Omega-",10,3>,
            <"GO-",10,3>,<"GO-",10,9>,<"GO-",10,27>,
            <"SO-",10,3>,
            <"GO",9,5>,<"GO",9,25>,
            <"SO",9,5>,<"SO",9,25>];

    exc = [];

    qs := [ x : x in [3..limq] | IsPrimePower( x )];
    for d in ranged do
        for q in qs do
            if not IsNewCodeApplicable( "Sym", type, d, q ) then 
                print d, q, "skipped";
                continue;
            end if;

            print d, q, ":", TestSymSquare( type, d, q : NrTries := nr );;
        end for;
    end for;
    
    SetVerbose( "SymSquareVerbose", vb );
    
    return true;
end function;


TestAltSquare := function( type, d, q : NrTries := 100,
                                        Method := "Recursive" )
    
    if d ge 20 then NrTries := 20; end if;

    type0 := case< type | "GL": "SL", "GU": "SU", "SO+": "Omega+", 
                         "GO+": "Omega+", "SO-": "Omega-", "GO-": "Omega-", 
                         "SO": "Omega", "GO": "Omega", default: type >;

    
    for i in [1..NrTries] do
        G := AltSquare( type, d, q : twist := true );
        v, a, b, bas := RecogniseAltSquare( G : type := type0, 
                                                CheckResult := true,
                                                Method := Method );
        assert v and { x@b@a*x^-1 eq x^0 : x in { Random( G ) : z in [1..100] }} eq { true };
    end for;
    
    return true;
end function;
    
TestAltSquare2 := function( type, limd, limq, nr : 
                  Method := "Recursive" )
    
    vb := GetVerbose( "SymSquareVerbose" );
    SetVerbose( "SymSquareVerbose", 0 );
    
    ranged := case< type |  "Sp": [8..limd by 2],
              "SU": [3..limd], "GU": [3..limd],
              "Omega+": [10..limd by 2], "GO+": [12..limd by 2], "SO+": [12..limd by 2], 
              "Omega-": [10..limd by 2], "GO-": [12..limd by 2], "SO-": [12..limd by 2],
              "Omega": [9..limd by 2], "GO": [9..limd by 2], "SO": [9..limd by 2],
              default: [3..limd]  >;
    
    ranged := case< type | "Sp": [4..limd by 2], "Omega+": [4..limd by 2], "Omega-": [4..limd by 2],
                           "Omega": [3..limd by 2], default: [3..limd] >;

    qs := [ x : x in [3..limq] | IsPrimePower( x )];
    exc := []; //[ <"Sp", 10, 3>, <"Sp", 10, 9 >, <"Sp",10,27> ];
    for d in ranged do
        for q in qs do
            if not IsNewCodeApplicable( "Alt", type,d,q ) then 
                print "skipping", <type,d,q>;
                continue;
            end if;
	        print d, q, ":", TestAltSquare( type, d, q : NrTries := nr,
			 Method := Method );
        end for;
    end for;
    
    SetVerbose( "SymSquareVerbose", vb );
    
    return true;
end function;

SymSquareVector := function( dim, vec )

    vec := Eltseq( vec );
    res := [];
    for i in [1..#vec] do
        if vec[i] ne 0 then
            Append( ~res, <vec[i],funcposinv_symsquare( dim, i )>);
        end if;
    end for;

    return res;
end function;

VectorSymSquare := function( dim, vec : type := "SL" )

    res := [];
    d := #Eltseq( vec );
    for i in [1..d] do 
        if vec[i] ne 0 then
            Append( ~res, <vec[i],funcposinv_symsquare( dim, i : type := type )>);
        end if;
    end for;

    return res;
end function;

VectorAltSquare := function( dim, vec : type := "SL" )

    res := [];
    d := #Eltseq( vec );
    for i in [1..d] do 
        if vec[i] ne 0 then
            Append( ~res, <vec[i],funcposinv_altsquare( dim, i : type := type )>);
        end if;
    end for;

    return res;
end function;
