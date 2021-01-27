q := 7;
F := GF(q); z := PrimitiveElement( GF( q ));
mat := ClassicalForms( OmegaMinus( 2, q ))`bilinearForm;
z1 := mat[1,1]; z2 := mat[2,2]; 

formplus := function( i, j )
    
    if i+j eq 21 then return 1; else return 0; end if;

end function;

formminus := function( i, j )

    if (not i in {7,8}) and i + j eq 15 then 
        return 1;
    elif i eq 7 and j eq 7 then
        return z1;
    elif i eq 8 and j eq 8 then
        return z2;
    else
        return 0;
    end if;

end function;

dc := 11;
formcircle := function( i, j )

    if (i ne (dc+1) div 2) and i + j eq dc + 1 then 
        return 1;
    elif i eq (dc+1) div 2 and j eq (dc+1) div 2 then
        return 1/2;
    else
        return 0;
    end if;

end function;


fplus := ZeroMatrix( F, 7*15, 7*15 );

for i in [1..105] do
    for j in [1..105] do 
        pair1 := funcposinv_symsquare( 14, i );
        pair2 := funcposinv_symsquare( 14, j );
        val := (formplus( pair1[1], pair2[1] )*formplus( pair1[2], pair2[2] )+
                formplus( pair1[1], pair2[2] )*formplus( pair1[2], pair2[1] ))/2;
        fplus[i,j] := val;
    end for;
end for;


fminus := ZeroMatrix( F, 105, 105 );

for i in [1..105] do
    for j in [1..105] do 
        pair1 := funcposinv_symsquare( 14, i );
        pair2 := funcposinv_symsquare( 14, j );
        val := (formminus( pair1[1], pair2[1] )*formminus( pair1[2], pair2[2] )+
                formminus( pair1[1], pair2[2] )*formminus( pair1[2], pair2[1] ))/2;
        fminus[i,j] := val;
    end for;
end for;

fcircle := ZeroMatrix( F, dc*(dc+1) div 2, dc*(dc+1) div 2 );

for i in [1..dc*(dc+1)/2] do
    for j in [1..dc*(dc+1)/2] do 
        pair1 := funcposinv_symsquare( dc, i );
        pair2 := funcposinv_symsquare( dc, j );
        val := (formcircle( pair1[1], pair2[1] )*formcircle( pair1[2], pair2[2] )+
                formcircle( pair1[1], pair2[2] )*formcircle( pair1[2], pair2[1] ))/2;
        fcircle[i,j] := val;
    end for;
end for;

fformcircle := function( u, v )

    v := Eltseq( v );
    return (u*fcircle*Matrix( F, #v, 1, v ))[1];
end function;

fform0 := function( u, v )

    v := Eltseq( v );
    return (u*form0*Matrix( F, #v, 1, v ))[1];
end function;
