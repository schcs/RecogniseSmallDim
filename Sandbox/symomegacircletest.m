g0 := Omega( 13, 11 );
f0 := ClassicalForms( g0 )`bilinearForm;
ff := ClassicalForms( g0 )`bilinearForm;
ff[3,3] := 1; ff[11,11] := 1; ff[3,11] := 0; ff[11,3] := 0;
tr := TransformForm( ff, "orthogonalcircle" );
g := sub< GL( 13, 11 ) | tr*g0.1*tr^-1, tr*g0.2*tr^-1 >;


