// testing Omega(13,11) in symsquare

bas0 := OmegaPlusBasis( 8, 5, GF( 11 ) : type := "Omega" );
bH := [ bas0[i] : i in [1..35]];
bK := [ bas0[i] : i in [36..49]];
bT := [ bas0[i] : i in [50..89]];
wH := bas0[90];
wK := bas0[91];

a := 6;
bas := BuildBasisOmega( bH, bK, bT : type := "Omega", wH := a*wH, wK := a*wK );
b1 := bH[8]; b2 := bH[14]; b3 := bH[19];
c1 := bK[5]; c2 := bK[8];
a0 := 9*b1+8*b2+8*b3+7*c1+7*c2+3*wH+4*wK;
9*b1+8*b2+8*b3+7*c1+7*c2+3*a*wH+4*a*wK eq bas[13]; 

u := 3; v := 4;

pol := 3/2 + 2*u*(a-1)*1/2+2*v*(a-1)*(-1/2)+u^2*(a-1)^2*2+v^2*(a-1)^2*(1+1/4);
GF(11)!pol eq (bas[13]*fcircle*Matrix( 91, 1, bas[13] ))[1];