WriteVectorSparseForm := function( vec )
    
    str := "";
    for i in [1..#Eltseq( vec )] do
            if vec[i] ne 0 then
            coo := funcposinv_altsquare( 12, i : type := "Sp" );
            str := str cat IntegerToString( Integers()!vec[i] ) 
                   cat "*[" cat IntegerToString( coo[1] ) cat "," cat
                   IntegerToString( Integers()!coo[2] ) cat "] ";
        end if;
    end for;
    
    return str;
end function;
    
/* Start Sp(12,11) */
    
g := Sp( 12, 11 ); 
/* the exterior square of this group splits, it was checked */

g := sub< GL( 65, 11 )| __funcSLdqToAltSquare( g.1 : type := "Sp" ), 
     __funcSLdqToAltSquare( g.2 : type := "Sp" )>;                   

form := ClassicalForms( g )`bilinearForm;                                      

hpos := [1,2,3,10,11,12];
kpos := [4,5,6,7,8,9];

V := VectorSpace( GF( 11 ), 65 );
V6 := VectorSpace( GF( 11 ), 6 );

bash := [ Zero( V ) : x in [1..14]];
bask := [ Zero( V ) : x in [1..14]];
bast := [ Zero( V ) : x in [1..36]];

w := Zero( V );

mat := Matrix( GF( 11 ), 6, 6, 
               [[1,0,0,0,0,-1],
                [0,1,0,0,0,-1],
                [0,0,1,0,0,-1],
                [0,0,0,1,0,-1],
                [0,0,0,0,1,-1],
                [1,1,1,1,1,1]]);

vecs := [ Zero( V ) : i in [1..6]];
bas := [ BasisMatrixForAltSquareSp( 12, GF( 11 ))[i,j] : 
         i in [1..65], j in [1..66] | j ne 46 ];
bas := Matrix( GF( 11 ), 65, 65, bas );

bvecs := [ funcpos_altsquare( 12, 1, 12 : type := "Sp" ),
           funcpos_altsquare( 12, 2, 11 : type := "Sp" ),
           funcpos_altsquare( 12, 3, 10 : type := "Sp" ),
           funcpos_altsquare( 12, 4, 9 : type := "Sp" ),
           funcpos_altsquare( 12, 5, 8 : type := "Sp" )];
           
for i in [1..6] do
    for j in [i+1..6] do
        if i+j ne 7 then
            pos := funcpos_altsquare( 12, hpos[i], hpos[j] : type := "Sp" );    
            bash[funcpos_altsquare( 6, i, j : type := "Sp" )] := bas[pos];
        elif i+j eq 7 and i lt 3 then
            vec := V6![0,0,-1,0,0,0];
            vec[i] := 1;
            coeff := vec*mat^-1;
            bash[funcpos_altsquare( 6, i, j : type := "Sp" )] := 
              &+[ coeff[m]*bas[bvecs[m]] : m in [1..5]];
        end if;
    end for;
end for;

for i in [1..6] do
    for j in [i+1..6] do
        if i+j ne 7 then
            pos := funcpos_altsquare( 12, kpos[i], kpos[j] : type := "Sp" );    
            bask[funcpos_altsquare( 6, i, j : type := "Sp" )] := bas[pos];
        elif i+j eq 7 and i lt 3 then
            vec := V6![0,0,0,0,0,-1];
            vec[3+i] := 1;
            print i, j, vec;
                        
            coeff := vec*mat^-1;
            bask[funcpos_altsquare( 6, i, j : type := "Sp" )] := 
              &+ [ coeff[m]*bas[bvecs[m]] : m in [1..5]];
        end if;
    end for;
end for;

for i in [1..6] do
    for j in [1..6] do
        if hpos[i] lt kpos[j] then
            bast[(i-1)*6+j] := bas[funcpos_altsquare( 12, hpos[i], kpos[j] : 
                                       type := "Sp" )];
        else
            bast[(i-1)*6+j] := -bas[funcpos_altsquare( 12, kpos[j], hpos[i] : 
                                       type := "Sp" )];
        end if;
    end for;
end for;

vec := V6![1,1,1,0,0,0];
coeff := vec*mat^-1;

w := &+ [ coeff[m]*bas[bvecs[m]] : m in [1..5]];

    
        
            


