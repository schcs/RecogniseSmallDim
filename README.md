# RecogniseSmallDim

The package contains Magma implementations for some recognition algorithms for small-dimensional representations 
of classical groups.

The two main functions are RecogniseAltSquare and RecogniseSymSquare. These need to be imported before used:

import "symsquare.m": RecogniseSymSquare;
import "altsquare.m": RecogniseAltSquare;


RecogniseAltSquare( G : 
            type := "SL", 
            CheckResult := true,
            Method := "Recursive" ) 
                                                         
G should be matrix group conjugate to the exterior square representation
of SL( d, q ). Returns true/false, a map from SL( d, q ) to G, a map from 
G to SL( d, q ), and a matrix whose rows form a basis that exhibits the 
alt square structure. The last piece of output can be used to conjugate 
the image of G under the second map into the standard copy of the classical 
group in Magma.
                           
Supply CheckResult := true to check the final result.
                           
he basic algorithm is implemented in two variations. The first uses a recursive call for smaller 
dimensional exterior square recognition, while the second uses recognition of tensor decomposition 
with IsTensor. In small dimensions (how small depends on the type of the group), the version using 
tensor recognition is called, while if the dimension is high enough, then the recursive version is used.
This choice can be overwritten by setting <Method> to "Tensor".
  
RecogniseSymSquare( G : type := "SL", CheckResult := false ) -> BoolElt, Map, Map, GrpMatElt, GrpMatElt
                                                         
G should be matrix group conjugate to the symmetric square representation
of SL( d, q ). Returns true/false, a map from SL( d, q ) to G, a map from 
G to SL( d, q ), and a matrix whose rows form a basis that exhibits the 
sym square structure. The last piece of output can be used to conjugate 
the image of G under the second map into the standard copy of the classical 
group in Magma.

Supply CheckResult := true to check the final result.

The file smalldimreps.m contains an implementation of Greenhill's algorithm
to recognize if a matrix is the alternating square of another matrix.
   
The algorithm is described in C Greenhill, "An algorithm for recognising 
the exterior square of a matrix", Linear and Multilinear Algebra, 1999.
   
The function assumes that the input is a *non-singular* matrix that is a 
member of AltSquare( SL( d, q )) in the basis 
e_12, e_13,...,e_1d,...,e_{d-1}d.
 
Greenhill's paper describes the algorithm for arbitrary, not necessary invertible, matrices, but
this implementation only works for invertible matrices and the other cases may lead to error!

Written by Csaba Schneider.
csaba@mat.ufmg.br
https://schcs.github.io/WP/
