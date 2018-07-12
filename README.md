# RecogniseSmallDim

The package contains Magma implementations for some recognition algorithms for small-dimensional representations 
of classical groups.

The two main functions are RecogniseAltSquare and RecogniseSymSquare.

intrinsic RecogniseAltSquare( G::GrpMat : 
            type := "SL", 
            CheckResult := true,
            UseTensorDecomposition := false ) 
          -> BoolElt, Map, Map, GrpMatElt
                                                         
G should be matrix group conjugate to the exterior square representation
of SL( d, q ). Returns true/false, a map from SL( d, q ) to G, a map from 
G to SL( d, q ), and a matrix whose rows form a basis that exhibits the 
alt square structure. 
                           
Supply CheckResult := true to check the final result.
                           
The basic algorithm is implemented in two variations. The first uses a 
recursive call for smaller dimensional alternating square recognition, while
the second uses recognition of tensor decomposition with IsTensor. 
For SL(d,q) with d=5,6,8 the tensor decomposition version is used while for
SL(d,q) with d=7 or d>8 the recursive version is called as default. 
This choice can be overwritten by setting UseTensorDecomposition to be true.
  
intrinsic RecogniseSymSquare( G::GrpMat : type := "SL", CheckResult := false ) 
          -> BoolElt, Map, Map, GrpMatElt
                                                         
G should be matrix group conjugate to the symmetric square representation
of SL( d, q ). Returns true/false, a map from SL( d, q ) to G, a map from 
G to SL( d, q ), and a matrix whose rows form a basis that exhibits the 
sym square structure. 

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
www.mat.ufmg.br/~csaba
