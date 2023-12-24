module Bokowski.Matrix where

import Data.List 

type MA =[[Integer]]            -- matrix
type OB =(Tu,Or)                -- oriented base
type Tu = [Int]                 -- tuple of elements
type Or =  Int                  -- orientation

-- r -> n -> all r-tuples of [1..n]
tuples::Int->Int->[[Int]]       
tuples 0 n = [[]]
tuples r n = tuplesL r [1..n]
  
-- r -> list -> all r-tuples of list
tuplesL::Int->[Int]->[[Int]]  
tuplesL  r list@(x:xs)        
  | length list <  r = []
  | length list == r = [list] 
  | r == 1           = [[el]|el<-list]
  | otherwise = [[x]++el| el<-tuplesL (r-1) xs]
                 ++tuplesL r xs

-- matrix -> determinant of matrix
det::MA -> Integer 
det m
 |n == 1   = head (head m)
 |otherwise=sum(map
  (\i->((-1)^(i+1))*(head(m!!i))*(det
  [(map tail m)!!l|l<-[0..n-1],l/=i]))[0..n-1])
  where n = length m

-- rsets -> matrix -> (r x r)-sub-determinants
dets::[[Int]]->MA-> [Integer]
dets sets matrix = [det[matrix!!(i-1)|i<-set]|set<-sets] 

-- matrix -> chirotope of matrix
m2Chi::MA->[OB]
m2Chi m=zip trn (map toInt (map signum(dets trn m)))
        where n=length m
              r=length(head m)
              trn=tuples r n 

-- exterior product in dimension 3
xProd::MA->[Integer]
xProd  [v1,v2] =[  det [[v1!!1,v1!!2],[v2!!1,v2!!2]],
                 -(det [[v1!!0,v1!!2],[v2!!0,v2!!2]]),
                   det [[v1!!0,v1!!1],[v2!!0,v2!!1]] ]

-- set1 -> set2 -> set1 contained in set2?
isSubSet::[Int]->[Int]->Bool
isSubSet  []     set = True
isSubSet  (x:xs) set  | x `elem` set = isSubSet xs set
                      | otherwise    = False

---------------------------------------------------------------
-- matrix -> 2-element minimal dependent sets
minDep2::MA->[[Int]] 
minDep2 m 
 =[[a,b]|[a,b]<-tuples 2 5,xProd[m!!(a-1),m!!(b-1)]==[0,0,0]]

-- matrix -> 3-element minimal dependent sets
minDep3::MA->[[Int]]
minDep3 m=[t|t<-tuples 3 5,and[not(isSubSet p t)|p<-mD], 
             head(dets [t] m)==0]
                                    where mD = minDep2 m

-- matrix -> 4-element minimal dependent sets
minDep4::MA->[[Int]]
minDep4 m=[q|q<-tuples 4 5,and[not(isSubSet t q)|t<-mD]]
           where mD = minDep2 m ++ minDep3 m

-- d -> matrix of d-cube
cube2MA::Int->MA
cube2MA 1 = [[0],[1]]
cube2MA d =  (map([0]++)(cube2MA(d-1)))
           ++(map([1]++)(cube2MA(d-1)))

-- d -> matrix (homogeneous) of d-cube
cube2MAHom::Int->MA
cube2MAHom d = map([1]++)(cube2MA d) 

-- indices -> matrix -> submatrix
subMA::[Int]->MA->MA
subMA t m = map(\i->m!!(i-1))t

