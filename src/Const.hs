module FunctionsConstant where

import List 

type MA =[[Integer]]            -- matrix
type OB =(Tu,Or)                -- oriented base
type OM1= [Int]                 -- rank1 oriented matroid
type OM2=[[Int]]                -- rank2 oriented matroid
type OM3=[(OM1,OM2)]            -- rank3 oriented matroid
type OM5=[([Int],OM2)]          -- rank5 matroid polytope
type Tu = [Int]                 -- tuple of elements
type Or =  Int                  -- orientation
type OF =[Int]->[Int]->Ordering -- order function, rank~2

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

-- matrix -> chirotope of matrix
m2Chi::MA->[OB]
m2Chi m=zip trn (map toInt (map signum(dets trn m)))
        where n=length m
              r=length(head m)
              trn=tuples r n 

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


-------------------------------------------------------------------
-- potential bases of a matroid
pb::[[Int]]      
pb=[[1,2,3],[1,2,5],[1,3,4],[1,3,5],
    [1,4,5],[2,3,4],[2,4,5],[3,4,5]]

-- hyperline data structure of example matrix M
hyperlines::[([Int],OM2)] 
hyperlines = [ ( [1], [ [2,-4], [-5], [3] ] ),
               ( [2], [ [1, 4], [-3,5]    ] ),
               ( [3], [ [1], [2,-5], [-4] ] ),
               ( [4], [ [1, 2], [-5], [3] ] ),
               ( [5], [ [1], [4], [-2,3]  ] )]

-- main example matrix of Chapter 1 and Chapter 2
m::MA  -- type MA = [[Integer]] 
m=[[ 0,-1, 1],
   [ 0, 0, 1],
   [-1,-1,-1],
   [ 0,-1,-1],
   [ 1, 1, 0]]

-- oriented bases in rank 2 example
r2ex::[OB] 
r2ex
  = [([1,3], 0),([1,4], 1),([1,5],-1),([1,6], 1),
     ([1,7], 1),([1,8], 1),([1,9], 1),([3,4], 1),
     ([3,5],-1),([3,6], 1),([3,7], 1),([3,8], 1),
     ([3,9], 1),([4,5], 1),([4,6], 0),([4,7], 1),
     ([4,8], 1),([4,9], 1),([5,6],-1),([5,7],-1),
     ([5,8],-1),([5,9],-1),([6,7], 1),([6,8], 1),
     ([6,9], 1),([7,8], 1),([7,9], 1),([8,9],-1)]

-- coordinates of example matrix
mex::MA 
mex=[[0,5],[0,7],[0,6],[7,0],[1,2],[4,3],[7,6],[4,9],[6,7]]

-- homogeneous coordinates of example matrix
homCoord::MA
homCoord = map ([1]++) mex

-- hyperline sequences of an example
-- hypex::[([Int],OM2)]
-- hypex=map(\i->([i],chi2HypR2(ctrElChi i(m2Chi mex))))[1..9]

-- r -> n -> alternating oriented matroid, n elements, rank r
altOM::Int->Int->[OB]
altOM r n=zip(tuples r n)(replicate(length(tuples r n))1)

{-
ex::[Int]
ex=[ 1, 1, 1, 1, 1, 1, 1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1, 1,
    -1,-1,-1,-1, 1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1, 1,
    -1,-1,-1,-1, 1,-1,-1, 1, 1,-1, 1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1,
    -1, 1,-1, 1,-1,-1,-1,-1, 1,-1,-1, 1, 1, 1,-1, 1, 1,-1,-1,-1, 1,
    -1,-1,-1,-1,-1,-1, 1, 1, 1, 1,-1, 1,-1,-1,-1,-1,-1,-1, 1,-1,-1,
    -1,-1,-1,-1,-1,-1,-1, 1,-1,-1, 1,-1, 1,-1,-1,-1, 1,-1, 1, 1, 1,
     1,-1, 1, 1, 1,-1, 1, 1,-1,-1, 1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
     1,-1,-1, 1,-1, 1,-1,-1,-1, 1,-1, 1, 1, 1, 1,-1, 1, 1, 1,-1, 1,
     1,-1,-1, 1,-1,-1,-1, 1, 1,-1, 1, 1,-1, 1,-1, 1, 1,-1, 1,-1, 1,
    -1,-1, 1,-1,-1,-1, 1,-1, 1,-1, 1,-1, 1,-1,-1,-1,-1, 1, 1, 1,-1]
-}

-- homogeneous coordinates of 3-cube
cube3::[[Int]]
cube3 = [[1,0,0,0],[1,1,0,0],[1,0,1,0],[1,0,0,1],
         [1,1,1,0],[1,1,0,1],[1,0,1,1],[1,1,1,1]]

-- coordinates of Altshuler's sphere 416
m416::MA
m416=[[1,     0,     0,     0,     0],
      [1, 10000,     0,     0,     0],
      [1,     0, 10000,     0,     0],
      [1,     0,     0, 10000,     0],
      [1,     0,     0,     0, 10000],
      [1,  -132,   264,  9868,  1316],
      [1, -1000,  3100,  7400,  1500],
      [1, -3144,  9434, -3144,  6289],
      [1,  2308, -2564,  5128, -5128],
      [1, 50000, 50000,-50000,-50000]]

-- facets of a 3-sphere of pottery model of Figure 5.6
facetsP::[[Int]] 
facetsP=[[1,2,4,5],[1,2,5,6],[1,2,4,6],
         [1,3,4,5],[1,3,5,6],[1,3,4,6],
         [2,3,4,5],[2,3,5,6],[2,3,4,6]]

-- facets of a 3-sphere of Kleinschmidt
facetsK::[[Int]]
facetsK=[[1,2,3, 4], [1,2,3, 7], [1,2,4, 8], [1,2,6, 7], 
         [1,2,6, 8], [1,3,4, 7], [1,4,5, 6], [1,4,5, 8], 
         [1,4,6, 7], [1,5,6, 8], [2,3,4, 8], [2,3,7,10], 
         [2,3,8, 9], [2,3,9,10], [2,6,7, 9], [2,6,8, 9], 
         [2,7,9,10], [3,4,5, 7], [3,4,5, 8], [3,5,7,10], 
         [3,5,8,10], [3,8,9,10], [4,5,6, 7], [5,6,7, 9], 
         [5,6,8,10], [5,6,9,10], [5,7,9,10], [6,8,9,10]]

-- facets of a 3-sphere of Brueckner
facetsB::[[Int]]
facetsB=[[1,2,3,4],[1,2,3,6],[1,2,4,6],[1,3,4,7],[1,3,6,8],
         [1,3,7,8],[1,4,5,6],[1,4,5,7],[1,5,6,8],[1,5,7,8],
         [2,3,4,8],[2,3,5,6],[2,3,5,8],[2,4,6,7],[2,4,7,8],
         [2,5,6,7],[2,5,7,8],[3,4,7,8],[3,5,6,8],[4,5,6,7]]

-- facets of a 3-sphere of Altshuler
facetsA::[[Int]]
facetsA=[[1,2,5,6],[1,2,5,9],[1,2,6,9],[1,5,7,9],[2,6,8,9],
         [1,4,5,6],[2,3,5,6],[1,4,6,9],[2,3,5,9],[1,4,7,8],
         [2,3,7,8],[1,4,7,9],[2,3,8,9],[1,4,5,8],[2,3,6,7],
         [1,5,7,8],[2,6,7,8],[3,4,7,8],[3,4,7,9],[3,4,8,9],
         [3,5,6,7],[4,5,6,8],[3,5,7,9],[4,6,8,9],[5,6,7,8]]

-- facets of an Altshuler sphere
sphereA425::[[Int]] 
sphereA425 
 = [[1,0,4,5],[3,2,6,7],[5,4,8,9],[7,6,0,1],[9,8,2,3],
    [0,1,3,2],[2,3,5,4],[4,5,7,6],[6,7,9,8],[8,9,1,0],
    [1,0,4,8],[1,0,6,2],[0,1,3,5],[0,1,9,7],[3,2,6,0],
    [3,2,8,4],[2,3,5,7],[2,3,1,9],[5,4,8,2],[5,4,0,6],
    [4,5,7,9],[4,5,3,1],[7,6,0,4],[7,6,2,8],[6,7,9,1],
    [6,7,5,3],[9,8,2,6],[9,8,4,0],[8,9,1,3],[8,9,7,5],
    [8,2,7,5],[0,4,9,7],[2,6,1,9],[4,8,3,1],[6,0,5,3] ]


-- 3-sphere of Gabor G{\'e}vay 
ex::[(Int,[[Int]])]  -- facet number with oriented triangles 
ex=[( 1,[[1,10,7],[1,13,10],[1,7,13],[3,7,10],[3,10,13],[3,13,7]]), 
    ( 2,[[2,11,8],[2,14,11],[2,8,14],[1,8,11],[1,11,14],[1,14,8]]),
    ( 3,[[3,12,9],[3,15,12],[3,9,15],[2,9,12],[2,12,15],[2,15,9]]),
    ( 4,[[4,14,7],[4,12,14],[4,7,12],[6,7,14],[6,14,12],[6,12,7]]),
    ( 5,[[5,15,8],[5,10,15],[5,8,10],[4,8,15],[4,15,10],[4,10,8]]),
    ( 6,[[6,13,9],[6,11,13],[6,9,11],[5,9,13],[5,13,11],[5,11,9]]),
    ( 7,[[1, 7,10],[1,10, 8],[1, 8,14],[1,14, 7],
         [4,10, 7],[4, 8,10],[4,14, 8],[4, 7,14]]),
    ( 8,[[2, 8,11],[2,11, 9],[2, 9,15],[2,15, 8],
         [5,11, 8],[5, 9,11],[5,15, 9],[5, 8,15]]),
    ( 9,[[3, 9,12],[3,12, 7],[3, 7,13],[3,13, 9],
         [6,12, 9],[6, 7,12],[6,13, 7],[6, 9,13]]),
    (10,[[1,13, 7],[1, 7,14],[1,14,11],[1,11,13],
         [6, 7,13],[6,14, 7],[6,11,14],[6,13,11]]),
    (11,[[2,14, 8],[2, 8,15],[2,15,12],[2,12,14],
         [4, 8,14],[4,15, 8],[4,12,15],[4,14,12]]),
    (12,[[3,15, 9],[3, 9,13],[3,13,10],[3,10,15],
         [5, 9,15],[5,13, 9],[5,10,13],[5,15,10]]),
    (13,[[4,12, 7],[4, 7,10],[4,10,15],[4,15,12],
         [3, 7,12],[3,10, 7],[3,15,10],[3,12,15]]),
    (14,[[5,10, 8],[5, 8,11],[5,11,13],[5,13,10],
         [1, 8,10],[1,11, 8],[1,13,11],[1,10,13]]),
    (15,[[6,11, 9],[6, 9,12],[6,12,14],[6,14,11],
         [2, 9,11],[2,12, 9],[2,14,12],[2,11,14]])]
 
-- facets of a 5-sphere of Shemer
facetsS::[[Int]]  -- A 5-sphere of Shemer 
facetsS = [[1,2,3,4,6,7],[1,2,3,4,5,6],[1,2,3,4,5,8],
 [1,3,4,5,6,9],[1,2,4,5,6,9],[2,3,4,5,6,10],[1,2,3,5,6,10],
 [1,2,3,4,7,10],[1,3,4,5,8,9],[1,2,4,5,8,9],[1,2,3,4,8,9],
 [2,3,4,5,8,10],[1,2,3,5,8,10],[1,2,3,4,9,10],[1,3,4,6,7,9],
 [1,2,4,6,7,9],[2,3,4,6,7,10],[1,2,3,6,7,10],[1,3,4,7,9,10],
 [1,2,4,7,9,10],[2,3,4,8,9,10],[1,2,3,8,9,10],[1,2,5,6,7,8],
 [1,3,5,6,7,9],[1,3,5,6,7,10],[1,2,5,6,7,10],[1,2,5,6,8,9],
 [1,2,5,7,8,10],[1,3,5,7,9,10],[1,3,5,8,9,10],[1,2,6,7,8,9],
 [1,2,7,8,9,10],[2,4,5,6,8,9],[2,4,5,6,8,10],[2,4,6,7,9,10],
 [2,4,6,8,9,10],[1,5,6,7,8,9],[2,5,6,7,8,10],[1,5,7,8,9,10],
 [2,6,7,8,9,10],[3,4,5,6,7,8],[3,4,5,6,7,9],[3,4,5,6,8,10],
 [3,4,5,7,8,9],[3,4,6,7,8,10],[3,4,7,8,9,10],[3,5,6,7,8,10],
 [3,5,7,8,9,10],[4,5,6,7,8,9],[4,6,7,8,9,10]]

-- matroid polytope corresponding to a Shemer sphere
res1::[Int]
res1 = [1,1,1,1,1,1,1,-1,-1,-1,1,1,1,-1,-1,-1,-1,-1,-1,-1,-1,
 -1,1,-1,1,1,-1,1,1,-1,-1,1,1,-1,-1,-1,-1,1,-1,1,1,-1,1,1,-1,
 -1,1,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,1,-1,1,-1,-1,1,-1,-1,1,1,
 -1,-1,1,1,-1,1,1,-1,-1,1,-1,1,1,-1,-1,1,1,-1,1,-1,1,-1,-1,1,
 -1,-1,1,1,-1,-1,1,1,-1,1,1,-1,-1,1,-1,1,1,-1,-1,1,1,-1,-1,1,
  1,1,1,-1,-1]
--res2 = dC (zip (tuples 7 10) res1)


-- an example 4-chirotope with 10 elements
chirotope::[Int]   -- given chirotope  10 elements, rank~4 
chirotope
 = [ 1, 1, 1, 1, 1, 1, 1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1, 1,-1,-1,-1,-1,
     1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1, 1,-1,-1,-1,-1, 1,-1,-1, 1,
     1,-1, 1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1,-1, 1,-1, 1,-1,-1,-1,-1, 1,-1,-1, 1,
     1, 1,-1, 1, 1,-1,-1,-1, 1,-1,-1,-1,-1,-1,-1, 1, 1, 1, 1,-1, 1,-1,-1,-1,-1,
    -1,-1, 1,-1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1,-1, 1,-1, 1,-1,-1,-1, 1,-1, 1, 1,
     1, 1,-1, 1, 1, 1,-1, 1, 1,-1,-1, 1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1, 1,-1,-1,
     1,-1, 1,-1,-1,-1, 1,-1, 1, 1, 1, 1,-1, 1, 1, 1,-1, 1, 1,-1,-1, 1,-1,-1,-1,
     1, 1,-1, 1, 1,-1, 1,-1, 1, 1,-1, 1,-1, 1,-1,-1, 1,-1,-1,-1, 1,-1, 1,-1, 1,
    -1, 1,-1,-1,-1,-1, 1, 1, 1,-1]

-- result, a dual 6-chirotope with 10 elements
dCr::[Int]  -- result of dC 4 10 chirotope
dCr 
 = [-1,-1, 1,-1,-1,-1, 1,-1,-1,-1,-1,-1, 1, 1, 1, 1,-1, 1, 1, 1,-1,-1, 1, 1, 1,
     1,-1,-1, 1, 1, 1,-1,-1,-1, 1,-1, 1,-1,-1,-1, 1, 1, 1, 1, 1,-1, 1, 1,-1, 1,
    -1, 1, 1, 1, 1,-1, 1, 1,-1,-1,-1, 1, 1, 1,-1,-1, 1,-1, 1,-1, 1,-1, 1, 1, 1,
    -1,-1,-1,-1,-1, 1,-1,-1, 1,-1, 1,-1,-1,-1,-1, 1,-1,-1, 1, 1, 1,-1,-1,-1, 1,
     1,-1, 1,-1, 1,-1, 1, 1,-1, 1,-1, 1,-1, 1, 1,-1,-1, 1,-1, 1, 1,-1, 1,-1, 1,
    -1, 1, 1,-1, 1, 1,-1,-1, 1,-1, 1, 1,-1,-1, 1,-1, 1,-1,-1,-1,-1,-1, 1, 1,-1,
     1,-1, 1,-1, 1,-1,-1,-1,-1,-1, 1, 1,-1,-1, 1,-1, 1,-1,-1,-1,-1, 1,-1, 1,-1,
     1,-1, 1,-1, 1,-1, 1,-1, 1, 1,-1, 1,-1, 1, 1, 1, 1,-1, 1,-1, 1,-1, 1,-1, 1,
    -1, 1,-1, 1,-1, 1,-1, 1,-1, 1]

--sort (allLinks kleinBottle)
--  [(1,[[2,7,4,3,5,8,2]]),
--   (2,[[1,7,6,3,9,8,1]]),
--   (3,[[1,4,6,2,9,5,1]]),
--   (4,[[1,3,6,8,5,7,1]]),
--   (5,[[1,3,9,7,4,8,1]]),
--   (6,[[2,3,4,8,9,7,2]]),
--   (7,[[1,2,6,9,5,4,1]]),
--   (8,[[1,2,9,6,4,5,1]]),
--   (9,[[2,3,5,7,6,8,2]])]

-- triangle list of pinched sphere
pinchedSphere::[[Int]]
pinchedSphere 
 = [[1,2, 3],[1,2, 4],[1,3, 8],[1,4,10],[1,5, 8],
    [1,5, 9],[1,6, 7],[1,6, 9],[1,7,10],[2,3, 9],
    [2,4,10],[2,5, 6],[2,5,10],[2,6, 8],[2,7, 8],
    [2,7, 9],[3,4, 5],[3,4, 9],[3,5, 7],[3,6, 7],
    [3,6,10],[3,8,10],[4,5, 6],[4,6, 8],[4,7, 8],
    [4,7, 9],[5,7,10],[5,8, 9],[6,9,10],[8,9,10]]

-- d -> chirotope of d-cube
cube2Chi::Int->[OB]
cube2Chi  d
 =zip tu (map(\t->toInt(signum(det
         (subMA t (cube2MAHom d))))) tu )
  where tu = tuples (d+1) (2^d) 

-- d -> matrix (homogeneous) of d-cube
cube2MAHom::Int->MA
cube2MAHom d = map([1]++)(cube2MA d) 

-- indices -> matrix -> submatrix
subMA::[Int]->MA->MA
subMA t m = map(\i->m!!(i-1))t

-- d -> matrix of d-cube
cube2MA::Int->MA
cube2MA 1 = [[0],[1]]
cube2MA d =  (map([0]++)(cube2MA(d-1)))
           ++(map([1]++)(cube2MA(d-1)))

