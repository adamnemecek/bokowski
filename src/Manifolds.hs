module Manifolds where

import List

type Star=(Int,[Int])           -- star  (vertex,link)

-- facets of a 3-sphere of Altshuler
facetsA::[[Int]]
facetsA=[[1,2,5,6],[1,2,5,9],[1,2,6,9],[1,5,7,9],[2,6,8,9],
         [1,4,5,6],[2,3,5,6],[1,4,6,9],[2,3,5,9],[1,4,7,8],
         [2,3,7,8],[1,4,7,9],[2,3,8,9],[1,4,5,8],[2,3,6,7],
         [1,5,7,8],[2,6,7,8],[3,4,7,8],[3,4,7,9],[3,4,8,9],
         [3,5,6,7],[4,5,6,8],[3,5,7,9],[4,6,8,9],[5,6,7,8]]

-- simplicial facets of 3-sphere -> subfacets
subfacets::[[Int]]->[[Int]]         
subfacets facets = nub (sub facets)
  where sub::[[Int]]->[[Int]]
        sub [] = []
        sub (f:fs) = [ f\\[j]| j<-f] ++ sub fs

--
symmetry::Int->Int
symmetry k = 15 - k



-----------------------------------------------------------
-- list of triangles -> lists of possisble stars
posStars::[[Int]]->[[Star]] 
posStars triangles
 = map(\n->(nStars([t|t<-triangles,n`elem`t]) n)) 
       (sort (nub (concat triangles)))

--used in posStars
nStars::[[Int]]->Int->[Star]
nStars [] _ = [] 
nStars (t:ts) n 
 =(completeStars (n,t\\[n]) ts)++(nStars ts n)

-- complete possible stars
completeStars::Star->[[Int]]->[Star]
completeStars (n,(x:xs)) trs 
 |x==last xs = [(n,xs)]        -- completed link
 |trs == []  = []              -- triangle list empty
 |otherwise
  =concat
   (map(\y->completeStars y [t|t<-trs, x`notElem`t])  
   [(n,(j:(x:xs)))|j<-(concat[t\\[n,x]|t<-trs,x`elem`t])]) 

-- stars -> do they form a 2-sphere?
isSphere::[(Int,[Int])]->Bool
isSphere stars = f_0 - f_1 + f_2 == 2
  where f_0 = length stars  
        f_1 = div inciEdgeTriangle 2
        f_2 = div inciEdgeTriangle 3
        inciEdgeTriangle
          =sum(map length(map snd stars))

-- stars -> do they form a torus?
isTorus::[(Int,[Int])]->Bool
isTorus stars = f_0 - f_1 + f_2 == 0
  where f_0 = length stars  
        f_1 = div inciEdgeTriangle 2
        f_2 = div inciEdgeTriangle 3
        inciEdgeTriangle
         =sum(map length(map snd stars))

-- stars -> genus of triangulated 2-manifold
genusManifold::[(Int,[Int])]->Int
genusManifold stars = div (2 -(f_0 - f_1 + f_2)) 2
  where f_0 = length stars  
        f_1 = div inciEdgeTriangle 2
        f_2 = div inciEdgeTriangle 3
        inciEdgeTriangle
          =sum(map length(map snd stars))

-- star -> star -> adjacent elements
adjEl::Star->Star->[Int] 
adjEl (a,bs) (x,ys)  = [after a ys, before a ys]
   where after::(Eq a)=>a->[a]->a 
         after p [] = p           
         after p (u:us) 
          |p==last us = u 
          |p==u       = head us 
          |otherwise  = after p us
         before::(Eq a)=>a->[a]->a 
         before p ls = after p (reverse ls)

-- star -> partial 2-manifold -> star consistent?
consistentStar::Star->[Star]->Bool 
consistentStar star partialManifold
 = and (map (\st->consistentStarPair star st) 
   partialManifold)

-- used in consistentStar
consistentStarPair::Star->Star->Bool 
consistentStarPair (a,bs) (x,ys) 
 |(a `notElem` ys) && (x `notElem` bs)= True
 |(adjEl(a,bs)(x,ys))
   ==(reverse(adjEl(x,ys)(a,bs)))     = True
 |otherwise                           = False

-- vertex -> list of stars -> stars with vertex
nstars::Int->[Star]->[Star]
nstars _ [] = []
nstars x starlist@(y:ys) 
 |x==fst y  = [y]++nstars x ys 
 |otherwise = nstars x ys

-- star list -> orientable 2-manifolds
manifolds::[Star]->[[Star]]
manifolds [] = []
manifolds (star:stars)        
 =(extsmani [star] (snd star) stars)++manifolds stars

-- star -> star list -> add star to list when consistent
posStar::Star->[Star]->[Star] 
posStar  star@(a,bs) partialManifold
 |consistentStar star partialManifold=[star]
 |consistentStar(a, reverse bs)partialManifold
                             =[(a,reverse bs)]
 |otherwise =[]

-- extensions of partial 2-manifolds
extsmani::[Star]->[Int]->[Star]->[[Star]] 
extsmani starsSoFar []      _ = [starsSoFar] 
extsmani starsSoFar (n:ns) starlist 
 =concat                        
  (map(\i->extsmani (starsSoFar++[i]) 
       (nub((ns++(snd i))\\[fst y|y<-(starsSoFar++[i])])) 
        starlist )   consnst )
 where 
  nst = nstars n starlist
  consnst = concat(map(\st->posStar st starsSoFar) nst) 

final = man (subfacets facetsA)

-- triangle list -> list of orientable triangulated 2-manifolds
man::[[Int]]->[[Star]] 
man triangles = manifolds(concat(posStars triangles))

-- function for investigating Szilassi's polyhedron
edges::[[Int]]->[[Int]]
edges [] = []
edges (hexagon:hexagons)
 = (edges6gon hexagon)++edges hexagons 

-- function for investigating Szilassi's polyhedron
edges6gon::[Int]->[[Int]]
edges6gon hexagon@[a,b,c,d,e,f] 
 = [[a,b],[b,c],[c,d],[d,e],[e,f],[f,a]]

edgesSzilassi = nub (map sort (edges hexagonsSzilassi))                   
fixEdges      = [edge |edge<-edgesSzilassi, 
                     head edge == symmetry (last edge)]
-- [[2,13],[1,14],[4,11]]

--
pseudoManifoldTest::[[Int]]->Bool
pseudoManifoldTest triangleList 
  =   edgeTest triangleList
   &&(and [twoVertices (concat star)
        | star<-starList])
  where 
  edgeTest::[[Int]]->Bool -- used within pseudoManifoldTest
  edgeTest triangleList 
    = twoEdges (concat (map triangle2Edges 
           triangleList))
    where 
    twoEdges::[[Int]]->Bool
    twoEdges [] = True
    twoEdges list@(x:xs)
      | x `elem` xs && x `notElem` (xs\\[x]) 
        = twoEdges (xs\\[x])
      | otherwise  = False
  triangle2Edges::[Int]->[[Int]]  -- a < b < c
  triangle2Edges [a,b,c] = [[a,b],[b,c],[a,c]]

  starList = [[(triangle\\[vertex]) 
                 |triangle <- triangleList, 
                  vertex `elem` triangle ]
              |vertex<- nub (concat triangleList) ]
  twoVertices::[Int]->Bool
  twoVertices    [] = True
  twoVertices list@(x:xs)
    | x `elem` xs && x `notElem` (xs\\[x]) 
        = twoVertices (xs\\[x])
    | otherwise  = False

-- > pseudoManifoldTest kleinBottle
--  True

-- 
linkGen::Int->[[Int]]->Int->[Int]->[[Int]]
                          ->(Int,[[Int]]) 
linkGen i cyclesSoFar _  cycleSoFar@c  [] 
      = (i,cyclesSoFar++[c])
linkGen i cyclesSoFar@cSF startVertex@v 
        cycleSoFar@c 
        remainingEdgeList@(e:es)
  |last c == v = linkGen i (cSF++[c]) (head e) e es
  |last c == head e   
    = linkGen i cSF v (cycleSoFar++[last e]) es 
  |last c == last e   
    = linkGen i cSF v (cycleSoFar++[head e]) es
  |otherwise          
    = linkGen i cSF v  cycleSoFar     (es++[e])

{-
allLinks::[[Int]]->[(Int,[[Int]])]
allLinks triangleList 
   = [ let star = [(triangle\\[vertex]) 
                   |triangle <- triangleList, 
                    vertex `elem` triangle ] 
       in linkGen vertex [](head (head star))
          (head star)(tail star) 
           vertex <- nub (concat triangleList) ]

-- 
manifoldTest::[[Int]]->Bool
manifoldTest triangleList
  = pseudoManifoldTest triangleList 
     && linkNumberTest triangleList


--
linkNumberTest::[[Int]]->Bool
linkNumberTest triangleList
  = and[length(snd((allLinks triangleList)!!j))==1 
      | j<-[0..(m-1)]]
  where
  m = length (allLinks triangleList) 
-}
-- > manifoldTest kleinBottle
--  True
  
-- start stars for K_12 embeddings on genus 6 surface
sts::[(Int,[[Int]])]               
sts=[(i,(map(\k->[mod((head k)+i)11]))
     ([[10]]++[[j]|j<-[2..9]]++[[1]]))|i<-[0..10]]

-- insert triangle
itr::[Int]->(Int,[[Int]])->(Int,[[Int]]) 
itr [a,b,c](j,gs)|j`notElem`[a,b,c]=(j,gs)
                 |j==a=ins[b,c](j,gs)
                 |j==b=ins[c,a](j,gs)
                 |j==c=ins[a,b](j,gs)

-- extending the star structure
e::[[(Int,[[Int]])]]->[[(Int,[[Int]])]]
e [] = []
e (s:r)                        
 |[]`elem`(map snd)s = e r
 |(map length)((map snd)s)
   ==[1,1,1,1,1,1,1,1,1,1,1] = [s]++(e r)
 |length gst==2=[(map(itr[m,ly,head(lagst)]))s]++(e r) 
 |otherwise 
   = [(map(itr[m,ly,head(gst!!i)]))s|i<-[1..lgst]]++(e r)
  where 
  m  = minimum[i|i<-[0..10], length(snd(s!!i))/=1] 
  gst= snd (s!!m); lgst=(length gst)-2; lagst=last gst
  y  = head gst; ly = last y; ys = tail gst

-- inserting a line segment in a star
ins::[Int]->(Int,[[Int]])->(Int,[[Int]]) 
ins [a,b] (j,gs) 
 |length gs==1 = (j,[])
 |length gs==2&&a==last(head gs)&&b==head(last gs)
  =(j,[new]) 
 |length gs==2 = (j,[]) 
 |a==last(head gs)&&b`elem`(map head)(tail(init gs))
  =(j,[new]++all)
 |a`elem`(map last)(tail(init gs))&&b==head(last gs)
  =(j,all++[new])
 |  a`elem`(map last)(tail(init gs))
  &&b`elem`(map head)(tail(init gs))
   =(j,(fst(splitAt 1 all))++[new]++(snd(splitAt 1 all)))
 |otherwise=(j,[]) 
 where all=[el|el<-gs,el/=beg,el/=end]
       beg=head[el|el<-init gs,last el==a]
       end=head[el|el<-tail gs,head el==b]
       new=beg++end

-- triangle list of Klein bottle
kleinBottle::[[Int]]
kleinBottle
 =[[1,2,7],[1,2,8],[1,3,4],[1,3,5],[1,4,7],[1,5,8],
   [2,3,6],[2,3,9],[2,6,7],[2,8,9],[3,4,6],[3,5,9],
   [4,5,7],[4,5,8],[4,6,8],[5,7,9],[6,7,9],[6,8,9]]

-- all hexagons of Szilassi's torus
hexagonsSzilassi::[[Int]]
hexagonsSzilassi 
 = [[1,  8, 2, 13, 6, 12], [2,  9, 3, 14, 7, 13],
    [3, 10, 4,  8, 1, 14], [4, 11, 5,  9, 2,  8],
    [5, 12, 6, 10, 3,  9], [6, 13, 7, 11, 4, 10],
                           [7, 14, 1, 12, 5, 11]]
