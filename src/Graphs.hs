module FirstProofs where

import List 

type GR =(Vs,Es)                -- graph 
type Vs = [Int]                 -- vertices
type Es =[[Int]]                -- edges 
type OE =(Vs,Int)               -- oriented edge

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

-- n -> complete graph with n vertices 
graphComplete::Int->([Int],[[Int]])
graphComplete n = ([1..n],tuples 2 n)

-- Petersen graph (an oriented version)
graphP::GR
graphP=([0..9], [ [a, ((a+1)`mod`5) ]   | a<-[0..4] ]
              ++[ [a, a+5 ]             | a<-[0..4] ]
              ++[ [5+a, 5+((a+2)`mod`5)]| a<-[0..4] ])

-- graph -> circuits of graph
gr2C::GR->[[OE]]
gr2C (_,[]) = []
gr2C graph@(vs,(e:es))=(cEdge e graph)++gr2C(vs,es) 


-- [z,a] -> graph -> circuits with edge ([z,a],1)
cEdge::[Int]->GR->[[OE]] 
cEdge e@[z,a](vs,es)=map([(e,1)]++)(paths a z[](vs,es\\[e]))

-- i -> z -> path -> graph -> [path & path from i to z
paths::Int->Int->[OE]->GR->[[OE]] 
paths   i    z   path  (vs,es) 
 =concat (map (\(edge,or)-> 
 (if  z `elem` edge  then   [path++[(edge,or)]] else 
 paths(head(edge\\[i]))z(path++[(edge,or)])(vs,es\\[edge]))) 
 orEdges)  
 where 
 fV = if path==[] then [] else tail (concat (map fst path)) 
 orEdges =   [([u,v], 1)|[u,v]<-es, u==i, v`notElem`fV ]    
          ++ [([u,v],-1)|[u,v]<-es, v==i, u`notElem`fV ] 


-- oriented edges -> graph -> list of signs of edges
signVector::[OE]->GR->[Char] 
signVector    c   (vs,es) 
 =map(\e->(if(e,1)`elem`c then '+' 
                          else(if(e,-1)`elem`c then '-' 
                                               else '0')))es
{-
-- graph -> number of components of graph
nOfComp::GR->Int
nOfComp ([],_) = 0
nOfComp  graph@(vs,es) 
 |length vs== 1 = 1
 |otherwise=1+nOfComp(vs2gr(vComp[head vs]graph)graph)

-- vertices  -> graph -> subgraph without vertices
vs2gr::[Int]->GR->GR
vs2gr vts (vs,es)=(vs\\vts,[e|e<-es,e\\vts==e])

-- vertices -> graph -> vertices of same component
vComp::[Int]->GR->[Int]
vComp vts (vs,es) | nvts==vts = vts 
                  | otherwise = vComp nvts (vs,es)
 where 
 nvts=nub(vts++concat[e\\[v]|v<-vts,e<-es,v`elem`e])

-- edges -> graph -> subgraph without edges
es2gr::[[Int]]->GR->GR 
es2gr eds (vs,es)=(vs,es\\eds)

-- k -> remaining number of components (Petersen graph)
r::Int->[Int]
r k= map nOfComp (map(\es->es2gr es graphP)
     [[elist!!(i-1)| i<-t]| t<-tuples k 15])
              where elist = snd graphP

-- function for Petersen graph investigation
res::Int->[[Int]]
res 2 = []
res k =(res (k-1))
       ++[fst el|el<-(zip (tuples k 15) (r k)), snd el >1, 
           and[not (isSubSet e (fst el))|e<-res (k-1)]]

-- function for Petersen graph investigation
ts::[[Int]]
ts=res3++res4++res5++res6++res7

-- function for Petersen graph investigation
t2gr::[Int]->GR->GR 
t2gr t (vs,es)=(vs,[es!!(i-1)|i<-[1..length es],
                              i`notElem`t       ])

-- function for Petersen graph investigation
ns::[Int]
ns = map nOfComp (map (\t->t2gr t graphP) ts)

-- cocircuit result, function for Petersen graph investigation
cs::[[Int]]
cs = map (vComp [1]) (map (\t->delEdges t graphP) ts)

-- string of characters for cocircuit result
resultCocircuits::[[Char]]                         
resultCocircuits  
 =map(\(t,c)->(map(\i->(if i`notElem`t 
                        then '0' 
                        else 
                        (if head((snd graphP)!!(i-1))`elem`c 
                         then '+' 
                         else '-'))) 
                   [1..15])) 
  (zip ts cs)

-- circuit -> cocircuit -> orthogonal property 
prod::[Char]->[Char]->Int
prod   []  []   = 0
prod  (c:cs) (coc:cocs)
 | c=='0'||coc=='0'                     = 0+(prod cs cocs)
 |(c=='+'&&coc=='+')||(c=='-'&&coc=='-')= 1+(prod cs cocs)   
 |(c=='+'&&coc=='-')||(c=='-'&&coc=='+')=-1+(prod cs cocs)   

-- test=[prod c coc| c<-resultCircuits, coc<-resultCocircuits]

-- vertex 1 -> vertex 2 -> graph -> (path,True) or (cut,False)
lFarkas::Int->Int->GR->(Es,Bool)
lFarkas  u v graph
 |u==v      = ([],True)
 |otherwise = pathCut u v [u] graph

-- part of proof of Farkas's lemma for graphs
pathCut::Int->Int->[Int]->GR->(Es,Bool)
pathCut vStart vFinal reachVs graph@(vs,es)
 |newEs == []         = ( cutEs,False)  
 |vFinal `elem` newVs = (pathEs,True ) 
 |otherwise = pathCut vStart vFinal (reachVs++newVs) graph
 where 
 complVs=vs\\reachVs 
 cutEs  =[[a,b]|[a,b]<-es, b`elem`reachVs, a`elem`complVs] 
 newEs  =[[a,b]|[a,b]<-es, a`elem`reachVs, b`elem`complVs]  
 newVs  =nub(map last newEs)
 finE   =head[[a,b]|[a,b]<-es, a`elem`reachVs, b==vFinal]
 pathEs =(fst(lFarkas vStart (head finE) graph))++[finE] 

-}

