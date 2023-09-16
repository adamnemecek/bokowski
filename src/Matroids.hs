module FunctionsMatroid where 

import List

type OM2=[[Int]]                -- rank2 oriented matroid

-- potential bases of a matroid -> is it a matroid?
isM::[[Int]]->Bool                     
isM b
 =and[or[s(u(xs\\[x])[y])`elem`b|y<-ys]|xs<-b,ys<-b,x<-xs]
      where s = sort; u = union  -- library functions

-- rank 3 hyperlines -> underlying matroid
hyp2Matroid::[([Int],OM2)]->[[Int]] 
hyp2Matroid [] = []
hyp2Matroid   (h:rest) 
  = sort (nub ([ sort [abs a, abs b, abs c] 
      |a <- fst h, 
       i <- [1..((length(snd h))-1)],
       b <- ((snd h)!!(i-1)), 
       j <- [(i+1)..(length(snd h))], 
       c <- ((snd h)!!(j-1))]++hyp2Matroid rest))

