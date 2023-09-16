module FunctionsConfigurations where


-- preliminary points, input for a 40_4 configuration
prepts::[[Int]] 
prepts =[[a,b,c,d]|a<-s,b<-s,c<-s,d<-s,
         [a,b,c,d]/=[0,0,0,0]] where s = [-1,0,1] 

-- reduction of preliminary points of 40_4 configuration
reduce::[[Int]]->[[Int]]
reduce [] = []
reduce ([a,b,c,d]:xs) 
 | [-a,-b,-c,-d]`elem` xs = reduce xs
 | otherwise              = [[a,b,c,d]]++reduce xs

pts = reduce prepts

-- an abstract product funcion, for point line configurations
prod::[Int]->[Int]->Int
prod [a1,b1,c1,d1] [a2,b2,c2,d2] 
      = a1*b2 - b1*a2 + c1*d2 - d1*c2

-- line condition for point pairs in a 40_4 configuration
on_ln::[Int]->[Int]->Bool 
on_ln  p1 p2 =  (prod p1 p2 ==  0)
              ||(prod p1 p2 ==  3)
              ||(prod p1 p2 == -3)   

-- lines of 40_4 configuration
lns::[[Int]]
lns = [[i,j,k,l]|i<-[0..36],     j <- [(i+1)..37],
                 k<-[(j+1)..38], l <- [(k+1)..39],
           on_ln(pts!!i)(pts!!j),on_ln(pts!!i)(pts!!k),
           on_ln(pts!!i)(pts!!l),on_ln(pts!!j)(pts!!k),
           on_ln(pts!!j)(pts!!l),on_ln(pts!!k)(pts!!l)]

-- curve arrangement with 4 elements
e_4::[(Int,[Int])]
e_4=[(1,[ 2, 3, 4]),(2,[-1, 3, 4]),(3,[-1,-2, 4]),(4,[-1,-2,-3])]
