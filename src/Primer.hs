module FunctionsPrimer where

-- Haskell primer function
pythtriple::Integer->[[Integer]]
pythtriple n = [[a,b,c]|a<-s,b<-s,c<-s, a*a+b*b==c*c]
               where s = [1..n]

-- Haskell primer function
fak:: Integer->Integer
fak 0 = 1
fak n = n * (fak (n-1))

-- Haskell primer function
tup::Int->[Int]->[[Int]]
tup r l
 |r == 1      = [[el]|el<-l] 
 |length l==r = [l]
 |True=(map([head l]++)(tup(r-1)(tail l)))++tup r(tail l)

-- Haskell primer function
qsort::[Int]->[Int]
qsort [] = []
qsort (x:xs) = (qsort smaller)++[x]++(qsort greater)
             where
             smaller = [el|el<-xs, el<x]
             greater = [el|el<-xs, el>x]

-- Haskell primer function
fib::Int->Int
fib 0 = 0
fib 1 = 1
fib n = fib(n-1) + fib(n-2)

