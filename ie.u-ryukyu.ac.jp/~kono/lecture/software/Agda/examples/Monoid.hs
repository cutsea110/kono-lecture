
-- Monoid Monad
--
--   Functor T
--    T(A)  =def M x A                T(A) = {(m,a)| m ∈ M, a ∈ A}
--   f:A->A'  ->  f':(M,A)->(M',A')
--class Functor t where
--    fmap :: (a->b) -> t a -> t b

class Monad1 t where
    eta :: a -> t a
    mu ::  t ( t a ) -> t a


data T1 m a = T [m] a
   deriving (Show)

instance Functor (T1 m) where
    fmap f (T m a)  = T  m (f a)

-- natural transformations
--    η(A) : A -> M x A               η(a) = (1,a)
--    μ(A) : M x (M x A) -> M x A     μ((m,(m',a))) = (m*m',a)

instance Monad1 (T1 a) where
    eta a          = T [] a
    mu  (T m (T m' a)) =  T (m ++ m') a

instance Monad (T1 a) where
    return a = eta a
    (>>=)   = \t f -> mu (fmap f t)

fact 0 = 1
fact n = 
    let m = fact (n - 1) in
       n * m

fact1 0 = T [] 1
fact1 n = fact1 (n -1) >>= \m ->
    T [n] (n * m )

fact2 0 = return 1
fact2 n = do 
    c <- fact2 (n -1)
    T [n] (n * c)

returnWithLog n  value = T [n] value

fact3 0 = return 1
fact3 n = do 
    c <- fact3 (n -1)
    returnWithLog n (n * c)

