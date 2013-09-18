class Monoid a where
    mempty :: a                
    mappend :: a -> a -> a    

data Funcs x = 
    Func (x -> x)

fid = Func (\x -> x)
apply (Func f) a =  f a

instance Monoid (Funcs a) where
    mempty = fid
    mappend (Func x) (Func y) = Func (\z -> (x (y z)))

