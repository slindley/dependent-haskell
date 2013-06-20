{- Free arrow over a bifunctor -}

{- An arrow computation is a sequence of effectful steps, each of
which generates an output value, followed by a pure function that
processes the generated values to output a final return value.

An effectful step comprises a pure function and an effectful body. The
environment is provided as input to the pure function. The
intermediate value returned by the pure function is fed into the
effectful body, which generates the output value.

Each effectful step has access to all of the previously generated
values in the form of the environment.  -}

{-# LANGUAGE
    DataKinds,
    GADTs, TypeOperators, TypeFamilies,
    UndecidableInstances
  #-}

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

{- type list concatenation -}
type family (ts :: [*]) :++: (ts' :: [*]) :: [*]
type instance '[]       :++: ts' = ts'
type instance (t ': ts) :++: ts' = t ': (ts :++: ts')

{- reverse type list concatenation -}
type family (ts :: [*])  :>++<: (ts' :: [*]) :: [*]
type instance  '[]       :>++<: ts' = ts'
type instance  (t ': ts) :>++<: ts' = ts :>++<: (t ': ts')

{- type lists as right-nested products -}
type family RProd (ts :: [*]) :: *
type instance RProd '[]       = ()
type instance RProd (t ': ts) = (t, RProd ts)

{- type lists as left-nested products -}
type family LProd (ts :: [*]) :: *
type instance LProd '[]       = ()
type instance LProd (t ': ts) = (LProd ts, t)

{- an effectful step of an arrow computation -}
data Step f (ts :: [*]) b where
  Step :: (RProd ts -> a) -> f a b -> Step f ts b

{-
  a list of effectful steps inputting ts and outputting ts'

      AList f ts [b1,...,bn] ==
        [               (ts -> a1, f a1 b1),
                  ((b1, ts) -> a2, f a2 b2),
                                   ...     ,
         ((bn, ..., b1, ts) -> an, f an bn)]
-}
data AList (f :: * -> * -> *) (ts :: [*]) (ts' :: [*]) where
  ANil ::                                         AList f ts '[]
  (:>) :: Step f ts t -> AList f (t ': ts) ts' -> AList f ts (t ': ts')

{- arrow list concatenation -}
(/++/) :: AList f ts0 ts' ->
             AList f (ts' :>++<: ts0) ts'' ->
                AList f ts0 (ts' :++: ts'')
ANil      /++/ ds = ds
(c :> cs) /++/ ds = c :> (cs /++/ ds)

{- transform the inputs of an arrow list -}
mapA :: (RProd ts2 -> RProd ts1) -> AList f ts1 ts' -> AList f ts2 ts'
mapA g ANil             = ANil
mapA g (Step f b :> cs) = Step (f . g) b :> mapA (second g) cs

{- the free arrow over a bifunctor -}
data Free (f :: * -> * -> *) (a :: *) (b :: *) :: * where
  Free :: AList f (a ': '[]) ts -> (RProd ts -> a -> b) -> Free f a b

{- bifunctors -}
class Bifunctor p where
  bimap :: (b -> a) -> (c -> d) -> p a c -> p b d

newtype BiId a b = BiId (a -> b)
instance Bifunctor BiId where
  bimap f g (BiId h) = BiId (g . h . f)

instance Bifunctor f => Bifunctor (Free f) where
  bimap f g (Free ANil p) = Free ANil (\() -> g . p () . f)

instance Bifunctor f => Category (Free f) where
  id  = Free ANil (\() -> id)
  (.) = flip fcomp

{- left to right composition of free arrows -}
fcomp :: Free f a b -> Free f b c -> Free f a c
fcomp (Free cs1 p1) (Free cs2 p2) =
  let (ts1, ts2) = (shape cs1, shape cs2) in
  let a = freeIn (Free cs1 p1) in
    Free (cs1 /++/ mapA (\xs -> (p1 (fstRev ts1 (TCons a TNil) xs)
                                    (fst (sndRev ts1 (TCons a TNil) xs)), ()))
                        cs2)
         (\ xs -> let (xs1, xs2) = split ts1 ts2 xs in
                    p2 xs2 . p1 xs1)

{- chopping up tuples
 
The second argument is computationally redundant, but required in
order to satisfy the type-checker. It wouldn't be necessary if we used
a suitable GADT in place of the type class RProd. -}
split :: TList ts -> TList ts' ->
           RProd (ts :++: ts') -> (RProd ts, RProd ts')
split TNil         _   xs      = ((), xs)
split (TCons t ts) ts' (x, xs) = ((x, ys), zs) where
  (ys, zs) = split ts ts' xs

sndRev :: TList ts -> TList ts' -> RProd (ts :>++<: ts') -> RProd ts'
sndRev TNil         _   l = l
sndRev (TCons t ts) ts' l = snd (sndRev ts (TCons t ts') l)

fstRev' :: TList ts -> TList ts' -> RProd (ts :>++<: ts') -> LProd ts
fstRev' TNil         _   l = ()
fstRev' (TCons t ts) ts' l =
  (fstRev' ts (TCons t ts') l, fst (sndRev ts (TCons t ts') l))

revrev :: TList ts -> LProd ts -> RProd ts
revrev TNil         l = ()
revrev (TCons t ts) l = (snd l, revrev ts (fst l))

fstRev :: TList ts -> TList ts' -> RProd (ts :>++<: ts') -> RProd ts
fstRev ts ts' l  = revrev ts (fstRev' ts ts' l) 

{-- proxy stuff --}

data Proxy (t :: *) = Proxy
{- list of type proxies -}
data TList (ts :: [*]) where
  TNil :: TList '[]
  TCons :: Proxy t -> TList ts -> TList (t ': ts)

{- shape of an AList -}
shape :: AList f ts ts' -> TList ts'
shape ANil = TNil
shape (c :> cs) = TCons Proxy (shape cs)

{- input type for an arrow -}
freeIn :: Free f a b -> Proxy a
freeIn _ = Proxy

{- output type for an arrow -}
freeOut :: Free f a b -> Proxy b
freeOut _ = Proxy
