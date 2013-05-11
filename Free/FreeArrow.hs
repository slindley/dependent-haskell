{- The free arrow over a bifunctor -}

{- An arrow computation is a sequence of effectful steps, each of
which generates an output value, followed by a pure function that
processes the generated values to output a final return value.

An effectful step comprises a pure function and an effectful body. The
environment is provided as input to the pure function. The
intermediate value returned by the pure function is fed into the
effectful body, which generates the output value.

Each effectful step has access to all of the previously generated
values in the form of the environment.  -}

{-# LANGUAGE DataKinds, RankNTypes, GADTs, TypeOperators, TypeFamilies #-}

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

{- type lists as right-nested products -}
type family Prod (ts :: [*]) :: *
type instance Prod '[]       = ()
type instance Prod (t ': ts) = (t, Prod ts)

{- an effectful step of an arrow computation -}
data Step f (ts :: [*]) b = forall a.Step (Prod ts -> a) (f a b)

{- a list of effectful steps inputting ts and outputting ts' -}
data AList (f :: * -> * -> *) (ts :: [*]) (ts' :: [*]) where
  ANil ::                                         AList f ts '[]
  (:>) :: Step f ts t -> AList f (t ': ts) ts' -> AList f ts (t ': ts')

{- transform the inputs of an arrow list -}
mapA :: (Prod ts2 -> Prod ts1) -> AList f ts1 ts' -> AList f ts2 ts'
mapA g ANil             = ANil
mapA g (Step f b :> cs) = Step (f . g) b :> mapA (second g) cs

{- the free arrow over a bifunctor -}
data Free (f :: * -> * -> *) (a :: *) (b :: *) :: * where
  Free :: AList f (a ': '[]) ts -> (Prod ts -> a -> b) -> Free f a b

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
fcomp (Free ANil p1) (Free ANil p2) = Free ANil (\() -> (p2 () . p1 ()))
fcomp (Free ANil p1) (Free cs p2)   =
  Free (mapA (first (p1 ())) cs) (\xs -> p2 xs . p1 ())
fcomp (Free (c :> cs) p) r =
  fcons c (fcomp (Free (squish cs) (\xs (x, y) -> p (x, xs) y)) r)

{- squish the first two inputs of an arrow list into a single pair -}
squish :: AList f (t ': t' ': ts) ts' -> AList f ((t, t') ': ts) ts'
squish = mapA (\((x, y), xs) -> (x, (y, xs)))

{- cons a step onto a suitably squished free arrow -}
fcons :: Step f (a ': '[]) t -> Free f (t, a) b -> Free f a b
fcons c (Free cs p) =
  Free (c :> mapA (\(x, (y, ())) -> ((x, y), ())) cs)
       (\(x, xs) a -> p xs (x, a))

instance Bifunctor f => Arrow (Free f) where
  arr f = Free ANil (\() -> f)
  first (Free cs p) =
    Free (mapA (\((x, _), ()) -> (x, ())) cs) (\ts -> first (p ts))

{- We might make things simpler (avoid squish and fcons) by building
the final pure computation into ALists or equivalently generalising
the Free datatype to input and output multiple values. -}
