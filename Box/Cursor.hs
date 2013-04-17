{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, LiberalTypeSynonyms, ImpredicativeTypes #-}

module Cursor where

import Box
import CharBox

type Cursor a m l r = (Vec l a, m, Vec r a)
type StringCursor l r = Cursor Char () l r

-- a cursor in a text buffer with bounded width w, where d = w - (l +
-- r + 1), i.e., d is the difference between the bound and the length
-- of the current line
type BTextCursor d l r t b = (Natty d, Cursor (BString ((l :+ r) :+ S d)) (StringCursor l r) t b)

--- sum lemmas ---
sumShift :: forall x y t.Natty x -> Natty y -> ((x :+ S y) ~ (S x :+ y) => t) -> t
sumShift Zy     _ t = t
sumShift (Sy x) y t = sumShift x y t

-- assocLR :: forall a b c t.Natty a -> Natty b -> Natty c -> (((a :+ b) :+ c) ~ (a :+ (b :+ c)) => t) -> t
-- assocLR Zy b c t = t
-- assocLR (Sy a) b c t = assocLR a b c t

sumIdR :: forall x t.Natty x -> ((x ~ (x :+ Z)) => t) -> t
sumIdR Zy     t = t
sumIdR (Sy x) t = sumIdR x t
------------------

cursorPos (xz, _, xs) = (vlength xz, vlength xs)

deactivate :: Cursor a () l r -> Vec (l :+ r) a
deactivate c = outward c where
  outward :: forall a l r.Cursor a () l r -> Vec (l :+ r) a
  outward (V0, (), xs)      = xs
  outward (x :> xz, (), xs) = sumShift (vlength xz) (vlength xs) (outward (xz, (), x :> xs))


activate :: Natty l -> Vec (l :+ r) a -> Cursor a () l r
activate n xs = inward Zy n (V0, (), xs) where
  inward :: forall l r n a.Natty l -> Natty n -> Cursor a () l (n :+ r) -> Cursor a () (l :+ n) r
  inward l Zy     c                 = sumIdR l c
  inward l (Sy n) (xz, (), x :> xs) = sumShift l n (inward (Sy l) n (x :> xz, (), xs))

activate' :: Vec n a -> Cursor a () n Z
activate' xs = sumIdR n (activate n xs) where n = vlength xs

vreverse :: Vec n a -> Vec n a
vreverse xs = xz where (xz, _, _) = activate' xs

-- this version might be useful...
--
-- activate'' :: Natty n -> Vec m a -> Cursor a () (Min m n) (m :- n)



whatAndWhere :: BTextCursor d l r t b -> (CharBox '((l :+ r) :+ S d, t :+ S b), Point l (S t))
whatAndWhere (d, (czz, cur@(cz, (), cs), css)) = (boxOfBStrings strs, (l, Sy (vlength czz)))
  where
    l = vlength cz
    r = vlength cs
    cs' = boundCharVec (Sy d) (deactivate cur)
    strs = deactivate (czz, (), cs' :> css)
