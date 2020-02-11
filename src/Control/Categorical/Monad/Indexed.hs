{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
module Control.Categorical.Monad.Indexed (Monad (..), (<=<), (>=>), Comonad (..), (=<=), (=>=)) where

import Data.Function (flip)

import Control.Categorical.Functor
import Control.Category.Dual

infixr 1 >=>, <=<, =>=, =<=

class (∀ i j . Endofunctor s (m i j)) => Monad s m where
    unit :: a `s` m k k a

    join :: m i j (m j k a) `s` m i k a
    join = bind id

    bind :: a `s` m j k b -> m i j a `s` m i k b
    bind f = join . map f

(<=<) :: Monad s m => b `s` m j k c -> a `s` m i j b -> a `s` m i k c
f <=< g = bind f . bind g . unit

(>=>) :: Monad s m => a `s` m i j b -> b `s` m j k c -> a `s` m i k c
(>=>) = flip (<=<)

instance Comonad s f => Monad (Dual s) f where
    unit = Dual counit
    join = Dual cut

instance (Category s, Comonad (NT s) f) => Monad (NT (Dual s)) f where
    unit = NT (Dual (nt counit))
    join = NT (Dual (nt cut))

class (∀ i j . Endofunctor s (ɯ i j)) => Comonad s ɯ where
    counit :: ɯ k k a `s` a

    cut :: ɯ i k a `s` ɯ i j (ɯ j k a)
    cut = cobind id

    cobind :: ɯ j k a `s` b -> ɯ i k a `s` ɯ i j b
    cobind f = map f . cut

(=<=) :: Comonad s ɯ => ɯ i j b `s` c -> ɯ j k a `s` b -> ɯ i k a `s` c
f =<= g = counit . cobind f . cobind g

(=>=) :: Comonad s ɯ => ɯ j k a `s` b -> ɯ i j b `s` c -> ɯ i k a `s` c
(=>=) = flip (=<=)
