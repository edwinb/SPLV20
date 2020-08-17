import Decidable.Equality

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  -- ...

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following 
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)

-- 3. (Optional, since we don't need this in Idris 2, but it's a good
-- exercise to see if you can do it!) Implement decidable equality, so you
-- also have a proof if names are *not* equal.
DecEq Name where
  decEq x y = ?decEq_rhs
