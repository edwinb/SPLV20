data Nat : Type where
     Z : Nat
     S : Nat -> Nat

plus : Nat -> Nat -> Nat
pat y : Nat =>
   plus Z y = y
pat k : Nat, y : Nat =>
   plus (S k) y = S (plus k y)
