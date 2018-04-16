module ranta where

data P : Set where
  p : P

data Q : Set where
  q : Q

--
--


-- Define a product type as a parameterized datatype with its type construction xI
data _x_ (A : Set) (B : Set) : Set where    --This is what Ranta called the Formation Rule xF
  xI : A → B → (A x B)                      -- Here we have the introduction rule


-- Now define projection, aka. elimination rules for cartesian product.
π₁ : {A B : Set} → (A x B) → A
π₁ (xI a b) = a

π₂ : {A B : Set} → (A x B) → B
π₂ (xI a b) = b


