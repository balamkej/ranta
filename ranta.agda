module ranta where

data P : Set where
  p : P

data Q : Set where
  q : Q

--
--


-- Define a product type as a parameterized datatype with its type construction xI. The data declaration is what Ranta called the Formation Rule xF. Given two types return A●B as a type. Here we have the introduction rule. ●I takes something of type A and B and returns something of the ●-type.
data _●_ (A B : Set) : Set where
  ●I : A → B → (A ● B)


-- Now define projection, aka. elimination rules for cartesian product.
●EL : {A B : Set} → (A ● B) → A
●EL (●I a b) = a

●ER : {A B : Set} → (A ● B) → B
●ER (●I a b) = b

-- Define sum types as a generalization of the cartesian product.
data Σ (A : Set) (B : A → Set) : Set where
  ΣI : (a : A) → B a → Σ A B

ΣEL : {A : Set} → {B : A → Set} → (Σ A B) → A
ΣEL (ΣI a B) = a

ΣER : {A : Set} → {B : A → Set} → (p : Σ A B) → B (ΣEL p)
ΣER (ΣI a B) = B

--Recover 
