module ranta where

data P : Set where
  p : P

data Q : Set where
  q : Q

--
--


-- Define a conjunction type as a parameterized datatype with its type construction xI. The data declaration is what Ranta called the Formation Rule xF. Given two types return (A & B) as a type. Here we have the introduction rule. &I takes something of type A and B and returns something of the &-type.

data _&_ (A B : Set) : Set where
  &I : A → B → (A & B)

-- Now define elimination rules for conjunction, which are just projection. That is, elements of type (A & B) are pairs (a,b) of a proof of A and a proof of B.
&EL : {A B : Set} → (A & B) → A
&EL (&I a b) = a

&ER : {A B : Set} → (A & B) → B
&ER (&I a b) = b

-- Define sum types (Σ-types) as a generalization of conjunction. When B is a constant function (Σ A B) = (A & B). Note Σ-types behave like existential quantification. They denote the set of "A such that B", that is, the set of A such that there is a proof of (B a) for each 'a'.

data Σ (A : Set) (B : A → Set) : Set where
  ΣI : (a : A) → (b : B a) → Σ A B

ΣEL : {A : Set} → {B : A → Set} → (Σ A B) → A
ΣEL (ΣI a b) = a

ΣER : {A : Set} → {B : A → Set} → (p : Σ A B) → B (ΣEL p)
ΣER (ΣI a b) = b

--Just as Σ-types are a generalization of conjunction corresponding to existential quantification, product types (Π-types) generalize implication and correspond to universal quantification.

data _⊃_ (A : Set) (B : Set) : Set where
  ⊃I : A → B → A ⊃ B

⊃E : {A B : Set} → (A ⊃ B) → A → B
⊃E (⊃I a b) a′ = b

data Π (A : Set) (B : A → Set) : Set where
  ΠI : (a : A) → (b : B a) → Π A B

