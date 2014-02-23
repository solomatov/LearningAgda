module LearningAgda where

data Bool : Set where
  true : Bool
  false : Bool

bool-elim : (P : Bool → Set) → (P true) → (P false) → (b : Bool) → P b
bool-elim P Pt Pf true = Pt
bool-elim P Pt Pf false = Pf

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

nat-elim : (P : Nat → Set) → (P zero) → ((n : Nat) → (P n) → (P (suc n))) → (n : Nat) → P n
nat-elim P base step zero = base
nat-elim P base step (suc n) = step n (nat-elim P base step n)

data I (A : Set) :  A → A → Set where
  refl : (a : A) → I A a a

J : (A : Set) → (a b : A) → 
    (M : (x : A) → (y : A) → (I A x y) → Set) → 
    (p : I A a b) → (c : (M a a (refl a))) → 
    (M a b p)
J A .a .a C (refl a) c = c

data True : Set where
  tt : True

data False : Set where
  
abort : (M : Set) → False → M
abort M ()

not : (A : Set) → Set
not A = (A → False)

data _and_ (A B : Set) : Set where
  pair : A → B → A and B

and-elim : (A B : Set) → (M : A and B → Set) → ((a : A) → (b : B) → M (pair a b)) → (a-and-b : A and B) → M a-and-b
and-elim A B M f (pair a b) = f a b

first : (A B : Set) → (A and B) → A 
first A B a-and-b = and-elim A B (λ _ → A) (λ a b → a) a-and-b

second : (A B : Set) → (A and B) → B 
second A B a-and-b = and-elim A B (λ _ → B) (λ a b → b) a-and-b

data _or_ (A B : Set) : Set where
  inl : A → A or B
  inr : B → A or B

or-elim : (A B : Set) → (M : A or B → Set) → ((a : A) → (M (inl a))) → ((b : B) → (M (inr b))) → (a-or-b : A or B) → M a-or-b
or-elim A B P a-case b-case (inl a) = a-case a
or-elim A B P a-case b-case (inr b) = b-case b

data Exists (A : Set) (P : A → Set) :  Set where
  ex : (a : A) → (P a) → Exists A P

ex-elim : (A : Set) → (P : A → Set) → (M : Exists A P → Set) → (f : (a : A) → (p : (P a)) → M (ex a p)) → (ex-a-P : Exists A P) → M ex-a-P
ex-elim A P M f (ex a pa) = f a pa 

-- Part 1. Equality properties

-- Excercise 1.1 (Leibniz equality)
cong : (A : Set) → (P : A → Set) → (a b : A) → (I A a b) → P a → P b
cong A P a b eq Pa = J A a b (λ x y r → P y ) eq Pa

-- Excercise 1.2 (eq reflexivity)
I-refl : (A : Set) → (a : A) → I A a a
I-refl A a = refl a

-- Excercise 1.3 (eq symmetry)
I-symm : (A : Set) → (a b : A) → (I A a b) → (I A b a)
I-symm A a b r = J A a b (λ x y r → I A y x) r (refl a)

-- Excercise 1.4 (eq transitivity)
I-trans : (A : Set) → (a b c : A) → (I A a b) → (I A b c) → (I A a c)
I-trans A a b c a=b b=c = J A b a (λ x y r → I A y c) (I-symm A a b a=b) b=c

-- Part 2. Equality usages

-- Excercise 2.1
bool-true-or-false : (b : Bool) → (I Bool b true) or (I Bool b false)
bool-true-or-false = bool-elim (λ b → (I Bool b true) or (I Bool b false)) (inl (refl true)) ((inr (refl false)))

-- Excercise 2.2
nat-zero-or-succ : (n : Nat) → (I Nat n zero) or (Exists Nat (λ m → I Nat n (suc m)))
nat-zero-or-succ = nat-elim 
  (λ n → (I Nat n zero) or (Exists Nat (λ m → I Nat n (suc m))))
  (inl (refl zero))
  (λ n H → 
    or-elim (I Nat n zero) (Exists Nat (λ m → I Nat n (suc m))) 
      ((λ _ → I Nat (suc n) zero or Exists Nat (λ m → I Nat (suc n) (suc m)))) 
      (λ n=0 → inr (ex zero (J Nat n zero (λ x y _ → I Nat (suc x) (suc y)) n=0 (refl (suc n)))) ) 
      (λ exNat → inr (ex-elim Nat (λ m → I Nat n (suc m)) (λ _ → Exists Nat (λ m → I Nat (suc n) (suc m)))
        (λ m n=suc-m → ex (suc m) (J Nat n (suc m) (λ x y _ → (I Nat (suc x) (suc y))) n=suc-m (refl (suc n))))
        exNat  
     )) 
     H)

-- Excercise 2.3 
minus-one : (n : Nat) → not (I Nat zero n) → Nat
minus-one = (nat-elim (λ n → not (I Nat zero n) → Nat) (λ nonZero → abort Nat (nonZero (refl zero))) (λ n _ _ → n))
