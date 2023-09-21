-----------------------Preface--------------------------
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
--------------------------------------------------------

-- Equality is (for now) defined as follows
data _≡_ {A : Set} (x : A) : A  → Set where
  refl : x ≡ x

_ : 5 ≡ 5
_ = refl
-- Here one parameter and one index comes into play
-- we basically fixate the first x in the type x ≡ x
-- with the argument and create a whole type family
-- via the index. Though, we can only construct x ≡ x
-- for every element x of a set A

-- The equality type also has a type parameter A
-- we can not use two parameters, otherwise everything
-- would be equal to everything but we -can- use two
-- indices as seen below
data _eq_ {A : Set} : A → A → Set where
  refl : ∀ {x : A} → x eq x

_ : 5 eq 5
_ = refl
-- Though, it usually is better to define
-- parameters if possible.

-- Precedence
infix 4 _≡_
--------------------------------------------------------

-- Equality is obviously an equivalence relation and
-- therefore we can show the three properties

≡-refl : ∀ {A : Set} {x : A} → x ≡ x
≡-refl = refl

≡-sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

-- Another nice property that already was used a lot is that
-- quality is satisfying congruence, which is the following law
cong : ∀ {A B : Set} (f : A → B) {x y : A}
    → x ≡ y
    --------
    → f x ≡ f y

cong f refl = refl

-- This also works for multiple arguments
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
      → u ≡ x
      → v ≡ y
      --------
      → f u v ≡ f x y

cong₂ f refl refl = refl

-- It also works in the function position
-- (we inject an argument into the equality, instead of the function)
cong-app : ∀ {A B : Set} (f g : A → B) → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app f .f refl x = refl

-- Equality also has the property of substitution
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  → P x
  --------
  → P y

subst p refl px = px

-- WIP: Chains of equations/reasoning
