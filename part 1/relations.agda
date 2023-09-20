import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-identityʳ)

-- A relation can be defined inductively by an indexed datatype
-- Parameters with {} are implicit parameters

-- Here we define a whole family of types m ≤ n where
-- m and n are two arbitrary naturals. Meaning, we even
-- define something like 10 ≤ 5. This is good, because
-- we can limit the types that are actually inhabited by
-- a value by defining the constructors in a correct way
-- giving us a good formalization
data _≤_ : ℕ → ℕ → Set where

 z≤n : ∀ {n : ℕ}
     ---------
   → zero ≤ n

 s≤s : ∀ {m n : ℕ}
   → m ≤ n
   --------------
   → suc m ≤ suc n

-- Implicit arguments can be ommitted or stated in different ways
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)


-- Precedence
infix 4 _≤_

-- The ≤ relation is reflexive, transitive and anti-symmetric, we will show this:

-- Reflexive
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitive
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Anti-symmatric
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- The reason why there is no case for one argument being z≤n
-- and one being s≤s is, that it would imply that m has to be
-- both zero and the suc of a natural which is clearly not possible

-- Not, since we do not have connectives yet, we can show that the
-- relation is total by a nice trick. That being, we encapsule the
-- fact of totality into a new type (Total m n) whose constructors
-- make sure that either m ≤ n or n ≤ m holds. We can use parameters
-- here instead of indices because m and n are fixed

data Total (m n : ℕ) : Set where
  forward :
          m ≤ n
          --------
        → Total m n

  flipped :
          n ≤ m
          --------
        → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward (m≤n) = forward (s≤s m≤n)
...                        | flipped (n≤m) = flipped (s≤s n≤m)


-- Monotonicity for addition

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


-- Similarly to how monotonocity for addition and the relation is defined,
-- we can define it for multiplication

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * p
*-mono-≤ .0 n p q z≤n p≤q = z≤n
*-mono-≤ (suc m) (suc n) p q (s≤s m≤n) p≤q = +-mono-≤ p p (m * p) (n * p) (≤-refl) (*-mono-≤ m n p q m≤n p≤q)


-- We can also define a strict inequality similar to ≤
data _<_ : ℕ → ℕ → Set where
  z≤s : ∀ {n : ℕ} →
      -----------
      zero < suc n

  s<s : ∀ {m n : ℕ} →
      m < n
      ----------------
    → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z≤s (s<s n<p) = z≤s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)


data Tricho (m n : ℕ) : Set where
  forward : m < n → Tricho m n
  flipped : n < m → Tricho m n
  same    : m ≡ n → Tricho m n


<-tricho : ∀ (m n : ℕ) → Tricho m n
<-tricho zero zero = same refl
<-tricho zero (suc n) = forward z≤s
<-tricho (suc m) zero = flipped z≤s
<-tricho (suc m) (suc n) with <-tricho m n
...                         | forward m<n = forward (s<s m<n)
...                         | flipped n<m = flipped (s<s n<m)
...                         | same n≡m = same (cong suc n≡m)


--WIP MONO FOR <
----------------


≤→< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤→< zero .(suc _) (s≤s sm≤n) = z≤s
≤→< (suc m) (suc n) (s≤s sm≤n) = s<s (≤→< m n sm≤n)

<→≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<→≤ .0 .(suc _) z≤s = s≤s z≤n
<→≤ (suc m) (suc n) (s<s m<n) = s≤s (<→≤ m n m<n)

≤-suc : ∀ (n : ℕ) → n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p m<n n<p = ≤→< m p (≤-trans (<→≤ m n m<n) (≤-trans (≤-suc n) (<→≤ n p n<p)))
