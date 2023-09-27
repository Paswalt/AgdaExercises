import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
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
  z<s : ∀ {n : ℕ} →
      -----------
      zero < suc n

  s<s : ∀ {m n : ℕ} →
      m < n
      ----------------
    → suc m < suc n

infix 4 _<_

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)


data Tricho (m n : ℕ) : Set where
  forward : m < n → Tricho m n
  flipped : n < m → Tricho m n
  same    : m ≡ n → Tricho m n


<-tricho : ∀ (m n : ℕ) → Tricho m n
<-tricho zero zero = same refl
<-tricho zero (suc n) = forward z<s
<-tricho (suc m) zero = flipped z<s
<-tricho (suc m) (suc n) with <-tricho m n
...                         | forward m<n = forward (s<s m<n)
...                         | flipped n<m = flipped (s<s n<m)
...                         | same n≡m = same (cong suc n≡m)



-----Mono with <-----------
+-monor-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monor-< zero p q p<q = p<q
+-monor-< (suc n) p q p<q = s<s (+-monor-< n p q p<q)

+-monol-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monol-< m n zero m<n rewrite +-comm m zero | +-comm n zero = m<n
+-monol-< m n (suc p) m<n rewrite +-comm m (suc p) | +-comm n (suc p) = +-monor-< (suc p) m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monol-< m n p m<n) (+-monor-< n p q p<q)

≤→< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤→< zero .(suc _) (s≤s sm≤n) = z<s
≤→< (suc m) (suc n) (s≤s sm≤n) = s<s (≤→< m n sm≤n)

<→≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<→≤ .0 .(suc _) z<s = s≤s z≤n
<→≤ (suc m) (suc n) (s<s m<n) = s≤s (<→≤ m n m<n)

≤-suc : ∀ (n : ℕ) → n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p m<n n<p = ≤→< m p (≤-trans (<→≤ m n m<n) (≤-trans (≤-suc n) (<→≤ n p n<p)))

-- We can also model unary predicates with the help of relations
-- we have to declare them in advance because this is our first
-- occurence of mutually recursive types!
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
-- We also have overloaded constructors here, for example suc can either mean
-- the ℕ → ℕ constructor, the even or the odd one. Agda does not allow
-- overloading of defined names, but does allow overloading of constructors.
-- zero is now also overloaded as natural and constructor for even



-- Corresponding to the mutually recursive types, we use two mutually
-- recursive functions, one to show that the sum of two even numbers
-- is even, and the other to show that the sum of an odd and an even
-- number is odd
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {suc m} {suc n} (suc em) (suc en) rewrite +-comm m (suc n) = suc (suc (e+e≡e en em))

----------------------------------Stretch exercise-----------------------------------------
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 0 + 2 * (from x)
from (x I) = 1 + 2 * (from x)

shift : ∀ (b : Bin) → (from b) + (from b) ≡ (from (b O))
shift ⟨⟩ = refl
shift (b O) rewrite +-comm (from b + (from b + zero)) zero = refl
shift (b I) rewrite +-comm (suc (from b + (from b + 0))) zero = refl

-- We can now define the predicates
data One : Bin → Set where
  singleI : One (⟨⟩ I)
  oneO : ∀ (b : Bin) → One b → One (b O)
  oneI : ∀ (b : Bin) → One b → One (b I)

data Can : Bin → Set where
  canZero : Can (⟨⟩ O)
  canOne  : ∀ (b : Bin) → One b → Can b

-- Now we can do proofs with these predicates
----------------------------------------------------------------------------------------
one-rev-O : ∀ {b : Bin} → One (b O) → One b
one-rev-O (oneO _ ob) = ob

inc-preserve-one : ∀ (b : Bin) → One b → One (inc b)
inc-preserve-one .(⟨⟩ I) singleI = oneO ((⟨⟩ I)) singleI
inc-preserve-one .(b O) (oneO b ob) = oneI b ob
inc-preserve-one .(b I) (oneI b ob) = oneO (inc b) (inc-preserve-one b ob)

can-inc : ∀ {b : Bin} → Can b → Can (inc b)
can-inc canZero = canOne (⟨⟩ I) singleI
can-inc (canOne (b O) x) = canOne ((b I)) (oneI b (one-rev-O x))
can-inc (canOne (b I) x) = canOne ((inc b) O) (inc-preserve-one (b I) x)
----------------------------------------------------------------------------------------
can-to : ∀ (n : ℕ) → Can (to n)
can-to zero = canZero
can-to (suc n) = can-inc (can-to n)
----------------------------------------------------------------------------------------
atleastOne : ∀ (b : Bin) → One b → 1 ≤ from b
atleastOne .(⟨⟩ I) singleI = s≤s z≤n
atleastOne .(b O) (oneO b ob) rewrite +-comm (from b) zero = ≤-trans (atleastOne b ob) (+-monoˡ-≤ 0 ((from b)) ( (from b)) z≤n)
atleastOne .(b I) (oneI b ob) = s≤s z≤n

lshiftnat : ∀ (n : ℕ) → to (2 * (suc n)) ≡ (to (suc n)) O
lshiftnat zero = refl
lshiftnat (suc n) = 
  begin
    to (2 * suc (suc n))
  ≡⟨ cong to (*-comm 2 (suc(suc n)))⟩
    to (suc (suc n) * 2)
  ≡⟨⟩
    to (2 + (suc n * 2))
  ≡⟨⟩
    inc (inc (to (suc n * 2)))
  ≡⟨ cong inc (cong inc (cong to (*-comm (suc n) 2))) ⟩
    inc (inc (to (2 * suc n)))
  ≡⟨ cong inc (cong inc (lshiftnat n)) ⟩
    inc (inc ((to (suc n)) O))
  ≡⟨⟩
    refl


lshift : ∀ (n : ℕ) → 1 ≤ n → to (2 * n) ≡ (to n) O
lshift (suc n) (s≤s 1≤n) = lshiftnat n

can-to-id-one : ∀ (b : Bin) → One b → to (from b) ≡ b
can-to-id-one .(⟨⟩ I) singleI = refl
can-to-id-one .(b O) (oneO b ob) =
  begin
    to (from (b O))
  ≡⟨⟩
    to (2 * from b)
  ≡⟨ lshift (from b) (atleastOne b ob) ⟩
    (to (from b)) O
  ≡⟨ cong (_O) (can-to-id-one b ob) ⟩
    b O
  ∎
  
can-to-id-one .(b I) (oneI b ob) =
  begin
    to (from (b I))
  ≡⟨⟩
    to (1 + 2 * from b)
  ≡⟨⟩
    inc (to (2 * from b))
  ≡⟨ cong inc (lshift (from b) (atleastOne b ob)) ⟩
    inc ( (to (from b)) O)
  ≡⟨⟩
    to (from b) I
  ≡⟨ cong (_I) (can-to-id-one b ob) ⟩
    b I
  ∎

can-to-id : ∀ (b : Bin) → Can b →  to (from b) ≡ b
can-to-id .(⟨⟩ O) canZero = refl
can-to-id b (canOne .b x) = can-to-id-one b x


