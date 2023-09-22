-----------------------Preface--------------------------
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}
--------------------------------------------------------

-- Equality is (for now) defined as follows
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

_ : 5 ≡ 5
_ = refl
-- Here one parameter and one index comes into play
-- we basically fixate the first x in the type x ≡ x
-- with the parameter and create a whole type family
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
-- parameters if possible because agda can
-- handle them more efficiently

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

-- The chains of equations used so far are nothing special,
-- they are just a clever use of Agda's type system. We define
-- these operators in terms of equality proofs as seen below
-- inside of the nested module

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = ≡-trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

_ : 1 + 1 ≡ 2
_ =
  begin             -- This just returns the entire proof again and is only syntactic sugar
    1 + 1           -- This is the x for the first _≡⟨⟩_
  ≡⟨⟩
    (suc zero) + 1  -- Everything following from here, including this line, is the proof that x ≡ y
  ≡⟨⟩
    suc (zero + 1)
  ≡⟨⟩
    suc 1
  ≡⟨⟩
    2
  ∎
-- The proof can be seen as begin (1 + 1 ≡⟨⟩ ((suc zero) + 1 ≡⟨⟩ (suc (zero + 1) ≡⟨⟩ (suc 1 ≡⟨⟩ (2 ∎)))))


-- Sometimes to save time and space, and in rare cases to introduce something useful that agda can not prove,
-- we can use a postulate to state a law without a proof, basically as an axiom. The syntax for that is

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)



-------------------------------------------Stretch exercise--------------------------------------------------
-- One can define chains of equations/reasoning on basically any relation that
-- is transitive. In the following this will be done for the ≤ relation
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
    ------------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
      → m ≤ n
      ---------------
      → suc m ≤ suc n

infix 4 _≤_
infixl 6 _+_

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where
  infix  1 begin≤_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎≤

  begin≤_ : {m n : ℕ} → m ≤ n → m ≤ n
  begin≤ m≤n = m≤n

  _≤⟨⟩_ : (m : ℕ) {n : ℕ} → m ≤ n → m ≤ n
  m ≤⟨⟩ m≤n = m≤n

  _≤⟨_⟩_ : (m : ℕ) {n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
  m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

  _∎≤ : ∀ (n : ℕ) → n ≤ n
  n ∎≤ = ≤-refl

open ≤-Reasoning

-- Out of time and redundancy reasons I will only show one of the monotonicity laws
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q

+-monoʳ-≤ zero p q p≤q =
  begin≤
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ∎≤

+-monoʳ-≤ (suc n) p q p≤q =
  begin≤
    (suc n) + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    (suc n) + q
  ∎≤ 


-- Rewriting is already known, so is the fact that one can use several rewrites at once
-- It is interesting to note that this is equivalent to a with clause as seen here

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-} -- Allows us to use rewrite

-- Stating commutativity as postulate to save space and time
postulate
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

-- First with using rewrites
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
  
even-comm m n ev rewrite +-comm m n = ev

-- Now using with clause
even-comm' : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm' m n ev with (m + n) | +-comm m n
... | .(n + m) | refl = ev

-- Matching against the first pattern uses that matched value
-- in both ev and as m+n term. By using an appropriate law
-- like +-comm that also now takes the term m+n as input
-- and matching it against refl we force the first term to
-- be (a so called dot-pattern) the term (n + m), there is
-- no other choice for it. By this we now obtain (n + m)
-- at every position where m+n was used as a term and therefore
-- the proof changes to showing that even (n + m) with evidence
-- ev as even (n + m) instead of ev as even (m + n). Hence, this
-- really is equivalent to using a rewrite!

-- We can also rewrite the goal, like rewrite would do it
even-comm'' : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm'' m n ev with (n + m) | +-comm n m
... | .(m + n) | refl = ev

---------------------------------------------------------------------------------------------------
-- Another notion of equality is the leibniz equality
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

-- This is also an equivalence relation
≐-refl : ∀ {A : Set} {x : A} → x ≐ x
≐-refl P Px  = Px

-- Symmetry is non-trivial and uses a smart construction and the fact
-- that leibniz equality works with -any- predicate. It's a very genius
-- proof!
sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = ≐-refl P
    Qy : Q y
    Qy = x≐y Q Qx


≐-trans : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans {A} {x} {y} {z} x≐y y≐z = λ P x₁ → y≐z P (x≐y P x₁)

-- As a final step one can show that both equalities are actually the same

-- The direction ≡ → ≐ follows from substitution law!
≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
  
≡-implies-≐ x≡y P  = subst P x≡y

-- Next the direction ≐ → ≡ which again works
-- by constructing a smart predicate.
≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y

≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = ≡-refl
    Qy : Q y
    Qy = x≐y Q Qx


--------------------------------------------------------------------
-- Lastly, for the definition of ≐ we had to use Set₁
-- This is because of set theoretical paradoxes. We have
-- a whole hierarchy, namely Set ≡ Set₀ : (Set₁ : (Set₂ : ...)
-- and so on. We can have so called universe polymorphism.
-- This is best explained by looking at the generalized
-- versions of the equality and the leibniz equality:

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

