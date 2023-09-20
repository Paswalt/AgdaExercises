-------------------------------Preface-----------------------------------------
-- This is equivalent to haskells recursive: data natural = zero | suc natural
-- Saying ℕ is a Set is saying that it is a type that we define
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- This allows us to write natural numbers in a more known way as seen below
{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = 7
------------------------------------Imports------------------------------------
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
-------------------------------------------------------------------------------

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ (suc n) = m * (m ^ n)

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

-- Types <-> Propositions!!!
-- Terms <-> Evidenve/Proofs!!!

-- This is how we write chains of equations, later defined in the equality chapter
_ : 1 + 1 ≡ 2
_ = begin
    1 + 1
  ≡⟨⟩
    suc (0 + 1)
  ≡⟨⟩
    suc 1
  ≡⟨⟩
    2
  ∎

-- Here's another one with multiplication, _ is a dummy name and we can omit signatures when agda can infere it
_ = begin
    2 * 2
  ≡⟨⟩
    2 + (1 * 2)
  ≡⟨⟩
    2 + (2 + (0 * 2))
  ≡⟨⟩
    2 + (2 + 0)
  ≡⟨⟩
    2 + 2
  ≡⟨⟩
    4
  ∎

-- We can define precedence on operators
infixl 6  _+_  _∸_
infixl 7  _*_
infix  8  _^_

-- These pragmas allow us to compute more efficiently with the help of haskells integer representation
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

------------------------------------------Stretch exercise--------------------------------------------
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- Again in haskell this would be similar to
-- data Bin = ⟨⟩ | O Bin | I Bin
-- (Other way around, I dunno how to do postfix in haskell but the idea is clear)

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ I I I) ≡ ⟨⟩ I O O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 0 + 2 * (from x)
from (x I) = 1 + 2 * (from x)

_ : to 5 ≡ ⟨⟩ I O I
_ = refl

_ : from (⟨⟩ O O O I I O I) ≡ 13
_ = refl
