
module grahams-number where

open import Data.Nat
open import Relation.Binary.PropositionalEquality


-- Definition of Graham's number, following Wikipedia:
-- https://en.wikipedia.org/wiki/Graham%27s_number

module _ where private
  _↑_ : ℕ → ℕ → ℕ
  _↑_ = _^_

  _↑↑_ : ℕ → ℕ → ℕ
  a ↑↑ zero = 1
  a ↑↑ suc b = a ↑ (a ↑↑ b)

  -- test
  _ : 2 ↑↑ 4 ≡ 65536
  _ = refl

-- Iterate a binary operation (with neutral element 1).
-- (Note: more elegant might be (List ℕ → ℕ) → (List ℕ → ℕ).)
iterate : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
iterate f a zero = 1
iterate f a (suc b) = f a (iterate f a b)

↑[_] : ℕ → ℕ → ℕ → ℕ
↑[ zero ] = _*_
↑[ suc k ] = iterate ↑[ k ]

-- test
_ : ↑[ 2 ] 2 4 ≡ 65536
_ = refl

g : ℕ → ℕ
g zero = 4
g (suc n) = ↑[ g n ] 3 3

grahams-number : ℕ
grahams-number = g 64

G = grahams-number

identity : {ℓ : _} → {A : Set ℓ} → A → A
identity a = a


-- Do the following things typecheck (fast)?

-- fast
_ : G ≡ G
_ = refl

-- hangs
-- _ : identity G ≡ G
-- _ = refl

-- hangs
-- _ : 0 + G ≡ G
-- _ = refl

-- hangs
-- _ : G + 0 ≡ G
-- _ = refl

-- fast
_ : Set
_ = G % 10 ≡ 7

-- hangs
-- _ : G % 10 ≡ 7
-- _ = refl

-- hangs
-- _ : G % 10 ≡ 0
-- _ = refl


-- Proof attempt that G % 10 ≡ 7.

_↑_ : ℕ → ℕ → ℕ
_↑_ = ↑[ 1 ]

level-1 : (n : ℕ) → 3 ↑ n % 2 ≡ 1
level-1 = {!!}

level-2 : (n : ℕ) → n % 2 ≡ 1 → 3 ↑ n % 4 ≡ 3
level-2 = {!!}

level-3 : (n : ℕ) → n % 4 ≡ 3 → 3 ↑ n % 10 ≡ 7
level-3 = {!!}

three-levels : (n : ℕ) → 3 ↑ (3 ↑ (3 ↑ n)) % 10 ≡ 7
three-levels n = level-3 (3 ↑ (3 ↑ n)) (level-2 (3 ↑ n) (level-1 n))

G' : ℕ
G' = {!!}

G-vs-G' : G ≡ 3 ↑ (3 ↑ (3 ↑ G'))
G-vs-G' = {!!}

G%10≡7 : G % 10 ≡ 7
G%10≡7 = subst P (sym G-vs-G') (three-levels G')
  where
    P : ℕ → Set
    P n = n % 10 ≡ 7
