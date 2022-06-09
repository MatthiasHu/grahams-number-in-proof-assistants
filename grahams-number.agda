
open import Data.Nat
open import Relation.Binary.PropositionalEquality


-- Definition of Graham's number, following Wikipedia:
-- https://en.wikipedia.org/wiki/Graham%27s_number

iterate : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
iterate f a zero = 1
iterate f a (suc b) = f a (iterate f a b)

_↑_ : ℕ → ℕ → ℕ
_↑_ = _^_

_↑↑_ : ℕ → ℕ → ℕ
a ↑↑ zero = 1
a ↑↑ suc b = a ↑ (a ↑↑ b)

-- test
_ : 2 ↑↑ 4 ≡ 65536
_ = refl

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
