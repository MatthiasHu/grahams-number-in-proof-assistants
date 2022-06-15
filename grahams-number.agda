
module grahams-number where

open import Data.Nat
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product
import Function.Base


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

module _ where private
  abstract
    g' : ℕ → ℕ
    g' zero = 4
    g' (suc n) = ↑[ g' n ] 3 3

    g'-computation-rule-zero : g' zero ≡ 4
    g'-computation-rule-zero = refl

    g'-computation-rule-suc : (n : ℕ) → g' (suc n) ≡ ↑[ g' n ] 3 3
    g'-computation-rule-suc n = refl

  g'≡g : (n : ℕ) → g' n ≡ g n
  g'≡g zero = g'-computation-rule-zero
  g'≡g (suc n) =
    trans
      (g'-computation-rule-suc n)
      (cong (λ k → ↑[ k ] 3 3) (g'≡g n))

  -- Yay!
  g'-computation-rule-64 : g' 64 ≡ ↑[ g' 63 ] 3 3
  g'-computation-rule-64 = g'-computation-rule-suc 63

-- Graham's number
G : ℕ
G = g 64

module _ where private
  g64%10≡7 : g 64 % 10 ≡ 7
  g64%10≡7 = {!!}

  -- This hangs!
  -- G%10≡7 : G % 10 ≡ 7
  -- G%10≡7 = g64%10≡7

module _ where private
  -- This hangs!
  -- G≡g64 : G ≡ g 64
  -- G≡g64 = refl

  -- hangs
  -- g64≡↑[g63]33 : g 64 ≡ ↑[ g 63 ] 3 3
  -- g64≡↑[g63]33 = refl

  -- fast
  gsucn≡↑[gn]33 : (n : ℕ) → g (suc n) ≡ ↑[ g n ] 3 3
  gsucn≡↑[gn]33 n = refl

  -- hangs with type signature, fast without
  -- g64≡↑[g63]33' : g 64 ≡ ↑[ g 63 ] 3 3
  g64≡↑[g63]33' = gsucn≡↑[gn]33 63

  -- fast
  g64≡↑[g63]33'' : Function.Base.typeOf (gsucn≡↑[gn]33 63)
  g64≡↑[g63]33'' = gsucn≡↑[gn]33 63

  -- fast
  g64≡↑[g63]33''' : (λ n → g (suc n) ≡ ↑[ g n ] 3 3) 63
  g64≡↑[g63]33''' = gsucn≡↑[gn]33 63

identity : {ℓ : _} → {A : Set ℓ} → A → A
identity a = a


-- Do the following things typecheck (fast)?
module _ where private
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

_↑_ _↑↑_ : ℕ → ℕ → ℕ
_↑_ = ↑[ 1 ]
_↑↑_ = ↑[ 2 ]

level-1 : (n : ℕ) → 3 ↑ n % 2 ≡ 1
level-1 = {!!}

level-2 : (n : ℕ) → n % 2 ≡ 1 → 3 ↑ n % 4 ≡ 3
level-2 = {!!}

level-3 : (n : ℕ) → n % 4 ≡ 3 → 3 ↑ n % 10 ≡ 7
level-3 = {!!}

three-levels : (n : ℕ) → 3 ↑ (3 ↑ (3 ↑ n)) % 10 ≡ 7
three-levels n = level-3 (3 ↑ (3 ↑ n)) (level-2 (3 ↑ n) (level-1 n))

has-three-levels : ℕ → Set
has-three-levels N = Σ[ N' ∈ ℕ ] ((3 ↑ (3 ↑ (3 ↑ N'))) ≡ N)

three-levels-finder-1 : (n : ℕ) → n ≥ 3 → has-three-levels (↑[ 2 ] 3 n)
three-levels-finder-1 .(suc (suc (suc _))) (s≤s (s≤s (s≤s (z≤n {n = n})))) =  3 ↑↑ n , refl

module estimates where
  open Data.Nat.Properties

  ↑≥1 : (n : ℕ) → 3 ↑ n ≥ 1
  ↑≥1 zero = s≤s z≤n
  ↑≥1 (suc n) = ≤-trans (s≤s z≤n) (*-monoʳ-≤ 3 (↑≥1 n))

  ↑[]≥1 : (m n : ℕ) → m ≥ 1 → (↑[ m ] 3 n) ≥ 1
  ↑[]≥1 .(suc _) zero (s≤s p) = s≤s z≤n
  ↑[]≥1 .1 (suc n) (s≤s {n = zero} (z≤n {n = .zero})) = ≤-trans (↑≥1 n) (m≤m+n (3 ↑ n) _)
  ↑[]≥1 .(suc (suc m)) (suc n) (s≤s {n = suc m} (z≤n {n = .(suc m)})) = ↑[]≥1 (1 + m) (↑[ 2 + m ] 3 n) (s≤s z≤n)

  ↑[]≥3 : (m n : ℕ) → n ≥ 1 → (↑[ m ] 3 n) ≥ 3
  ↑[]≥3 zero n p = *-monoʳ-≤  3 p
  ↑[]≥3 (suc m) .(suc _) (s≤s (z≤n {n = n})) = ↑[]≥3 m _ ( (↑[]≥1 (1 + m) n (s≤s z≤n)) )

three-levels-finder-2 : (m n : ℕ) → m ≥ 2 → n ≥ 3 → has-three-levels (↑[ m ] 3 n)
three-levels-finder-2 .2 n (s≤s (s≤s {n = zero} (z≤n {n = .zero}))) q =
  three-levels-finder-1 n q
three-levels-finder-2 .(suc (suc (suc m))) .(suc _) (s≤s (s≤s {n = suc m} z≤n)) (s≤s {n = n} q) = three-levels-finder-2 (2 + m) (↑[ 3 + m ] 3 n) (s≤s (s≤s z≤n)) (estimates.↑[]≥3 (3 + m) n (≤-trans (s≤s z≤n) q))
  where open Data.Nat.Properties

G-has-three-levels : has-three-levels (g 64)
G-has-three-levels = {!three-levels-finder-2 (g 63) !}  -- Problem. Can't even do C-c C-d or C-c C-.

G%10≡7 : g 64 % 10 ≡ 7
G%10≡7 = subst P G'-vs-G (three-levels G')
  where
    P : ℕ → Set
    P n = n % 10 ≡ 7

    G' = proj₁ G-has-three-levels
    G'-vs-G = proj₂ G-has-three-levels
