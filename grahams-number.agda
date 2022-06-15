
module grahams-number where

open import Data.Nat
import Data.Nat.Properties
import Data.Nat.DivMod
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

-- We don't want g to compute, so define it abstract.
abstract
  g : ℕ → ℕ
  g zero = 4
  g (suc n) = ↑[ g n ] 3 3

-- Graham's number
G : ℕ
G = g 64

module _ where private
  -- This would not succeed if g was not abstract.
  _ : G ≡ g 64
  _ = refl

-- Version of g that computes for exactly one step.
-- We use this to package the computation rules for g in one equation.
g-1 : ℕ → ℕ
g-1 zero = 4
g-1 (suc n) = ↑[ g n ] 3 3

-- Reenter the abstract block to prove the computation rule of g.
abstract
  g-computation-rule : (n : ℕ) → g n ≡ g-1 n
  g-computation-rule zero = refl
  g-computation-rule (suc n) = refl


-- Proof that G % 10 ≡ 7.

_↑_ _↑↑_ : ℕ → ℕ → ℕ
_↑_ = ↑[ 1 ]
_↑↑_ = ↑[ 2 ]

module three-levels where
  open ≡-Reasoning
  open Data.Nat.Properties
  open Data.Nat.DivMod

  level-1 : (n : ℕ) → 3 ↑ n % 2 ≡ 1
  level-1 zero = refl
  level-1 (suc n) = begin
    3 * (3 ↑ n)        % 2  ≡⟨ %-distribˡ-* 3 (3 ↑ n) 2 ⟩
    1 * ((3 ↑ n) % 2)  % 2  ≡⟨ cong (_% 2) (*-identityˡ ((3 ↑ n) % 2)) ⟩
    (3 ↑ n) % 2        % 2  ≡⟨ m%n%n≡m%n (3 ↑ n) 2 ⟩
    3 ↑ n   % 2             ≡⟨ level-1 n ⟩
    1                       ∎

  level-2 : (n : ℕ) → n % 2 ≡ 1 → 3 ↑ n % 4 ≡ 3
  level-2 (suc zero) p = refl
  level-2 (suc (suc n)) p = begin
    3 * (3 * (3 ↑ n))  % 4  ≡˘⟨ cong (_% 4) (*-assoc 3 3 (3 ↑ n)) ⟩
    9 * (3 ↑ n)        % 4  ≡⟨ %-distribˡ-* 9 (3 ↑ n) 4 ⟩
    1 * ((3 ↑ n) % 4)  % 4  ≡⟨ cong (_% 4) (*-identityˡ ((3 ↑ n) % 4)) ⟩
    ((3 ↑ n) % 4)      % 4  ≡⟨ m%n%n≡m%n (3 ↑ n) 4 ⟩
    (3 ↑ n) % 4             ≡⟨ level-2 n p ⟩
    3                       ∎

  level-3 : (n : ℕ) → n % 4 ≡ 3 → 3 ↑ n % 10 ≡ 7
  level-3 (suc (suc (suc zero))) p = refl
  level-3 (suc (suc (suc (suc n)))) p = begin
    3  * (3 ↑ (3 + n))  % 10  ≡˘⟨ cong (_% 10) (*-assoc 3 3 (3 ↑ (2 + n))) ⟩
    9  * (3 ↑ (2 + n))  % 10  ≡˘⟨ cong (_% 10) (*-assoc 9 3 (3 ↑ (1 + n))) ⟩
    27 * (3 ↑ (1 + n))  % 10  ≡˘⟨ cong (_% 10) (*-assoc 27 3 (3 ↑ n)) ⟩
    81 * (3 ↑ n)        % 10  ≡⟨ %-distribˡ-* 81 (3 ↑ n) 10 ⟩
    1 * ((3 ↑ n) % 10)  % 10  ≡⟨ cong (_% 10) (*-identityˡ ((3 ↑ n) % 10)) ⟩
    ((3 ↑ n) % 10)      % 10  ≡⟨ m%n%n≡m%n (3 ↑ n) 10 ⟩
    (3 ↑ n) % 10              ≡⟨ level-3 n p ⟩
    7                         ∎

  %10≡7 : (n : ℕ) → 3 ↑ (3 ↑ (3 ↑ n)) % 10 ≡ 7
  %10≡7 n = level-3 (3 ↑ (3 ↑ n)) (level-2 (3 ↑ n) (level-1 n))

has-three-levels : ℕ → Set
has-three-levels N = Σ[ N' ∈ ℕ ] ((3 ↑ (3 ↑ (3 ↑ N'))) ≡ N)

%10≡7-from-has-three-levels : (n : ℕ) → has-three-levels n → n % 10 ≡ 7
%10≡7-from-has-three-levels n n-has-three-levels =
  subst P 3↑3↑3↑n'≡n (three-levels.%10≡7 n')
  where
    P : ℕ → Set
    P n = n % 10 ≡ 7

    n' = proj₁ n-has-three-levels
    3↑3↑3↑n'≡n = proj₂ n-has-three-levels


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

  g≥3 : (n : ℕ) → g n ≥ 3
  g≥3 zero = ≤-trans (s≤s (s≤s (s≤s z≤n))) (≤-reflexive (sym (g-computation-rule zero)))
  g≥3 (suc n) = subst (_≥ 3) (sym (g-computation-rule (suc n))) (↑[]≥3 (g n) 3 (s≤s z≤n))

three-levels-finder-2 : (m n : ℕ) → m ≥ 2 → n ≥ 3 → has-three-levels (↑[ m ] 3 n)
three-levels-finder-2 .2 n (s≤s (s≤s {n = zero} (z≤n {n = .zero}))) q =
  three-levels-finder-1 n q
three-levels-finder-2 .(suc (suc (suc m))) .(suc _) (s≤s (s≤s {n = suc m} z≤n)) (s≤s {n = n} q) =
  three-levels-finder-2 (2 + m) (↑[ 3 + m ] 3 n) (s≤s (s≤s z≤n)) (estimates.↑[]≥3 (3 + m) n (≤-trans (s≤s z≤n) q))
  where open Data.Nat.Properties

G-has-three-levels : has-three-levels (g 64)
G-has-three-levels =
  subst has-three-levels (sym (g-computation-rule 64))
    (three-levels-finder-2 (g 63) 3 (g≥2 63) ≤-refl)
  where
    open Data.Nat.Properties
    g≥2 : (n : ℕ) → g n ≥ 2
    g≥2 n = ≤-trans (s≤s (s≤s z≤n)) (estimates.g≥3 n)

G%10≡7 : G % 10 ≡ 7
G%10≡7 = %10≡7-from-has-three-levels G G-has-three-levels
