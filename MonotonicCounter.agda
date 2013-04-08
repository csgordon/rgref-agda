open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality
-- Why on earch isn't ≡ in the prelude?
open import Data.Maybe
open import RGref

module MonotonicCounter where

-- Monotonically increasing counter, in the Agda DSL
  inc : hrel ℕ
  inc n n' h h' = Data.Nat._≤_ n n'

  monoctr = Ref ℕ any inc inc

  -- proof of guarantee satisfaction
  plusone-le : ∀ n -> Data.Nat._≤_ n (n + 1)
  plusone-le zero = z≤n
  plusone-le (suc n) = s≤s (plusone-le n)
  
  inc-pf : ∀ (c : monoctr) h h' -> inc ( ! c ) (( ! c ) + 1 ) h h'
  inc-pf c h h' = plusone-le (! c)

  inc-mono : (c : monoctr) -> ● Unit
  inc-mono c =
    [ c ]:=< (! c) + 1 > ((λ h → inc-pf c h (h [ c ↦ (! c + 1) ])))
